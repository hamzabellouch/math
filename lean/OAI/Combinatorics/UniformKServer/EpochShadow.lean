import Mathlib
import OAI.Combinatorics.UniformKServer.BoundedFilter
import OAI.Combinatorics.UniformKServer.Fallback
import OAI.Combinatorics.UniformKServer.Epochs

namespace OAI

namespace UniformKServer.EpochShadow

abbrev Selector (n k : ℕ) := List (Fin n) → Configuration n k → Fin n → Fin k

def StronglyLazy {n k : ℕ} (T : Selector n k) : Prop :=
  ∀ (w : List (Fin n)) (c : Configuration n k) (r : Fin n),
    (∃ j, c j = r) → c (T w c r) = r

def shadowTrace {n k : ℕ} (T : Selector n k) :
    List (Fin n) → Configuration n k → List (Fin n) → History n k
  | _, _, [] => []
  | p, c, r :: w => (r,T p c r) :: shadowTrace T (p ++ [r]) (serve c r (T p c r)) w

def bookStep {n k : ℕ} (seen : Finset (Fin n)) (r : Fin n) : Finset (Fin n) :=
  if k < (insert r seen).card then ∅ else insert r seen

/-- Number of portions, including an inherited nonempty raw block. -/
def blockCount {n k : ℕ} : Finset (Fin n) → List (Fin n) → ℕ
  | seen, [] => if seen.Nonempty then 1 else 0
  | seen, r :: w => (if k < (insert r seen).card then 1 else 0) +
      blockCount (k:=k) (bookStep (k:=k) seen r) w

def keptTail {n k : ℕ} (M : ℕ) : FilterState n k → List (Fin n) → List (Fin n)
  | _, [] => []
  | f, r :: w => if ∀ e ∈ f.live, Covers e r then keptTail M f w
    else r :: keptTail M (UniformKServer.step M f r) w

def nextEntry {n k : ℕ} (e : Entry n k) (r : Fin n) (j : Fin k) : Entry n k :=
  ⟨serve e.position r j, e.moves + if e.position j = r then 0 else 1⟩

/-- The literal one-epoch virtual routine. The deterministic filter continues
independently through fallback; its discarded final state has no effect on
service. Its full kept word is provided separately by `keptTail`. -/
def trace {n k : ℕ} (hk : 0 < k) (M : ℕ) (T : Selector n k) :
    FilterState n k → Entry n k → Finset (Fin n) → List (Fin n) → History n k
  | _, _, _, [] => []
  | f, e, seen, r :: w =>
      let seen' := bookStep (k:=k) seen r
      if ∀ z ∈ f.live, Covers z r then
        let j := Fallback.pick hk (Fallback.coverers e.position r)
        (r,j) :: trace hk M T f e seen' w
      else
        let j := T f.kept e.position r
        let e' := nextEntry e r j
        (r,j) :: if e'.moves ≤ M then
          trace hk M T (UniformKServer.step M f r) e' seen' w
        else Fallback.rawTrace hk ⟨⟨e'.position,∅⟩,seen',0⟩ w

                                                                       

theorem raw_count {n k : ℕ} (hk : 0 < k) (s : Fallback.RawState n k)
    (w : List (Fin n)) :
    Fallback.portions (Fallback.rawRun hk s w) = s.completed + blockCount (k:=k) s.seen w := by
  induction w generalizing s with
  | nil => rfl
  | cons r w ih =>
    rw [Fallback.rawRun, ih]
    by_cases he : k < (insert r s.seen).card <;>
      simp [Fallback.rawStep, Fallback.isEndpoint, he, blockCount, bookStep, Nat.add_assoc]

theorem book_card {n k : ℕ} (seen : Finset (Fin n)) (r : Fin n) :
    (bookStep (k:=k) seen r).card ≤ k := by
  unfold bookStep
  split_ifs with h
  · simp
  · exact le_of_not_gt h

theorem block_tail_le {n k : ℕ} (seen : Finset (Fin n)) (r : Fin n) (w : List (Fin n)) :
    blockCount (k:=k) (bookStep (k:=k) seen r) w ≤ blockCount (k:=k) seen (r::w) := by
  simp only [blockCount]
  omega

theorem kept_tail_snoc {n k : ℕ} (M : ℕ) (f : FilterState n k) (w : List (Fin n)) :
    (w.foldl (UniformKServer.step M) f).kept = f.kept ++ keptTail M f w := by
  induction w generalizing f with
  | nil => simp [keptTail]
  | cons r w ih =>
    rw [List.foldl_cons, ih]
    by_cases h : ∀ e ∈ f.live, Covers e r
    · simp only [keptTail, UniformKServer.step, ite_eq_left h]
    · simp only [keptTail, UniformKServer.step, ite_eq_right h, List.append_assoc, List.singleton_append]

theorem kept_tail_full {n k : ℕ} (M : ℕ) (u : Configuration n k) (raw : List (Fin n)) :
    keptTail M (initial u) raw = (runFilter M u raw).kept := by
  simpa [runFilter, initial] using (kept_tail_snoc M (initial u) raw).symm

theorem next_lazy {n k : ℕ} (T : Selector n k) (hT : StronglyLazy T)
    (p : List (Fin n)) (e : Entry n k) (r : Fin n) :
    LazyStep e r (nextEntry e r (T p e.position r)) := by
  unfold LazyStep
  split_ifs with h
  · have hj := hT p e.position r h
    have hc : serve e.position r (T p e.position r) = e.position := by
      unfold serve
      conv_lhs => arg 3; rw [← hj]
      exact Function.update_eq_self _ _
    cases e
    simp_all [nextEntry]
  · have hj : e.position (T p e.position r) ≠ r := fun hh => h ⟨_,hh⟩
    exact ⟨T p e.position r, by simp [nextEntry, hj, serve]⟩

theorem next_cost {n k : ℕ} (d : RationalMetric n) (δ : ℝ)
    (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (e : Entry n k) (r : Fin n) (j : Fin k) (paid : ℝ)
    (hp : e.moves * δ ≤ paid) :
    (nextEntry e r j).moves * δ ≤ paid + (d.distance (e.position j) r : ℝ) := by
  by_cases h : e.position j = r
  · simp only [nextEntry, ite_eq_left h, Nat.add_zero]
    exact hp.trans (le_add_of_nonneg_right (by exact_mod_cast d.nonneg _ _))
  · simp only [nextEntry, ite_eq_right h, Nat.cast_add, Nat.cast_one]
    nlinarith [hsep _ _ h]

theorem fallback_bound {n k : ℕ} (hk : 0 < k) (d : RationalMetric n)
    (D : ℝ) (hD : 0 ≤ D) (hdiam : ∀ x y, (d.distance x y : ℝ) ≤ D)
    (c : Configuration n k) (hc : Function.Injective c)
    (seen : Finset (Fin n)) (hs : seen.card ≤ k)
    (w : List (Fin n)) (R : ℕ) (hR : blockCount (k:=k) seen w ≤ R) :
    (Fallback.rawTrace hk ⟨⟨c,∅⟩,seen,0⟩ w).map Prod.fst = w ∧
    costAlong d c (Fallback.rawTrace hk ⟨⟨c,∅⟩,seen,0⟩ w) ≤ R * (k+1) * D := by
  have hR' : Fallback.portions (Fallback.rawRun hk ⟨⟨c,∅⟩,seen,0⟩ w) ≤ R := by
    simpa [raw_count] using hR
  exact (Fallback.raw_fallback_bound hk d D hD hdiam c hc seen hs w R hR').2


/-- Paying for fallback by an already accumulated *unconditioned* shadow
prefix; the comparison never conditions on the event of reaching the cap. -/
theorem trace_ledger {n k : ℕ} (hk : 0 < k) (d : RationalMetric n)
    (T : Selector n k) (hT : StronglyLazy T) (u : Configuration n k)
    (hu : Function.Injective u) (M R : ℕ) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (hdiam : ∀ x y, (d.distance x y : ℝ) ≤ D)
    (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (hcap : R * (k+1) * D ≤ (M+1) * δ)
    (raw : List (Fin n)) (f : FilterState n k) (e : Entry n k)
    (seen : Finset (Fin n)) (paid : ℝ)
    (hf : Represents M u f) (hp : LazyPath u f.kept e) (hm : e.moves ≤ M)
    (hs : seen.card ≤ k) (hR : blockCount (k:=k) seen raw ≤ R)
    (hpaid : e.moves * δ ≤ paid) :
    (trace hk M T f e seen raw).map Prod.fst = raw ∧
    costAlong d e.position (trace hk M T f e seen raw) ≤
      paid + 2 * costAlong d e.position (shadowTrace T f.kept e.position (keptTail M f raw)) := by
  induction raw generalizing f e seen paid with
  | nil =>
    have hn : 0 ≤ paid := (mul_nonneg (Nat.cast_nonneg _) hδ).trans hpaid
    simpa only [trace, List.map_nil, keptTail, shadowTrace, costAlong, mul_zero, add_zero,
      true_and] using hn
  | cons r w ih =>
    have hs' := book_card (k:=k) seen r
    have hR' := (block_tail_le (k:=k) seen r w).trans hR
    by_cases hdrop : ∀ z ∈ f.live, Covers z r
    · have hc := hdrop e ((hf e).mpr ⟨hp,hm⟩)
      let j := Fallback.pick hk (Fallback.coverers e.position r)
      have hj : e.position j = r := by
        apply (Fallback.mem_coverers _ _ _).mp
        apply Fallback.pick_mem
        rcases hc with ⟨l,hl⟩
        exact ⟨l,(Fallback.mem_coverers _ _ _).mpr hl⟩
      have heq : serve e.position r j = e.position := by
        unfold serve
        conv_lhs => arg 3; rw [← hj]
        exact Function.update_eq_self _ _
      have hz : (d.distance (e.position j) r : ℝ) = 0 := by
        rw [hj, (d.eq_zero r r).mpr rfl, Rat.cast_zero]
      have hi := ih f e (bookStep (k:=k) seen r) paid hf hp hm hs' hR' hpaid
      dsimp only [j] at heq hz
      simpa only [trace, ite_eq_left hdrop, keptTail, List.map_cons, costAlong,
        heq, hz, zero_add, List.cons.injEq, true_and] using hi
    · let j := T f.kept e.position r
      let e' := nextEntry e r j
      let f' := UniformKServer.step M f r
      let q : ℝ := (d.distance (e.position j) r : ℝ)
      have hq : 0 ≤ q := by
        dsimp [q]
        exact_mod_cast d.nonneg (e.position j) r
      have hnew : e'.moves * δ ≤ paid+q := next_cost d δ hsep e r j paid hpaid
      have hls : LazyStep e r e' := next_lazy T hT f.kept e r
      have hfp : f'.kept = f.kept ++ [r] := by
        simp only [f', UniformKServer.step, ite_eq_right hdrop]
      have hpath : LazyPath u f'.kept e' := hfp ▸ LazyPath.snoc hp hls
      have hf' : Represents M u f' := step_represents M u f r hf
      by_cases hcont : e'.moves ≤ M
      · dsimp only [e', j] at hcont
        have hi := ih f' e' (bookStep (k:=k) seen r) (paid+q)
          hf' hpath hcont hs' hR' hnew
        constructor
        · simpa only [trace, ite_eq_right hdrop, ite_eq_left hcont, List.map_cons,
            List.cons.injEq, true_and] using hi.1
        · simp only [trace, ite_eq_right hdrop, ite_eq_left hcont, keptTail, shadowTrace,
            costAlong]
          change q + costAlong d e'.position (trace hk M T f' e' (bookStep seen r) w) ≤
            paid+2*(q + costAlong d e'.position
              (shadowTrace T (f.kept++[r]) e'.position (keptTail M f' w)))
          rw [hfp] at hi
          linarith [hi.2]
      · dsimp only [e', j] at hcont
        have hc : (M+1 : ℝ)*δ ≤ paid+q := by
          have hm' : M+1 ≤ e'.moves := Nat.succ_le_of_lt (lt_of_not_ge hcont)
          have hm'' : (M+1 : ℝ) ≤ e'.moves := by exact_mod_cast hm'
          exact (mul_le_mul_of_nonneg_right hm'' hδ).trans hnew
        have hb := fallback_bound hk d D hD hdiam e'.position
          (lazyPath_injective hu hpath) (bookStep (k:=k) seen r) hs' w R hR'
        constructor
        · simpa only [trace, ite_eq_right hdrop, ite_eq_right hcont, List.map_cons,
            List.cons.injEq, true_and] using hb.1
        · simp only [trace, ite_eq_right hdrop, ite_eq_right hcont, keptTail, shadowTrace,
            costAlong]
          change q + costAlong d e'.position
            (Fallback.rawTrace hk ⟨⟨e'.position,∅⟩,bookStep seen r,0⟩ w) ≤
            paid + 2*(q + costAlong d e'.position
              (shadowTrace T (f.kept++[r]) e'.position (keptTail M f' w)))
          have hn := costAlong_nonneg d e'.position
            (shadowTrace T (f.kept++[r]) e'.position (keptTail M f' w))
          linarith [hb.2]

theorem epoch_virtual_bound {n k : ℕ} (hk : 0 < k) (d : RationalMetric n)
    (T : Selector n k) (hT : StronglyLazy T) (u : Configuration n k)
    (hu : Function.Injective u) (M R : ℕ) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (hdiam : ∀ x y, (d.distance x y : ℝ) ≤ D)
    (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (hcap : R * (k+1) * D ≤ (M+1) * δ)
    (raw : List (Fin n)) (hR : blockCount (k:=k) ∅ raw ≤ R) :
    (trace hk M T (initial u) ⟨u,0⟩ ∅ raw).map Prod.fst = raw ∧
    costAlong d u (trace hk M T (initial u) ⟨u,0⟩ ∅ raw) ≤
      2 * costAlong d u (shadowTrace T [] u (keptTail M (initial u) raw)) := by
  have h := trace_ledger hk d T hT u hu M R D δ hD hδ hdiam hsep hcap raw
    (initial u) ⟨u,0⟩ ∅ 0 (initial_represents M u) LazyPath.nil
    (Nat.zero_le _) (by simp) hR (by simp)
  simpa only [initial, zero_add] using h

theorem epoch_actual_bound {n k : ℕ} (hk : 0 < k) (d : RationalMetric n)
    (T : Selector n k) (hT : StronglyLazy T) (u s : Configuration n k)
    (hu : Function.Injective u) (M R : ℕ) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (hdiam : ∀ x y, (d.distance x y : ℝ) ≤ D)
    (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (hcap : R * (k+1) * D ≤ (M+1) * δ)
    (raw : List (Fin n)) (hR : blockCount (k:=k) ∅ raw ≤ R) :
    costAlong d s (trace hk M T (initial u) ⟨u,0⟩ ∅ raw) ≤
      2 * costAlong d u (shadowTrace T [] u (keptTail M (initial u) raw)) + k*D := by
  have hv := epoch_virtual_bound hk d T hT u hu M R D δ hD hδ hdiam hsep hcap raw hR
  have ht := subsequence_cost_transfer d s u
    (trace hk M T (initial u) ⟨u,0⟩ ∅ raw)
    (trace hk M T (initial u) ⟨u,0⟩ ∅ raw) (List.Sublist.refl _) D hdiam
  linarith [ht.2.1, hv.2]


end UniformKServer.EpochShadow

end OAI
