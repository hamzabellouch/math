import OAI.Analysis.SeparableQuotients.PathConvergence

namespace OAI

noncomputable section

namespace SeparableQuotient.DiscreteDiagonal
open Filter
open scoped Topology Classical

/-- Countably many yes/no tests can be made eventually constant by one
subsequence. The index set is arbitrary countable, not just natural numbers. -/
lemma exists_stabilizing_subsequence {ι : Type*} [Countable ι] (p : ℕ → ι → Prop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, ∃ b : Prop,
      ∀ᶠ n in atTop, p (φ n) i ↔ b := by
  let x : ℕ → ι → Bool := fun n i => decide (p n i)
  obtain ⟨y, _, φ, hφ, hy⟩ := isCompact_univ.tendsto_subseq
    (x := x) (fun _ => Set.mem_univ _)
  refine ⟨φ, hφ, fun i => ⟨y i = true, ?_⟩⟩
  have ht := (tendsto_pi_nhds.mp hy) i
  have he : ∀ᶠ n in atTop, x (φ n) i = y i :=
    (by simpa only [nhds_discrete, tendsto_pure, Function.comp_apply] using ht)
  filter_upwards [he] with n hn
  change decide (p (φ n) i) = y i at hn
  rw [← hn, decide_eq_true_eq]

end SeparableQuotient.DiscreteDiagonal

namespace SeparableQuotient.IncreasingLists
open Filter
open scoped Classical

/-- Pointwise stabilization of membership in increasing finite lists, with an
infinite limiting set, stabilizes every list position. -/
lemma positions_stabilize (len : ℕ → ℕ) (v : ℕ → ℕ → ℕ)
    (hv : ∀ n, StrictMono (fun i : Fin (len n) => v n i)) (W : Set ℕ)
    (hW : W.Infinite)
    (hmem : ∀ w, ∀ᶠ n in atTop, (∃ i < len n, v n i = w) ↔ w ∈ W) :
    ∀ i, ∀ᶠ n in atTop, i < len n ∧ v n i = Nat.nth (· ∈ W) i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    let w := Nat.nth (· ∈ W) i
    have hwi : w ∈ W := Nat.nth_mem_of_infinite hW i
    have hsmall : ∀ᶠ n in atTop, ∀ u ≤ w,
        (∃ k < len n, v n k = u) ↔ u ∈ W := by
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using
        (eventually_all_finset (I := Finset.range (w+1))).mpr (fun u _ => hmem u)
    have hprev : ∀ᶠ n in atTop, ∀ j < i,
        j < len n ∧ v n j = Nat.nth (· ∈ W) j := by
      simpa only [Finset.mem_range] using
        (eventually_all_finset (I := Finset.range i)).mpr (fun j hj => ih j (Finset.mem_range.mp hj))
    filter_upwards [hsmall, hprev] with n hn hp
    obtain ⟨k, hk, hkw⟩ := (hn w le_rfl).mpr hwi
    have hki : k = i := by
      rcases lt_trichotomy k i with h | h | h
      · have he := (hp k h).2.symm.trans hkw
        exact ((Nat.nth_injective hW he).not_lt h).elim
      · exact h
      · have hi : i < len n := h.trans hk
        have hiv : v n i < w := (hv n (show (⟨i, hi⟩ : Fin (len n)) < ⟨k, hk⟩ from h)).trans_eq hkw
        have hiW : v n i ∈ W := (hn (v n i) hiv.le).mp ⟨i, hi, rfl⟩
        obtain ⟨j, hj⟩ := Nat.subset_range_nth hiW
        have hji : j < i := (Nat.nth_lt_nth hW).mp (hj ▸ hiv)
        have hvi : v n j = v n i := (hp j hji).2.trans hj
        exact ((hv n (show (⟨j, (hp j hji).1⟩ : Fin (len n)) < ⟨i, hi⟩ from hji)).ne hvi).elim
    subst k
    exact ⟨hk, hkw⟩

/-- Bounded windows of arbitrarily high eventual hits force the limiting
membership set to be infinite. The upper window endpoints are essential. -/
lemma infinite_of_windows (len : ℕ → ℕ) (v : ℕ → ℕ → ℕ) (W : Set ℕ)
    (hmem : ∀ w, ∀ᶠ n in atTop, (∃ i < len n, v n i = w) ↔ w ∈ W)
    (hwin : ∀ B, ∃ T, ∀ᶠ n in atTop, ∃ i < len n, B < v n i ∧ v n i ≤ T) :
    W.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨T, hT⟩ := hwin B
  have hsmall : ∀ᶠ n in atTop, ∀ u ≤ T,
      (∃ k < len n, v n k = u) ↔ u ∈ W := by
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using
      (eventually_all_finset (I := Finset.range (T+1))).mpr (fun u _ => hmem u)
  obtain ⟨n, hn, i, hi, hBi, hiT⟩ := (hsmall.and hT).exists
  exact ⟨v n i, (hn (v n i) hiT).mp ⟨i, hi, rfl⟩, hBi⟩

end SeparableQuotient.IncreasingLists

namespace SeparableQuotient.Norming
open PathCoding CoherentClosures Filter
open scoped Classical

lemma PrefixValid.support_subset_closure {P : RawPath} {len : ℕ}
    (h : PrefixValid P len) {n : ℕ} (hn : n < len) :
    P.support n ⊆ P.closure n := by
  intro a ha
  exact (rho_le_iff a (P.endpoint n) (P.le_endpoint ha) _ (h.metadata_pos n hn)).mp
    (h.rho_bound n hn a (P.endpoint n) ha (P.endpoint_mem n) (P.le_endpoint ha))

lemma PrefixValid.piece_support_subset_closure {P : RawPath} {len : ℕ}
    (h : PrefixValid P len) {i n : ℕ} (hi : i ≤ n) (hn : n < len) :
    (P.piece i).support ⊆ P.closure n :=
  (P.piece_support_subset hi).trans (h.support_subset_closure hn)

/-- A retained coordinate in a later piece anchors the compressed code in the
actual ordinal labels. This is the finite-prefix version of path rigidity. -/
lemma PrefixValid.piece_eq_of_code_anchor {P Q : RawPath} {len len' i j n : ℕ}
    (hP : PrefixValid P len) (hQ : PrefixValid Q len')
    (hn : n < len) (hn' : n < len') (hij : i < j) (hjn : j ≤ n)
    (hc : P.code n = Q.code n) (a : Γ)
    (ha : a ∈ (P.piece j).support) (ha' : a ∈ Q.closure n) :
    P.piece i = Q.piece i := by
  have hm := (RawPath.code_eq_at hc n le_rfl).2.1
  have haP := hP.piece_support_subset_closure hjn hn ha
  apply position_alignment (a := a) ?_
    (hP.piece_support_subset_closure (hij.le.trans hjn) hn)
    (hQ.piece_support_subset_closure (hij.le.trans hjn) hn')
    (fun x hx => hP.successive i j hij (hjn.trans_lt hn) x hx a ha)
    (RawPath.code_eq_at hc i (hij.le.trans hjn)).2.2
  unfold RawPath.closure at haP ha' ⊢
  rw [hm] at haP ⊢
  exact shared_initial_segment (P.endpoint n) (Q.endpoint n) a (Q.metadata n) haP ha'

/-- Fixed successor weights and arbitrarily late retained coordinates force
stabilization of the entire *uncropped* data, not just coordinatewise limits. -/
lemma finite_paths_stabilize {f : Family} (P : ℕ → FinitePath f)
    (hlen : ∀ i, ∀ᶠ n in atTop, i < (P n).length)
    (hw : ∀ i, ∃ w, ∀ᶠ n in atTop, (P n).raw.weight i = w)
    (ha : ∀ i, ∃ j > i, ∃ a : Γ,
      ∀ᶠ n in atTop, a ∈ ((P n).raw.piece j).support) :
    ∀ i, ∃ d : Array × ℕ × ℕ, ∀ᶠ n in atTop,
      (P n).raw.piece i = d.1 ∧ (P n).raw.weight i = d.2.1 ∧
        (P n).raw.metadata i = d.2.2 := by
  intro i
  obtain ⟨j, hij, a, ha⟩ := ha i
  obtain ⟨w, hw⟩ := hw (j+1)
  have hg := (hlen (j+1)).and (hw.and ha)
  obtain ⟨n₀, hn₀, hw₀, ha₀⟩ := hg.exists
  refine ⟨⟨(P n₀).raw.piece i, (P n₀).raw.weight i, (P n₀).raw.metadata i⟩, ?_⟩
  filter_upwards [hg] with n hn
  have hc : (P n).raw.code j = (P n₀).raw.code j := by
    apply sigma_injective
    rw [← (P n).valid.rule j hn.1, ← (P n₀).valid.rule j hn₀, hn.2.1, hw₀]
  refine ⟨(P n).valid.piece_eq_of_code_anchor (P n₀).valid
    (by omega) (by omega) hij le_rfl hc a hn.2.2
    ((P n₀).valid.piece_support_subset_closure le_rfl (by omega) ha₀), ?_, ?_⟩
  · exact (RawPath.code_eq_at hc i hij.le).1
  · exact (RawPath.code_eq_at hc i hij.le).2.1

lemma raw_support_eq_of_prefix {P Q : RawPath} {n : ℕ}
    (hp : ∀ i ≤ n, P.piece i = Q.piece i) : P.support n = Q.support n := by
  ext a
  simp only [RawPath.mem_support_iff]
  constructor <;> rintro ⟨i, hi, ha⟩
  · exact ⟨i, hi, (hp i hi) ▸ ha⟩
  · exact ⟨i, hi, (hp i hi).symm ▸ ha⟩

lemma raw_code_eq_of_prefix {P Q : RawPath} {n : ℕ}
    (hp : ∀ i ≤ n, P.piece i = Q.piece i)
    (hw : ∀ i ≤ n, P.weight i = Q.weight i)
    (hm : ∀ i ≤ n, P.metadata i = Q.metadata i) : P.code n = Q.code n := by
  have hs := raw_support_eq_of_prefix hp
  have he : P.endpoint n = Q.endpoint n := by
    unfold RawPath.endpoint
    congr 1
  have hc : P.closure n = Q.closure n := by
    simp only [RawPath.closure, he, hm n le_rfl]
  apply congrArg List.ofFn
  funext i
  simp only [hw i (by omega), hm i (by omega), hp i (by omega), hc]

/-- Assemble the pointwise stabilized raw data into an actual infinite path.
Type-I membership is witnessed by original finite-path pieces, never by an
assumption that a limit belongs to the norming set. -/
lemma infinite_path_of_stabilized {f : Family} (P : ℕ → FinitePath f)
    (hmem : ∀ n i j, ((P n).piece i).child j ∈ f.norming)
    (hlen : ∀ i, ∀ᶠ n in atTop, i < (P n).length)
    (hstable : ∀ i, ∃ d : Array × ℕ × ℕ, ∀ᶠ n in atTop,
      (P n).raw.piece i = d.1 ∧ (P n).raw.weight i = d.2.1 ∧
        (P n).raw.metadata i = d.2.2) :
    ∃ Q : InfinitePath f, ∀ i, ∀ᶠ n in atTop,
      (P n).raw.piece i = Q.raw.piece i ∧
      (P n).raw.weight i = Q.raw.weight i ∧
      (P n).raw.metadata i = Q.raw.metadata i := by
  choose d hd using hstable
  let Q : RawPath := {
    piece := fun i => (d i).1
    weight := fun i => (d i).2.1
    metadata := fun i => (d i).2.2
    nonzero := fun i => by
      obtain ⟨n, hn⟩ := (hd i).exists
      exact hn.1 ▸ (P n).raw.nonzero i }
  have he (i : ℕ) : ∀ᶠ n in atTop,
      (P n).raw.piece i = Q.piece i ∧ (P n).raw.weight i = Q.weight i ∧
        (P n).raw.metadata i = Q.metadata i := hd i
  have heAll (i : ℕ) : ∀ᶠ n in atTop, ∀ j ≤ i,
      (P n).raw.piece j = Q.piece j ∧ (P n).raw.weight j = Q.weight j ∧
        (P n).raw.metadata j = Q.metadata j := by
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using
      (eventually_all_finset (I := Finset.range (i+1))).mpr (fun j _ => he j)
  have hc (i : ℕ) : ∀ᶠ n in atTop, (P n).raw.code i = Q.code i := by
    filter_upwards [heAll i] with n hn
    exact raw_code_eq_of_prefix (fun j hj => (hn j hj).1)
      (fun j hj => (hn j hj).2.1) (fun j hj => (hn j hj).2.2)
  have hvalid : Q.Admissible := {
    successive := by
      intro i j hij a ha b hb
      obtain ⟨n, hn, hi, hj⟩ := ((hlen j).and ((he i).and (he j))).exists
      exact (P n).valid.successive i j hij hn a (hi.1.symm ▸ ha) b (hj.1.symm ▸ hb)
    metadata_strict := by
      intro i j hij
      obtain ⟨n, hn, hi, hj⟩ := ((hlen j).and ((he i).and (he j))).exists
      simpa only [hi.2.2, hj.2.2] using (P n).valid.metadata_strict i j hij hn
    metadata_pos := by
      intro i
      obtain ⟨n, hn, hi⟩ := ((hlen i).and (he i)).exists
      simpa only [hi.2.2] using (P n).valid.metadata_pos i hn
    weight_pos := by
      intro i
      obtain ⟨n, hn, hi⟩ := ((hlen i).and (he i)).exists
      simpa only [hi.2.1] using (P n).valid.weight_pos i hn
    weight_le_metadata := by
      intro i
      obtain ⟨n, hn, hi⟩ := ((hlen i).and (he i)).exists
      simpa only [hi.2.1, hi.2.2] using (P n).valid.weight_le_metadata i hn
    rho_bound := by
      intro i a b ha hb hab
      obtain ⟨n, hn, hi⟩ := ((hlen i).and (heAll i)).exists
      have hs := raw_support_eq_of_prefix (fun j hj => (hi j hj).1)
      simpa only [(hi i le_rfl).2.2] using (P n).valid.rho_bound i hn a b
        (hs.symm ▸ ha) (hs.symm ▸ hb) hab
    rule := by
      intro i
      obtain ⟨n, hn, hi, hci⟩ := ((hlen (i+1)).and ((he (i+1)).and (hc i))).exists
      simpa only [hi.2.1, hci] using (P n).valid.rule i hn }
  have hpiece (i : ℕ) : ∃ e : TypeI f, e.value = Q.piece i ∧ e.weight = Q.weight i ∧
      ∀ j, e.child j ∈ f.norming := by
    obtain ⟨n, hn, hi⟩ := ((hlen i).and (he i)).exists
    exact ⟨(P n).piece ⟨i, hn⟩, ((P n).value_eq _).trans hi.1,
      ((P n).weight_eq _).trans hi.2.1, hmem n _⟩
  choose e heval heweight hemem using hpiece
  refine ⟨⟨Q, hvalid, e, heval, heweight, ?_, hemem⟩, he⟩
  intro i j hij
  obtain ⟨n, hn, hi, hj⟩ := ((hlen j).and ((he i).and (he j))).exists
  simpa only [hi.1, hj.1] using (P n).mixed_successive
    ⟨i, hij.trans hn⟩ ⟨j, hn⟩ hij

lemma infinite_path_of_fixed_chain {f : Family} (P : ℕ → FinitePath f)
    (hmem : ∀ n i j, ((P n).piece i).child j ∈ f.norming)
    (hlen : ∀ i, ∀ᶠ n in atTop, i < (P n).length)
    (hw : ∀ i, ∃ w, ∀ᶠ n in atTop, (P n).raw.weight i = w)
    (ha : ∀ i, ∃ j > i, ∃ a : Γ,
      ∀ᶠ n in atTop, a ∈ ((P n).raw.piece j).support) :
    ∃ Q : InfinitePath f, ∀ i, ∀ᶠ n in atTop,
      (P n).raw.piece i = Q.raw.piece i ∧
      (P n).raw.weight i = Q.raw.weight i ∧
      (P n).raw.metadata i = Q.raw.metadata i :=
  infinite_path_of_stabilized P hmem hlen (finite_paths_stabilize P hlen hw ha)

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open PathCoding Filter
open scoped Classical

lemma PrefixValid.index_le_weight {P : RawPath} {len : ℕ} (h : PrefixValid P len)
    (i : ℕ) (hi : i < len) : i ≤ P.weight i := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    have hv := h.weight_strict (show (⟨i, by omega⟩ : Fin len) < ⟨i+1, hi⟩ from by change i < i+1; omega)
    have := ih (by omega)
    change P.weight i < P.weight (i+1) at hv
    omega

/-- A compactness statement sufficient for the four-hits contradiction. Unlike
weak-star compactness alone, it recovers one actual infinite coded path. Every
high window has a finite upper endpoint and a finite possible coordinate set. -/
lemma path_of_recurrent_windows {f : Family} (P : ℕ → FinitePath f)
    (hmem : ∀ n i j, ((P n).piece i).child j ∈ f.norming)
    (hwin : ∀ B : ℕ, ∃ T : ℕ, ∃ s : Finset Γ, ∀ᶠ n in atTop,
      ∃ i < (P n).length, B < (P n).raw.weight i ∧ (P n).raw.weight i ≤ T ∧
        ∃ a ∈ s, a ∈ ((P n).raw.piece i).support) :
    ∃ (φ : ℕ → ℕ) (Q : InfinitePath f), StrictMono φ ∧ ∀ i, ∀ᶠ n in atTop,
      i < (P (φ n)).length ∧ (P (φ n)).raw.piece i = Q.raw.piece i ∧
      (P (φ n)).raw.weight i = Q.raw.weight i ∧
      (P (φ n)).raw.metadata i = Q.raw.metadata i := by
  choose T s hs using hwin
  let ι := ℕ ⊕ (Σ B : ℕ, ℕ × s B)
  let test : ℕ → ι → Prop := fun n t => match t with
    | .inl w => ∃ i < (P n).length, (P n).raw.weight i = w
    | .inr ⟨B, i, a⟩ => a.val ∈ ((P n).raw.piece i).support
  obtain ⟨φ, hφ, htest⟩ := DiscreteDiagonal.exists_stabilizing_subsequence test
  choose b hb using htest
  let W : Set ℕ := {w | b (.inl w)}
  have hWmem (w : ℕ) : ∀ᶠ n in atTop,
      (∃ i < (P (φ n)).length, (P (φ n)).raw.weight i = w) ↔ w ∈ W := hb (.inl w)
  have hwin' (B : ℕ) : ∀ᶠ n in atTop,
      ∃ i < (P (φ n)).length, B < (P (φ n)).raw.weight i ∧
        (P (φ n)).raw.weight i ≤ T B ∧ ∃ a ∈ s B,
          a ∈ ((P (φ n)).raw.piece i).support := (hs B).filter_mono hφ.tendsto_atTop
  have hW : W.Infinite := IncreasingLists.infinite_of_windows
    (fun n => (P (φ n)).length) (fun n i => (P (φ n)).raw.weight i) W hWmem
    (fun B => ⟨T B, (hwin' B).mono fun _ ⟨i, hi, hBi, hiT, _⟩ => ⟨i, hi, hBi, hiT⟩⟩)
  let w := Nat.nth (· ∈ W)
  have hpos (i : ℕ) : ∀ᶠ n in atTop,
      i < (P (φ n)).length ∧ (P (φ n)).raw.weight i = w i :=
    IncreasingLists.positions_stabilize _ _ (fun n => (P (φ n)).valid.weight_strict) W hW hWmem i
  have hanchor (i : ℕ) : ∃ j > i, ∃ a : Γ,
      ∀ᶠ n in atTop, a ∈ ((P (φ n)).raw.piece j).support := by
    let B := w i
    have hpall : ∀ᶠ n in atTop, ∀ j ≤ T B,
        j < (P (φ n)).length ∧ (P (φ n)).raw.weight j = w j := by
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using
        (eventually_all_finset (I := Finset.range (T B+1))).mpr (fun j _ => hpos j)
    have hc (j : Fin (T B+1)) (a : s B) : ∀ᶠ n in atTop,
        a.val ∈ ((P (φ n)).raw.piece j).support ↔ b (.inr ⟨B, j.val, a⟩) :=
      hb (.inr ⟨B, j.val, a⟩)
    have hcall : ∀ᶠ n in atTop, ∀ j : Fin (T B+1), ∀ a : s B,
        a.val ∈ ((P (φ n)).raw.piece j).support ↔ b (.inr ⟨B, j.val, a⟩) :=
      eventually_all.mpr (fun j => eventually_all.mpr (hc j))
    obtain ⟨n, hn, hp, hcoord⟩ := ((hwin' B).and (hpall.and hcall)).exists
    obtain ⟨j, hj, hBj, hjT, a, has, haj⟩ := hn
    have hjT' : j ≤ T B := ((P (φ n)).valid.index_le_weight j hj).trans hjT
    have hij : i < j := (Nat.nth_lt_nth hW).mp (hBj.trans_eq (hp j hjT').2)
    have hba : b (.inr ⟨B, j, ⟨a, has⟩⟩) := (hcoord ⟨j, by omega⟩ ⟨a, has⟩).mp haj
    refine ⟨j, hij, a, ?_⟩
    exact (hb (.inr ⟨B, j, ⟨a, has⟩⟩)).mono (fun _ h => h.mpr hba)
  obtain ⟨Q, hQ⟩ := infinite_path_of_fixed_chain (P ∘ φ) (fun n => hmem (φ n))
    (fun i => (hpos i).mono fun _ h => h.1)
    (fun i => ⟨w i, (hpos i).mono fun _ h => h.2⟩) hanchor
  exact ⟨φ, Q, hφ, fun i => ((hpos i).and (hQ i)).mono (fun _ h => ⟨h.1.1, h.2⟩)⟩

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open Filter PathCoding
open scoped Classical Topology

lemma Family.m_mono (f : Family) : Monotone f.m :=
  (Parameters.m_strict f.s_ge_two).monotone.comp (fun _ _ h => Nat.sub_le_sub_right h 1)

lemma FinitePath.at_piece {f : Family} (P : FinitePath f) (i : Fin P.length)
    (a : Γ) (hi : P.raw.piece i a ≠ 0) : P.value a = P.raw.piece i a := by
  change (∑ j : Fin P.length, P.raw.piece j) a = _
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · intro j _ hji
    by_contra hj
    have he : j = i := Fin.ext (by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact (lt_irrefl a) (P.valid.successive j i h i.isLt a
          (Finsupp.mem_support_iff.mpr hj) a (Finsupp.mem_support_iff.mpr hi))
      · exact (lt_irrefl a) (P.valid.successive i j h j.isLt a
          (Finsupp.mem_support_iff.mpr hi) a (Finsupp.mem_support_iff.mpr hj)))
    exact hji he
  · simp

lemma FinitePath.coefficient_le {f : Family} (P : FinitePath f)
    (hm : ∀ i j, (P.piece i).child j ∈ f.norming) (a : Γ) :
    |(P.value a : ℝ)| ≤ 1/(f.m (P.raw.weight (P.hitIndex a)) : ℝ) := by
  rw [P.value_at_hit, ← P.value_eq, ← P.weight_eq]
  exact (P.piece (P.hitIndex a)).coefficient_bound
    (fun j b => full_coefficient_bound _ (f.norming_subset_full (hm _ j)) b) a

/-- Coordinate value of the bounded infinite path functional. -/
def InfinitePath.coordinateValue {f : Family} (P : InfinitePath f) (a : Γ) : ℚ :=
  (P.prefix_coordinate_eventually_constant a).choose

lemma InfinitePath.prefix_coordinateValue {f : Family} (P : InfinitePath f) (a : Γ) :
    ∀ᶠ n in atTop, (P.prefix n).value a = P.coordinateValue a :=
  (P.prefix_coordinate_eventually_constant a).choose_spec

lemma InfinitePath.coordinateValue_at_hit {f : Family} (P : InfinitePath f)
    (a : Γ) (i : ℕ) (hi : P.raw.piece i a ≠ 0) :
    P.coordinateValue a = P.raw.piece i a := by
  obtain ⟨n, hn, hiv⟩ := ((P.prefix_coordinateValue a).and (eventually_ge_atTop i)).exists
  exact hn.symm.trans (P.prefix_at_hit a i n hi hiv)

lemma InfinitePath.coordinateValue_zero {f : Family} (P : InfinitePath f)
    (a : Γ) (hi : ∀ i, P.raw.piece i a = 0) : P.coordinateValue a = 0 := by
  obtain ⟨n, hn⟩ := (P.prefix_coordinateValue a).exists
  rw [← hn]
  change (∑ i : Fin (n+1), P.raw.piece i) a = 0
  simp only [Finsupp.finsetSum_apply, hi, Finset.sum_const_zero]

/-- Stabilization is on exact actual uncropped pieces. Any extra pieces escape
in weight, and their coordinate coefficients tend to zero. -/
lemma stabilized_coordinate_tendsto {f : Family} (P : ℕ → FinitePath f)
    (hm : ∀ n i j, ((P n).piece i).child j ∈ f.norming) (Q : InfinitePath f)
    (hst : ∀ i, ∀ᶠ n in atTop, i < (P n).length ∧
      (P n).raw.piece i = Q.raw.piece i ∧ (P n).raw.weight i = Q.raw.weight i)
    (a : Γ) : Tendsto (fun n => ((P n).value a : ℝ)) atTop (𝓝 (Q.coordinateValue a : ℝ)) := by
  by_cases hh : ∃ i, Q.raw.piece i a ≠ 0
  · obtain ⟨i, hi⟩ := hh
    apply tendsto_const_nhds.congr'
    filter_upwards [hst i] with n hn
    rw [Q.coordinateValue_at_hit a i hi]
    congr 1
    exact ((P n).at_piece ⟨i, hn.1⟩ a (by simpa only [hn.2.1] using hi)).trans
      (congrArg (fun z : Array => z a) hn.2.1) |>.symm
  · push Not at hh
    rw [Q.coordinateValue_zero a hh, Rat.cast_zero]
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp f.reciprocal_summable.tendsto_atTop_zero ε hε
    have heps : 1/(Parameters.m f.s N : ℝ) < ε := by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity :
        0 ≤ 1/(Parameters.m f.s N : ℝ))] using hN N le_rfl
    have hall : ∀ᶠ n in atTop, ∀ i ≤ N+2, i < (P n).length ∧
        (P n).raw.piece i = Q.raw.piece i ∧ (P n).raw.weight i = Q.raw.weight i := by
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using
        (eventually_all_finset (I := Finset.range (N+2+1))).mpr (fun i _ => hst i)
    filter_upwards [hall] with n hn
    rw [Real.dist_eq, sub_zero]
    by_cases hz : (P n).value a = 0
    · simpa only [hz, Rat.cast_zero, abs_zero] using hε
    · let i := (P n).hitIndex a
      have hi : N+2 < i.val := by
        by_contra hnle
        have hzero : (P n).raw.piece i a = 0 := by
          rw [(hn i (by omega)).2.1, hh]
        exact hz ((P n).value_at_hit a |>.trans hzero)
      have hw : N+2 ≤ (P n).raw.weight i :=
        hi.le.trans ((P n).valid.index_le_weight i i.isLt)
      have hmle : Parameters.m f.s N ≤ f.m ((P n).raw.weight i) :=
        (Parameters.m_strict f.s_ge_two).monotone (by omega)
      exact ((P n).coefficient_le (hm n) a).trans_lt
        ((one_div_le_one_div_of_le (by exact_mod_cast Parameters.m_pos f.s N)
          (by exact_mod_cast hmle)).trans_lt heps)

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology
@[reducible] local instance dualEGroup12 : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance dualESpace12 : NormedSpace ℝ (StrongDual ℝ E) := inferInstance

lemma pathFunctional_finite {f : Family} (Q : InfinitePath f) (x : Γ →₀ ℝ) :
    pathFunctional Q (norming.includeFinite x) = x.sum (fun a t => t * (Q.coordinateValue a : ℝ)) := by
  apply tendsto_nhds_unique (pathPartial_tendsto Q _)
  apply tendsto_const_nhds.congr'
  filter_upwards [(eventually_all_finset x.support).mpr (fun a _ => Q.prefix_coordinateValue a)] with n hn
  rw [pathPartial, norming.functional_includeFinite]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [hn a ha]

lemma finitePath_mem_full {f : Family} (P : FinitePath f)
    (hm : ∀ i j, (P.piece i).child j ∈ f.norming) : P.value ∈ Full := by
  have h := TypeII.mem_family (P.oneTerm Crop.all) (fun _ i j => hm i j)
  apply f.norming_subset_full
  simpa only [FinitePath.oneTerm_value, Crop.all_set, restrict_univ] using h

def finitePathFunctional {f : Family} (P : FinitePath f)
    (hm : ∀ i j, (P.piece i).child j ∈ f.norming) : StrongDual ℝ E :=
  norming.functional ⟨P.value, finitePath_mem_full P hm⟩

lemma norm_finitePathFunctional_le {f : Family} (P : FinitePath f)
    (hm : ∀ i j, (P.piece i).child j ∈ f.norming) : ‖finitePathFunctional P hm‖ ≤ 1 :=
  norming.norm_functional_le _

lemma stabilized_path_tendsto {f : Family} (P : ℕ → FinitePath f)
    (hm : ∀ n i j, ((P n).piece i).child j ∈ f.norming) (Q : InfinitePath f)
    (hst : ∀ i, ∀ᶠ n in atTop, i < (P n).length ∧
      (P n).raw.piece i = Q.raw.piece i ∧ (P n).raw.weight i = Q.raw.weight i)
    (x : E) : Tendsto (fun n => finitePathFunctional (P n) (hm n) x) atTop (𝓝 (pathFunctional Q x)) := by
  let g : ℕ → StrongDual ℝ E := fun n => finitePathFunctional (P n) (hm n) - pathFunctional Q
  have hb (n : ℕ) : ‖g n‖ ≤ 2 := (norm_sub_le _ _).trans
    (by linarith [norm_finitePathFunctional_le (P n) (hm n), norm_pathFunctional_le Q])
  have hz (y : E) (hy : y ∈ Set.range norming.includeFinite) :
      Tendsto (fun n => g n y) atTop (𝓝 0) := by
    obtain ⟨v, rfl⟩ := hy
    have ht : Tendsto (fun n => finitePathFunctional (P n) (hm n) (norming.includeFinite v))
        atTop (𝓝 (pathFunctional Q (norming.includeFinite v))) := by
      simp only [finitePathFunctional, norming.functional_includeFinite, pathFunctional_finite]
      exact tendsto_finsetSum _ (fun a _ => tendsto_const_nhds.mul (stabilized_coordinate_tendsto P hm Q hst a))
    simpa only [g, sub_apply, sub_self] using ht.sub_const (pathFunctional Q (norming.includeFinite v))
  have ht := DenseZero.tendsto_zero_of_dense g 2 hb _ norming.denseRange_includeFinite hz x
  have he : (fun n => g n x + pathFunctional Q x) = (fun n => finitePathFunctional (P n) (hm n) x) := by
    funext n
    simp only [g, sub_apply, sub_add_cancel]
  simpa only [he, zero_add] using ht.add_const (pathFunctional Q x)

end SeparableQuotient.ActualSpace

end

end OAI
