import OAI.Analysis.SeparableQuotients.WindowEstimates

namespace OAI

noncomputable section

namespace SeparableQuotient.InfiniteRamsey
open Filter
open scoped Classical

variable {χ : Type*} [Finite χ]

lemma eventually_constant (U : Ultrafilter ℕ) (f : ℕ → χ) :
    ∃ b, ∀ᶠ m in U, f m = b :=
  U.eventually_exists_iff.mp (Eventually.of_forall (fun m => ⟨f m, rfl⟩))

def limitColor (U : Ultrafilter ℕ) (c : Finset ℕ → χ) : ℕ → Finset ℕ → χ
  | 0, s => c s
  | k+1, s => (eventually_constant U (fun m => limitColor U c k (insert m s))).choose

lemma limitColor_eventually (U : Ultrafilter ℕ) (c : Finset ℕ → χ)
    (k : ℕ) (s : Finset ℕ) :
    ∀ᶠ m in U, limitColor U c k (insert m s) = limitColor U c (k+1) s :=
  (eventually_constant U (fun m => limitColor U c k (insert m s))).choose_spec

/-- The finite-set form of the infinite Ramsey theorem, proved by iterated
ultrafilter colors. Used only for the four-hit thinning in exact-pairs. -/
theorem homogeneous (n : ℕ) (c : Finset ℕ → χ) :
    ∃ (M : Set ℕ) (b : χ), M.Infinite ∧
      ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ M → s.card = n → c s = b := by
  let U := Ultrafilter.of (atTop : Filter ℕ)
  let b := limitColor U c n ∅
  let Good : Finset ℕ → Prop := fun S => ∀ s ⊆ S, s.card ≤ n → limitColor U c (n-s.card) s = b
  have hempty : Good ∅ := by
    intro s hs _
    have he : s = ∅ := Finset.subset_empty.mp hs
    subst s
    rfl
  have hstep (S : Finset ℕ) (hS : Good S) : ∃ m > S.sup id, Good (insert m S) := by
    have hev (s : Finset ℕ) (hs : s ⊆ S) : ∀ᶠ m in U,
        s.card < n → limitColor U c (n-s.card-1) (insert m s) = b := by
      by_cases hlt : s.card < n
      · have he : n-s.card-1+1 = n-s.card := by omega
        exact (limitColor_eventually U c (n-s.card-1) s).mono
          (fun _ h _ => h.trans (by rw [he]; exact hS s hs hlt.le))
      · exact Eventually.of_forall (fun _ h => (hlt h).elim)
    have hall : ∀ᶠ m in U, ∀ s ∈ S.powerset,
        s.card < n → limitColor U c (n-s.card-1) (insert m s) = b :=
      (eventually_all_finset S.powerset).mpr (fun s hs => hev s (Finset.mem_powerset.mp hs))
    have hlarge : ∀ᶠ m in U, S.sup id < m :=
      (eventually_gt_atTop (S.sup id)).filter_mono (Ultrafilter.of_le atTop)
    obtain ⟨m, hm, hall⟩ := (hlarge.and hall).exists
    have hmS : m ∉ S := by
      intro h
      exact (not_le_of_gt hm) (Finset.le_sup (f := id) h)
    refine ⟨m, hm, fun s hs hcard => ?_⟩
    by_cases hms : m ∈ s
    · let t := s.erase m
      have hts : t ⊆ S := by
        intro a ha
        have hh := Finset.mem_of_subset hs (Finset.mem_of_mem_erase ha)
        exact (Finset.mem_insert.mp hh).resolve_left (Finset.ne_of_mem_erase ha)
      have htc : t.card+1 = s.card := by
        exact Finset.card_erase_add_one hms
      have he : insert m t = s := Finset.insert_erase hms
      have hh := hall t (Finset.mem_powerset.mpr hts) (by omega)
      simpa only [he, show n-t.card-1 = n-s.card by omega] using hh
    · have hss : s ⊆ S := by
        intro a ha
        exact (Finset.mem_insert.mp (hs ha)).resolve_left (fun h => hms (h ▸ ha))
      exact hS s hss hcard
  let next (S : {S : Finset ℕ // Good S}) : ℕ := (hstep S.val S.property).choose
  have hn (S : {S : Finset ℕ // Good S}) : S.val.sup id < next S ∧ Good (insert (next S) S.val) :=
    (hstep S.val S.property).choose_spec
  let seq : ℕ → {S : Finset ℕ // Good S} := Nat.rec ⟨∅, hempty⟩
    (fun _ S => ⟨insert (next S) S.val, (hn S).2⟩)
  have hseq (i : ℕ) : (seq (i+1)).val = insert (next (seq i)) (seq i).val := rfl
  have hmono : Monotone (fun i => (seq i).val) := monotone_nat_of_le_succ
    (fun i => by rw [hseq]; exact Finset.subset_insert _ _)
  let v : ℕ → ℕ := fun i => next (seq i)
  have hvmem (i : ℕ) : v i ∈ (seq (i+1)).val := by rw [hseq]; exact Finset.mem_insert_self _ _
  have hv : StrictMono v := by
    apply strictMono_nat_of_lt_succ
    intro i
    exact (Finset.le_sup (f := id) (hvmem i)).trans_lt (hn (seq (i+1))).1
  let M : Set ℕ := ⋃ i, ↑(seq i).val
  have hM : M.Infinite := (Set.infinite_range_of_injective hv.injective).mono (by
    rintro _ ⟨i, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i+1, hvmem i⟩)
  refine ⟨M, b, hM, fun s hs hcard => ?_⟩
  have hex : ∀ a : s, ∃ i, a.val ∈ (seq i).val :=
    fun a => Set.mem_iUnion.mp (hs a.property)
  choose k hk using hex
  let N := Finset.univ.sup k
  have hsub : s ⊆ (seq N).val := by
    intro a ha
    exact hmono (Finset.le_sup (f := k) (Finset.mem_univ ⟨a, ha⟩)) (hk ⟨a, ha⟩)
  have hh := (seq N).property s hsub hcard.le
  simpa only [hcard, Nat.sub_self, limitColor] using hh

/-- Relative version for any infinite subset of the natural numbers. -/
theorem homogeneous_subset (n : ℕ) (c : Finset ℕ → χ) (A : Set ℕ) (hA : A.Infinite) :
    ∃ (M : Set ℕ) (b : χ), M ⊆ A ∧ M.Infinite ∧
      ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ M → s.card = n → c s = b := by
  let f : ℕ → ℕ := Nat.nth (· ∈ A)
  have hf : StrictMono f := Nat.nth_strictMono hA
  obtain ⟨B, b, hB, hb⟩ := homogeneous n (fun s => c (s.image f))
  refine ⟨f '' B, b, ?_, hB.image hf.injective.injOn, ?_⟩
  · rintro _ ⟨i, _, rfl⟩
    exact Nat.nth_mem_of_infinite hA i
  · intro s hs hcard
    let t := s.preimage f (hf.injective.injOn)
    have him : t.image f = s := by
      ext a
      constructor
      · intro ha
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
        exact Finset.mem_preimage.mp hi
      · intro ha
        obtain ⟨i, _, rfl⟩ := hs ha
        exact Finset.mem_image.mpr ⟨i, Finset.mem_preimage.mpr ha, rfl⟩
    have hts : (↑t : Set ℕ) ⊆ B := by
      intro i hi
      have hfi : f i ∈ s := (Finset.mem_preimage.mp hi)
      obtain ⟨j, hj, he⟩ := hs hfi
      exact hf.injective he ▸ hj
    have htcard : t.card = n := by rw [← hcard, ← him, Finset.card_image_of_injective _ hf.injective]
    simpa only [him] using hb t hts htcard

end SeparableQuotient.InfiniteRamsey

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter SeriesTails
open scoped Classical Topology

lemma four_distinct_finset (a b c d : ℕ) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ({a,b,c,d} : Finset ℕ).card = 4 := by
  have hac := hab.trans hbc
  have hbd := hbc.trans hcd
  have had := hac.trans hcd
  simp [ne_of_lt hab, ne_of_lt hac, ne_of_lt had, ne_of_lt hbc, ne_of_lt hbd, ne_of_lt hcd]

/-- Four-hit thinning under the Type I partition estimate. -/
theorem four_hits_thinning {f : Family} (x : ℕ → Γ →₀ ℝ) (J T : ℕ → ℕ)
    (hJT : ∀ i, J i ≤ T i)
    (horder : ∀ i j, i < j → T i < J j)
    (hs : ∀ i j, i < j → ∀ a ∈ (x i).support, ∀ b ∈ (x j).support, a < b)
    (hcoh : ∀ i j, i < j → ∀ a ∈ (x i).support, ∀ b ∈ (x i).support,
      rho (min a b) (max a b) ≤ J j)
    (M A δ : ℝ) (hM : ∀ i, ‖norming.includeFinite (x i)‖ ≤ M) (hA : 0 ≤ A) (hδ : 0 < δ)
    (hlow : ∀ i (e : TypeI f), (∀ j, e.child j ∈ f.norming) → e.weight < J i →
      |norming.evaluateArray (norming.includeFinite (x i)) e.value| ≤ A * f.theta e.weight)
    (htail : Tendsto (fun i => vectorL1 (x i) * tail (fun j => 1 / (f.m j : ℝ)) (T i+1)) atTop (𝓝 0))
    (hnull : ∀ Q : InfinitePath f, Tendsto (fun i => pathFunctional Q (norming.includeFinite (x i))) atTop (𝓝 0))
    (N : Set ℕ) (hN : N.Infinite) :
    ∃ W ⊆ N, W.Infinite ∧ ∀ S : Finset ℕ, (↑S : Set ℕ) ⊆ W → S.card = 4 →
      ¬ ∃ P : LegalFinitePath f, ∀ i ∈ S, WindowHit P (x i) (J i) (T i) δ := by
  let pos (S : Finset ℕ) : Prop := ∃ P : LegalFinitePath f, ∀ i ∈ S, WindowHit P (x i) (J i) (T i) δ
  let color : Finset ℕ → Bool := fun S => decide (pos S)
  obtain ⟨W, b, hWN, hW, hhom⟩ := InfiniteRamsey.homogeneous_subset 4 color N hN
  have hfalse : b = false := by
    by_contra hb
    have hb' : b = true := Bool.eq_true_of_not_eq_false hb
    let u : ℕ → ℕ := Nat.nth (· ∈ W)
    have hu : StrictMono u := Nat.nth_strictMono hW
    have humem (i : ℕ) : u i ∈ W := Nat.nth_mem_of_infinite hW i
    apply not_all_four_hits (fun i => x (u i)) (fun i => J (u i)) (fun i => T (u i))
      (fun i => hJT (u i)) (fun i j hij => horder _ _ (hu hij))
      (fun i j hij => hs _ _ (hu hij)) (fun i j hij => hcoh _ _ (hu hij))
      M A δ (fun i => hM (u i)) hA hδ (fun i => hlow (u i))
      (htail.comp hu.tendsto_atTop) (fun Q => (hnull Q).comp hu.tendsto_atTop)
    intro w v t k hwv hvt htk
    let S : Finset ℕ := {u w,u v,u t,u k}
    have hc : color S = true := (hhom S (by
      intro i hi
      simp only [S, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> exact humem _) (four_distinct_finset _ _ _ _ (hu hwv) (hu hvt) (hu htk))).trans hb'
    have hp : pos S := of_decide_eq_true hc
    obtain ⟨P, hP⟩ := hp
    exact ⟨P, hP _ (by simp [S]), hP _ (by simp [S]), hP _ (by simp [S]), hP _ (by simp [S])⟩
  refine ⟨W, hWN, hW, fun S hS hc hp => ?_⟩
  have he : color S = false := (hhom S hS hc).trans hfalse
  have hp' : pos S := hp
  change decide (pos S) = false at he
  rw [decide_eq_true hp'] at he
  contradiction

end SeparableQuotient.ActualSpace

end

end OAI
