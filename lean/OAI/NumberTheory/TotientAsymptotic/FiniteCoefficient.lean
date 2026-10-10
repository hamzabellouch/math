import OAI.NumberTheory.TotientAsymptotic.IntersectionLimit

namespace OAI

/-! A fixed finite universe for the phase-dependent inclusion-exclusion sums. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def allTailData (H : ℕ) : Finset (TailDatum H) := (finite_tail_data H).toFinset

def tailValueBound (H : ℕ) : ℕ :=
  tailCofactorBound H * (tailPrimeBound H)^(H-P H)

def nonemptyTailSubsets (H : ℕ) : Finset (Finset (TailDatum H)) := by
  classical
  exact (allTailData H).powerset.filter Finset.Nonempty

lemma witness_mem_allTailData {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (hη : IsWitness H s η) : η ∈ allTailData H :=
  (finite_tail_data H).mem_toFinset.mpr ⟨s, hs, hη⟩

lemma tail_finsum_eq_sum (H : ℕ) {s : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1)
    (d : ℕ) (F : Finset (TailDatum H) → ℝ) :
    (∑ᶠ T : Finset (TailDatum H),
      if T.Nonempty ∧ (↑T : Set (TailDatum H)) ⊆ witnesses H s d then F T else 0) =
    ∑ T ∈ nonemptyTailSubsets H,
      if (↑T : Set (TailDatum H)) ⊆ witnesses H s d then F T else 0 := by
  classical
  rw [finsum_eq_sum_of_support_subset _ (s := nonemptyTailSubsets H)]
  · apply Finset.sum_congr rfl
    intro T hT
    have hn := (Finset.mem_filter.mp hT).2
    simp only [hn, true_and]
  · intro T hT
    have ht : T.Nonempty ∧ (↑T : Set (TailDatum H)) ⊆ witnesses H s d := by
      by_contra h
      simp only [Function.mem_support, ite_eq_right h, ne_eq, not_true_eq_false] at hT
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, ht.1⟩
    intro η hη
    exact witness_mem_allTailData hs (ht.2 hη).1

def finiteTailCoefficient (H : ℕ) (f : ℝ → ℝ) (s : ℝ)
    (F : Finset (TailDatum H) → ℝ) : ℝ := by
  classical
  exact ∑ d ∈ Finset.Icc 1 (tailValueBound H),
    if IsTotient d then f ((ell d : ℝ)/d)/d *
      ∑ T ∈ nonemptyTailSubsets H,
        if (↑T : Set (TailDatum H)) ⊆ witnesses H s d then
          (-1 : ℝ)^(T.card-1)*F T else 0
    else 0

lemma AH_eq_finiteTailCoefficient (H : ℕ) (f : ℝ → ℝ) {s : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    AH H f s = finiteTailCoefficient H f s (intersectionWeight s) := by
  classical
  unfold AH finiteTailCoefficient
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc 1 (tailValueBound H))]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hdt : IsTotient d
    · simp only [ite_eq_left hdt]
      rw [tail_finsum_eq_sum H hs d]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      split_ifs <;> (try unfold intersectionWeight) <;> ring
    · simp only [ite_eq_right hdt, mul_zero]
  · intro d hd
    by_contra hmem
    have hz : ∀ T : Finset (TailDatum H),
        ¬ (T.Nonempty ∧ (↑T : Set (TailDatum H)) ⊆ witnesses H s d) := by
      rintro T ⟨hne, hsub⟩
      obtain ⟨η, hη⟩ := hne
      have hw := hsub hη
      have hdt : IsTotient d := by
        refine ⟨w η, ?_, hw.2⟩
        unfold w
        exact Nat.mul_pos hw.1.2.1 (Finset.prod_pos (fun l hl =>
          (hw.1.2.2.1 l hl).1.pos))
      exact hmem (Finset.mem_Icc.mpr ⟨isTotient_pos hdt, witness_totient_bound hs η hw⟩)
    have hh : (∑ᶠ T : Finset (TailDatum H),
        if T.Nonempty ∧ (↑T : Set (TailDatum H)) ⊆ witnesses H s d then
          (-1 : ℝ)^(T.card-1)*Real.exp (-(gamma/alpha s)*
            ∑' n : ℕ, rho^(H+n)*maxD (H+n) T) else 0) = 0 := by
      simp only [ite_eq_right (hz _), finsum_zero]
    simp only [Function.mem_support] at hd
    split_ifs at hd with hdt
    · exact hd (by rw [hh, mul_zero])
    · exact hd rfl

end TotientAsymptotic

end

end OAI
