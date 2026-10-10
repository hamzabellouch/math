import OAI.Geometry.SurfaceImmersion.Correction.MixedJetPolynomial

namespace OAI

/-! The coefficient part of the mixed polynomial variation is the actual
low-jet chain rule, with the position coordinates held fixed. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial

lemma variationLowJet_expansion (H : Base → Space) (p : Base) :
    variationLowJet H p = ∑ i : Fin 7 × Fin 4,
      jet H (lowWord i.1) i.2 p • lowBasis (.inr i) := by
  funext k
  cases k with
  | inl k => simp [variationLowJet, lowBasis]
  | inr k => simp [variationLowJet, lowBasis, Pi.single_apply]

lemma coefficient_variation_sum (c : LowJet × ℝ → ℝ) (G H : Base → Space) (z : Base × ℝ) :
    fderiv ℝ c (lowJet G z.1, z.2) (variationLowJet H z.1, 0) =
      ∑ i : Fin 7 × Fin 4, jet H (lowWord i.1) i.2 z.1 *
        fderiv ℝ c (lowJet G z.1, z.2) (lowBasis (.inr i), 0) := by
  let L : LowJet →L[ℝ] ℝ :=
    (fderiv ℝ c (lowJet G z.1, z.2)).comp (ContinuousLinearMap.inl ℝ LowJet ℝ)
  change L (variationLowJet H z.1) = _
  rw [variationLowJet_expansion, map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

namespace MixedExpression

lemma sumList_eval {ι : Type*} (l : List ι) (f : ι → MixedExpression)
    (G : Fin 4 → Base → Space) (z : Base × ℝ) :
    (sumList l f).eval G z = (l.map (fun i => (f i).eval G z)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [sumList, eval, List.map_cons, List.sum_cons, ih]

lemma differentiate_coeff_eval (c : LowJet × ℝ → ℝ) (j : Fin 3)
    (G : Fin 4 → Base → Space) (z : Base × ℝ) :
    ((coeff c).differentiate j).eval G z =
      fderiv ℝ c (lowJet (G 0) z.1, z.2) (variationLowJet (G j.succ) z.1, 0) := by
  rw [coefficient_variation_sum]
  simp only [differentiate, sumList_eval, eval, coefficientDerivative]
  exact Finset.sum_map_toList _ _

lemma smoothCoeffs_sumList {ι : Type*} {O : Set LowJet} (l : List ι) (f : ι → MixedExpression)
    (h : ∀ i ∈ l, (f i).SmoothCoeffs O) : (sumList l f).SmoothCoeffs O := by
  induction l with
  | nil => exact contDiffOn_const
  | cons i l ih => exact ⟨h i (List.mem_cons_self ..),
      ih (fun j hj => h j (List.mem_cons_of_mem _ hj))⟩

theorem differentiate_smoothCoeffs {O : Set LowJet} (hO : IsOpen O) (j : Fin 3)
    {e : MixedExpression} (he : e.SmoothCoeffs O) : (e.differentiate j).SmoothCoeffs O := by
  induction e with
  | coeff c =>
    apply smoothCoeffs_sumList
    intro i _
    exact (he.fderiv_of_isOpen (hO.prod isOpen_univ) (m := ∞) (by simp)).clm_apply contDiffOn_const
  | atom i w a e ih =>
    by_cases hi : i = 0
    · simpa only [differentiate, hi, ↓reduceIte, SmoothCoeffs] using And.intro he (ih he)
    · simpa only [differentiate, hi, ↓reduceIte, SmoothCoeffs] using ih he
  | add e f ihe ihf => exact ⟨ihe he.1, ihf he.2⟩

end MixedExpression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
