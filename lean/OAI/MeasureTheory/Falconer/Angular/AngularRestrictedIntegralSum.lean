import OAI.MeasureTheory.Falconer.Angular.AngularRestrictedKernel

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate
attribute [local instance] Classical.propDecidable

theorem angularRestrictedIntegral_sum (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (sourceAngularShellMeasure v Ψ)]
    (C : Finset (CellPath × CellPath))
    (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop)
    (U V : CellPath → ℝ × UnitCircle → ℂ)
    (hU : ∀ P, Measurable (U P)) (hV : ∀ Q, Measurable (V Q))
    {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hbU : ∀ P z, ‖U P z‖ ≤ B) (hbV : ∀ Q z, ‖V Q z‖ ≤ D) :
    angularKernelIntegral a v Ψ (angularRestrictedKernel C G U V) =
      ∑ row ∈ C, ∑ col ∈ C, if G row col then
        angularKernelIntegral a v Ψ (fun z => angularPairTerm
          (fun P => U P (z.1,z.2.1)) (fun Q => V Q (z.1,z.2.2)) row col) else 0 := by
  let F := fun (row col : CellPath × CellPath) (z : ℝ × (UnitCircle × UnitCircle)) =>
    if G row col then angularPairTerm
      (fun P => U P (z.1,z.2.1)) (fun Q => V Q (z.1,z.2.2)) row col else 0
  have hi (row col : CellPath × CellPath) : Integrable (F row col)
      ((sourceAngularShellMeasure v Ψ).prod (sourceArcLength.prod sourceArcLength)) := by
    by_cases hg : G row col
    · have hm : Measurable (F row col) := by dsimp [F]; simp only [hg,↓reduceIte,angularPairTerm]; fun_prop
      apply Integrable.of_bound hm.aestronglyMeasurable (B^2*D^2)
      apply Filter.Eventually.of_forall
      intro z
      dsimp [F]
      simp only [hg,↓reduceIte,angularPairTerm,norm_mul,Complex.norm_conj,pow_two]
      exact mul_le_mul
        (mul_le_mul (hbU row.1 _) (hbU col.1 _) (norm_nonneg _) hB)
        (mul_le_mul (hbV row.2 _) (hbV col.2 _) (norm_nonneg _) hD)
        (by positivity) (by positivity)
    · simp only [F,hg,↓reduceIte]
      exact integrable_zero _ _ _
  change ((2:ℝ)^(2*(v-a))) • (∫ z, ∑ row ∈ C, ∑ col ∈ C, F row col z ∂_) = _
  rw [integral_finsetSum C (fun row _ => integrable_finsetSum C (fun col _ => hi row col))]
  simp_rw [integral_finsetSum C (fun col _ => hi _ col),Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro col _
  by_cases hg : G row col <;> simp [F,hg,angularKernelIntegral]

end PlanarFalconer

end OAI
