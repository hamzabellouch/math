import OAI.MeasureTheory.Falconer.Angular.AngularNearSum
import OAI.MeasureTheory.Falconer.Angular.AngularKernelIntegral

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate
attribute [local instance] Classical.propDecidable

noncomputable def angularRestrictedKernel (C : Finset (CellPath × CellPath))
    (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop)
    (U V : CellPath → ℝ × UnitCircle → ℂ) (z : ℝ × (UnitCircle × UnitCircle)) : ℂ :=
  angularRestrictedSum C G (fun P => U P (z.1,z.2.1)) (fun Q => V Q (z.1,z.2.2))

theorem angularRestrictedKernel_measurable (C : Finset (CellPath × CellPath))
    (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop)
    (U V : CellPath → ℝ × UnitCircle → ℂ)
    (hU : ∀ P, Measurable (U P)) (hV : ∀ Q, Measurable (V Q)) :
    Measurable (angularRestrictedKernel C G U V) := by
  unfold angularRestrictedKernel angularRestrictedSum angularPairTerm
  apply Finset.measurable_sum
  intro row _
  apply Finset.measurable_sum
  intro col _
  by_cases hg : G row col
  · simp only [hg,↓reduceIte]
    exact ((hU row.1).comp (measurable_fst.prodMk measurable_snd.fst)).mul
      (Complex.continuous_conj.measurable.comp ((hU col.1).comp (measurable_fst.prodMk measurable_snd.fst))) |>.mul
      (((hV row.2).comp (measurable_fst.prodMk measurable_snd.snd)).mul
      (Complex.continuous_conj.measurable.comp ((hV col.2).comp (measurable_fst.prodMk measurable_snd.snd))))
  · simp only [hg,↓reduceIte]
    exact measurable_const

theorem angularRestrictedKernel_bound (C : Finset (CellPath × CellPath))
    (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop)
    (U V : CellPath → ℝ × UnitCircle → ℂ) {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hbU : ∀ P z, ‖U P z‖ ≤ B) (hbV : ∀ Q z, ‖V Q z‖ ≤ D)
    (z : ℝ × (UnitCircle × UnitCircle)) :
    ‖angularRestrictedKernel C G U V z‖ ≤ (C.card:ℝ)^2*(B^2*D^2) := by
  have ht (row col : CellPath × CellPath) :
      ‖if G row col then angularPairTerm (fun P => U P (z.1,z.2.1))
        (fun Q => V Q (z.1,z.2.2)) row col else 0‖ ≤ B^2*D^2 := by
    by_cases hg : G row col
    · simp only [hg,↓reduceIte,angularPairTerm,norm_mul,Complex.norm_conj]
      simpa only [pow_two] using mul_le_mul
        (mul_le_mul (hbU row.1 _) (hbU col.1 _) (norm_nonneg _) hB)
        (mul_le_mul (hbV row.2 _) (hbV col.2 _) (norm_nonneg _) hD)
        (by positivity) (by positivity)
    · simp only [hg,↓reduceIte,norm_zero]
      positivity
  calc
    _ ≤ ∑ row ∈ C, ∑ col ∈ C, B^2*D^2 := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro row _
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun col _ => ht row col))
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

theorem angularRestrictedIntegral_complement (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (sourceAngularShellMeasure v Ψ)]
    (C : Finset (CellPath × CellPath))
    (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop)
    (U V : CellPath → ℝ × UnitCircle → ℂ)
    (hU : ∀ P, Measurable (U P)) (hV : ∀ Q, Measurable (V Q))
    {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hbU : ∀ P z, ‖U P z‖ ≤ B) (hbV : ∀ Q z, ‖V Q z‖ ≤ D) :
    angularKernelIntegral a v Ψ (angularRestrictedKernel C G U V) +
      angularKernelIntegral a v Ψ (angularRestrictedKernel C (fun row col => ¬ G row col) U V) =
      angularKernelIntegral a v Ψ (fun z => ∑ row ∈ C, ∑ col ∈ C,
        angularPairTerm (fun P => U P (z.1,z.2.1)) (fun Q => V Q (z.1,z.2.2)) row col) := by
  rw [← angularKernelIntegral_add a v Ψ _ _
    (angularRestrictedKernel_measurable C G U V hU hV)
    (angularRestrictedKernel_measurable C _ U V hU hV)
    (angularRestrictedKernel_bound C G U V hB hD hbU hbV)
    (angularRestrictedKernel_bound C _ U V hB hD hbU hbV)]
  congr 1
  funext z
  exact angularRestrictedSum_complement C G _ _

end PlanarFalconer

end OAI
