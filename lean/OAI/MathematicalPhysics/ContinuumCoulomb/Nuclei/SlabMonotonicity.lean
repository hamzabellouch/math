import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabSections

namespace OAI

/-! Coordinatewise monotonicity of the actual singular slab potential.
This strengthens centering to comparison at any two absolute coordinates. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

theorem coulombLineIntegral_abs_antitone {A H x y : ℝ} (hA : 0 < A)
    (hH : 0 ≤ H) (hxy : |x| ≤ |y|) :
    centeredLineIntegral (coulombLineKernel A) H y ≤
      centeredLineIntegral (coulombLineKernel A) H x := by
  have he (t : ℝ) : coulombLineKernel A (-t) = coulombLineKernel A t := by
    simp [coulombLineKernel]
  have ha (t : ℝ) : centeredLineIntegral (coulombLineKernel A) H |t| =
      centeredLineIntegral (coulombLineKernel A) H t := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht]
      exact centeredLineIntegral_even _ he H t
  rw [← ha x, ← ha y]
  exact coulombLineIntegral_antitone hA hH (abs_nonneg x) (abs_nonneg y) hxy

private theorem coulombLine_setIntegral_abs_antitone {A H x y : ℝ}
    (hA : 0 < A) (hH : 0 ≤ H) (hxy : |x| ≤ |y|) :
    (∫ t in Set.Icc (-H) H, coulombLineKernel A (y-t)) ≤
      ∫ t in Set.Icc (-H) H, coulombLineKernel A (x-t) := by
  have h := coulombLineIntegral_abs_antitone hA hH hxy
  simp only [centeredLineIntegral_translate,
    intervalIntegral.integral_of_le (show -H ≤ H by linarith),
    ← integral_Icc_eq_integral_Ioc] at h
  exact h

private theorem regularizedSections_integrable {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) (i : Fin 3) :
    Integrable (fun p : ℝ × (Fin 2 → ℝ) => NeutralAtom.regularizedKernel epsilon
      (y-WithLp.toLp 2 (i.insertNth p.1 p.2)))
      ((slabAxisMeasure H S i).prod
        (Measure.pi (fun j : Fin 2 => slabAxisMeasure H S (i.succAbove j)))) := by
  have hp := (measurePreserving_piFinSuccAbove (slabAxisMeasure H S) i).symm
  exact (hp.integrable_comp_emb
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i).symm.measurableEmbedding).mpr
      ((slabProduct_integrable H S _).mpr (regularizedSlab_integrableOn hepsilon hH hS y))

theorem regularizedSlab_coordinate_antitone {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (x y : Position) (i : Fin 3)
    (hother : ∀ j : Fin 2, x (i.succAbove j) = y (i.succAbove j))
    (hxy : |x i| ≤ |y i|) :
    (∫ b in slabDomain H S, NeutralAtom.regularizedKernel epsilon (y-b)) ≤
      ∫ b in slabDomain H S, NeutralAtom.regularizedKernel epsilon (x-b) := by
  rw [regularizedSlab_sectionIntegral hepsilon hH hS y i,
    regularizedSlab_sectionIntegral hepsilon hH hS x i]
  apply integral_mono
    (regularizedSections_integrable hepsilon hH hS y i).integral_prod_right
    (regularizedSections_integrable hepsilon hH hS x i).integral_prod_right
  intro v
  simp_rw [regularizedKernel_section, hother]
  have hA : 0 < epsilon^2+∑ j : Fin 2, (y (i.succAbove j)-v j)^2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hepsilon)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hside : 0 ≤ slabSide H S i := by unfold slabSide; split <;> assumption
  exact coulombLine_setIntegral_abs_antitone hA hside hxy

/-- Increasing a single absolute coordinate increases the singular slab potential. -/
theorem slabPotential_coordinate_monotone {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (x y : Position) (i : Fin 3)
    (hother : ∀ j : Fin 2, x (i.succAbove j) = y (i.succAbove j))
    (hxy : |x i| ≤ |y i|) : slabPotential rho H S x ≤ slabPotential rho H S y := by
  let epsilon : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hep (n : ℕ) : 0 < epsilon n := by dsimp [epsilon]; positivity
  have heps : Tendsto epsilon atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  apply le_of_tendsto_of_tendsto
    (regularizedSlabPotential_tendsto hep heps rho hH hS x)
    (regularizedSlabPotential_tendsto hep heps rho hH hS y)
  exact Filter.Eventually.of_forall (fun n =>
    mul_le_mul_of_nonpos_left
      (regularizedSlab_coordinate_antitone (hep n).ne' hH hS x y i hother hxy)
      (neg_nonpos.mpr hrho))

end ContinuumCoulomb

end

end OAI
