import OAI.MeasureTheory.Falconer.Slicing.GramSchmidtVolume
import OAI.MeasureTheory.Falconer.Geometry.PiCoordinateSections
import OAI.MeasureTheory.Falconer.Slicing.GaussianRows

namespace OAI

/-! # A square Gaussian matrix is nonsingular almost surely

Each zero Gram--Schmidt residual lies in a Gaussian-null fixed hyperplane
when the other rows are fixed. No polynomial zero-set theorem is assumed.
-/
namespace Falconer
open Set MeasureTheory ProbabilityTheory InnerProductSpace
open scoped ENNReal BigOperators
variable {n : ℕ}

theorem gaussian_residual_zero_mass (i : Fin (n+1)) :
    gaussianRows (n+1) (n+1) {v | gramSchmidt ℝ v i = 0} = 0 := by
  have hh := pi_measure_le_of_coordinate_sections (stdGaussian (Space (n+1))) i
    {v | gramSchmidt ℝ v i = 0}
    (measurableSet_eq_fun (gramSchmidt_measurable i) measurable_const) (0:ℝ≥0∞)
  have hsections : ∀ y, stdGaussian (Space (n+1))
      {x | gramSchmidt ℝ (i.insertNth x y) i = 0} ≤ 0 := by
    intro y
    let v : Fin (n+1) → Space (n+1) := i.insertNth 0 y
    obtain ⟨w,hw,hinner⟩ := small_residual_fixed_slab v i
    have hsub : {x : Space (n+1) | gramSchmidt ℝ (i.insertNth x y) i = 0} ⊆
        {x | |inner ℝ w x| ≤ 0} := by
      intro x hx
      change gramSchmidt ℝ (i.insertNth x y) i = 0 at hx
      have hprefix : ∀ j : Fin (n+1), j < i →
          (i.insertNth x y : Fin (n+1) → Space (n+1)) j = v j := by
        intro j hj
        dsimp [v]
        rw [Fin.insertNth_apply_below hj,Fin.insertNth_apply_below hj]
      have hb := hinner (i.insertNth x y) hprefix
      simpa only [mem_ofPred_eq,Fin.insertNth_apply_same,hx,norm_zero] using hb
    exact (measure_mono hsub).trans (by simpa using gaussian_unit_inner_band hw (le_refl (0:ℝ)))
  have hle : gaussianRows (n+1) (n+1) {v | gramSchmidt ℝ v i = 0} ≤ 0 := by
    simpa only [gaussianRows,zero_mul] using hh hsections
  exact le_antisymm hle bot_le

theorem gaussian_square_det_ne_zero_ae :
    ∀ᵐ v : Fin (n+1) → Space (n+1) ∂gaussianRows (n+1) (n+1),
      (euclideanColumnMatrix v).det ≠ 0 := by
  have hzero : gaussianRows (n+1) (n+1)
      (⋃ i : Fin (n+1), {v | gramSchmidt ℝ v i = 0}) = 0 :=
    measure_iUnion_null gaussian_residual_zero_mass
  have hgood : ∀ᵐ v : Fin (n+1) → Space (n+1) ∂gaussianRows (n+1) (n+1),
      v ∉ ⋃ i : Fin (n+1), {v | gramSchmidt ℝ v i = 0} := by
    rw [ae_iff]
    simpa only [not_not,ofPred_mem_eq] using hzero
  filter_upwards [hgood] with v hv hdet
  have hp : (∏ i : Fin (n+1), ‖gramSchmidt ℝ v i‖) = 0 := by
    rw [← gram_volume_eq_residual_product,euclideanColumnMatrix_gram_sqrt,hdet,abs_zero]
  obtain ⟨i,_,hi⟩ := Finset.prod_eq_zero_iff.mp hp
  exact hv (mem_iUnion.mpr ⟨i,norm_eq_zero.mp hi⟩)

end Falconer

end OAI
