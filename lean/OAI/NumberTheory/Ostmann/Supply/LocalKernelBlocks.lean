import OAI.NumberTheory.Ostmann.Supply.BalancedProjectionBlocks
import OAI.NumberTheory.Ostmann.Supply.LocalBlockConstant
import OAI.NumberTheory.Ostmann.Supply.LocalKernelOperator
import OAI.NumberTheory.Ostmann.Supply.ProjectionScalar
import OAI.NumberTheory.Ostmann.Supply.RawBlockBounds

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [NeZero p]
local notation "H" => EuclideanSpace ℂ (ZMod p)

def kernelScalar (S : Finset (ZMod p)) (t : ℝ) (u v : ℂ) : ℂ :=
  inner ℂ (uniformVector S) (localKernelOperator S t u v (uniformVector Sᶜ))

theorem kernelScalar_expansion (S : Finset (ZMod p)) (t : ℝ) (u v : ℂ)
    (hS : S.Nonempty) (hT : Sᶜ.Nonempty) :
    kernelScalar S t u v = 1 + ((u+v)*(t:ℂ))*
      inner ℂ (uniformVector S) (spectralProjection (largeSpectrum S) (uniformVector Sᶜ)) +
      (u*v)*inner ℂ (uniformVector S) (squaredLocalKernelOperator S t (uniformVector Sᶜ)) := by
  simp only [kernelScalar,localKernelOperator_decomposition,
    add_apply,smul_apply,
    convolution_one_apply,sum_uniformVector_all _ hT,one_smul,
    inner_add_right,inner_smul_right,uniformVector_oneVector _ hS]

theorem localKernel_row_bound (S : Finset (ZMod p)) (t : ℝ) (u v : ℂ) {ε : ℝ}
    (hlo : (1/3:ℝ) ≤ density S) (hhi : density S ≤ 2/3)
    (hε : 0 ≤ ε) (hg : gamma S ≤ ε^2) (z : centeredSpace Sᶜ) :
    ‖inner ℂ (uniformVector S) (localKernelOperator S t u v (z:H))‖ ≤
      (‖(u+v)*(t:ℂ)‖*(2*ε/Real.sqrt p) +
        ‖u*v‖*((2/Real.sqrt p)*‖squaredLocalKernelOperator S t‖))*‖z‖ := by
  simp only [localKernelOperator_decomposition,add_apply,
    smul_apply,convolution_one_apply,sum_centered_all,zero_smul,
    inner_add_right,inner_smul_right,zero_add]
  have hP := balanced_projection_row_le S hlo hhi hε hg z
  have hB : ‖inner ℂ (uniformVector S) (squaredLocalKernelOperator S t (z:H))‖ ≤
      ((2/Real.sqrt p)*‖squaredLocalKernelOperator S t‖)*‖z‖ :=
    (raw_row_bound S Sᶜ _ z).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (balanced_uniform_norm S hlo) (norm_nonneg _)) (norm_nonneg _))
  calc
    _ ≤ ‖((u+v)*(t:ℂ))*inner ℂ (uniformVector S) (spectralProjection (largeSpectrum S) (z:H))‖ +
      ‖(u*v)*inner ℂ (uniformVector S) (squaredLocalKernelOperator S t (z:H))‖ := norm_add_le _ _
    _ ≤ ‖(u+v)*(t:ℂ)‖*((2*ε/Real.sqrt p)*‖z‖) +
      ‖u*v‖*(((2/Real.sqrt p)*‖squaredLocalKernelOperator S t‖)*‖z‖) := by
        simp only [norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hP (by positivity))
          (mul_le_mul_of_nonneg_left hB (by positivity))
    _ = _ := by ring

theorem localKernel_column_bound (S : Finset (ZMod p)) (t : ℝ) (u v : ℂ) {ε : ℝ}
    (hlo : (1/3:ℝ) ≤ density S) (hhi : density S ≤ 2/3)
    (hε : 0 ≤ ε) (hg : gamma S ≤ ε^2) :
    ‖centeredProjection S (localKernelOperator S t u v (uniformVector Sᶜ))‖ ≤
      ‖(u+v)*(t:ℂ)‖*(2*ε/Real.sqrt p) +
        ‖u*v‖*((2/Real.sqrt p)*‖squaredLocalKernelOperator S t‖) := by
  simp only [localKernelOperator_decomposition,add_apply,
    smul_apply,convolution_one_apply,
    sum_uniformVector_all _ (balanced_nonempty _ (balanced_compl S hlo hhi).1),one_smul,
    map_add,map_smul,centeredProjection_oneVector,zero_add]
  have hP := balanced_projection_column_le S hlo hhi hε hg
  have hB : ‖centeredProjection S (squaredLocalKernelOperator S t (uniformVector Sᶜ))‖ ≤
      (2/Real.sqrt p)*‖squaredLocalKernelOperator S t‖ := by
    calc
      _ ≤ ‖squaredLocalKernelOperator S t‖*‖uniformVector Sᶜ‖ := raw_column_bound S Sᶜ _
      _ ≤ ‖squaredLocalKernelOperator S t‖*(2/Real.sqrt p) :=
        mul_le_mul_of_nonneg_left (balanced_uniform_norm _ (balanced_compl S hlo hhi).1) (norm_nonneg _)
      _ = _ := by ring
  exact (norm_add_le _ _).trans (by
    simp only [norm_smul]
    exact add_le_add (mul_le_mul_of_nonneg_left hP (by positivity))
      (mul_le_mul_of_nonneg_left hB (by positivity)))

theorem localKernel_lower_bound (S : Finset (ZMod p)) (t : ℝ) (u v : ℂ)
    (z : centeredSpace Sᶜ) :
    ‖centeredProjection S (localKernelOperator S t u v (z:H))‖ ≤
      (‖(u+v)*(t:ℂ)‖/2+‖u*v‖*‖squaredLocalKernelOperator S t‖)*‖z‖ := by
  simp only [localKernelOperator_decomposition,add_apply,
    smul_apply,convolution_one_apply,sum_centered_all,zero_smul,
    map_add,map_smul,zero_add]
  calc
    _ ≤ ‖((u+v)*(t:ℂ)) • centeredProjection S (spectralProjection (largeSpectrum S) (z:H))‖ +
      ‖(u*v) • centeredProjection S (squaredLocalKernelOperator S t (z:H))‖ := norm_add_le _ _
    _ ≤ ‖(u+v)*(t:ℂ)‖*((1/2:ℝ)*‖z‖)+‖u*v‖*(‖squaredLocalKernelOperator S t‖*‖z‖) := by
      simp only [norm_smul]
      exact add_le_add (mul_le_mul_of_nonneg_left (projection_lower_le S z) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (raw_lower_bound S Sᶜ _ z) (norm_nonneg _))
    _ = _ := by ring

end Ostmann.Supply

end

end OAI
