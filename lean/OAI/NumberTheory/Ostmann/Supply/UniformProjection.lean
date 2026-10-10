import OAI.NumberTheory.Ostmann.Supply.CenteredOrthogonality
import OAI.NumberTheory.Ostmann.Supply.KernelMoments
import OAI.NumberTheory.Ostmann.Supply.UniformNorms

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [NeZero p]
local notation "H" => EuclideanSpace ℂ (ZMod p)

theorem spectralProjection_oneVector (E : Finset (ZMod p)) (hE : 0 ∉ E) :
    spectralProjection E oneVector = 0 := by
  rw [← convolution_fourierKernel]
  ext x
  simp only [convolutionOperator_apply, oneVector_apply, mul_one, fourierKernel_sum E hE,
    PiLp.zero_apply]

theorem spectralProjection_uniform (S : Finset (ZMod p))
    (hpos : 0 < density S) (hlt : density S < 1) :
    spectralProjection (largeSpectrum S) (uniformVector S) =
      (uniformCoefficient S : ℂ) • spectralProjection (largeSpectrum S) (normalizedVector S) := by
  rw [uniformVector_decomposition S hpos hlt, map_add, map_smul, map_smul,
    spectralProjection_oneVector _ (zero_not_mem_largeSpectrum S), smul_zero, zero_add]

theorem spectralProjection_uniform_compl (S : Finset (ZMod p))
    (hpos : 0 < density S) (hlt : density S < 1) :
    spectralProjection (largeSpectrum S) (uniformVector Sᶜ) =
      -(uniformCoefficient Sᶜ : ℂ) • spectralProjection (largeSpectrum S) (normalizedVector S) := by
  rw [uniformVector_compl_decomposition S hpos hlt, map_sub, map_smul, map_smul,
    spectralProjection_oneVector _ (zero_not_mem_largeSpectrum S), smul_zero, zero_sub,
    neg_smul]

theorem centered_sparse_projection_le (S T : Finset (ZMod p)) {ε : ℝ}
    (hT : centeredProjection T (normalizedVector S) = 0)
    (hε : 0 ≤ ε) (hg : gamma S ≤ ε^2) :
    ‖centeredProjection T (spectralProjection (largeSpectrum S) (normalizedVector S))‖ ≤
      ε*Real.sqrt p := by
  have he : centeredProjection T (spectralProjection (largeSpectrum S) (normalizedVector S)) =
      centeredProjection T (spectralProjection (largeSpectrum S) (normalizedVector S)-normalizedVector S) := by
    rw [map_sub,hT,sub_zero]
  rw [he]
  exact ((centeredSpace T).norm_starProjection_apply_le _).trans
    (sparse_projection_error_le S hε hg)

theorem centered_projection_uniform_le (S T : Finset (ZMod p)) {ε : ℝ}
    (hpos : 0 < density S) (hlt : density S < 1)
    (hT : centeredProjection T (normalizedVector S) = 0)
    (hε : 0 ≤ ε) (hg : gamma S ≤ ε^2) :
    ‖centeredProjection T (spectralProjection (largeSpectrum S) (uniformVector S))‖ ≤
      uniformCoefficient S * (ε*Real.sqrt p) := by
  rw [spectralProjection_uniform S hpos hlt,map_smul,norm_smul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (uniformCoefficient_nonneg S)]
  exact mul_le_mul_of_nonneg_left (centered_sparse_projection_le S T hT hε hg)
    (uniformCoefficient_nonneg S)

theorem centered_projection_uniform_compl_le (S T : Finset (ZMod p)) {ε : ℝ}
    (hpos : 0 < density S) (hlt : density S < 1)
    (hT : centeredProjection T (normalizedVector S) = 0)
    (hε : 0 ≤ ε) (hg : gamma S ≤ ε^2) :
    ‖centeredProjection T (spectralProjection (largeSpectrum S) (uniformVector Sᶜ))‖ ≤
      uniformCoefficient Sᶜ * (ε*Real.sqrt p) := by
  rw [spectralProjection_uniform_compl S hpos hlt,map_smul,norm_smul,norm_neg,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (uniformCoefficient_nonneg Sᶜ)]
  exact mul_le_mul_of_nonneg_left (centered_sparse_projection_le S T hT hε hg)
    (uniformCoefficient_nonneg Sᶜ)

end Ostmann.Supply

end

end OAI
