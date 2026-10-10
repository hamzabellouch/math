import OAI.NumberTheory.Ostmann.Supply.LocalProjectionBlocks
import OAI.NumberTheory.Ostmann.Supply.UniformBalanced

namespace OAI

noncomputable section
namespace Ostmann.Supply
variable {p : ℕ} [NeZero p]
local notation "H" => EuclideanSpace ℂ (ZMod p)

theorem balanced_projection_row_le (S : Finset (ZMod p)) {ε : ℝ}
    (hlo : (1/3:ℝ) ≤ density S) (hhi : density S ≤ 2/3)
    (hε : 0 ≤ ε) (hg : gamma S ≤ ε^2) (v : centeredSpace Sᶜ) :
    ‖inner ℂ (uniformVector S) (spectralProjection (largeSpectrum S) (v:H))‖ ≤
      (2*ε/Real.sqrt p)*‖v‖ :=
  (projection_row_le S (by linarith) (by linarith) hε hg v).trans
    (mul_le_mul_of_nonneg_right (balanced_uniformCoefficient_error S hlo hhi hε) (norm_nonneg _))

theorem balanced_projection_column_le (S : Finset (ZMod p)) {ε : ℝ}
    (hlo : (1/3:ℝ) ≤ density S) (hhi : density S ≤ 2/3)
    (hε : 0 ≤ ε) (hg : gamma S ≤ ε^2) :
    ‖centeredProjection S (spectralProjection (largeSpectrum S) (uniformVector Sᶜ))‖ ≤
      2*ε/Real.sqrt p :=
  (projection_column_le S (by linarith) (by linarith) hε hg).trans
    (balanced_uniformCoefficient_error Sᶜ (balanced_compl S hlo hhi).1
      (balanced_compl S hlo hhi).2 hε)

end Ostmann.Supply

end

end OAI
