import OAI.Analysis.LipschitzHilbert.Estimates.MihlinPVCommutator
import OAI.Analysis.LipschitzHilbert.Fourier.SignedAnnularOperator
import OAI.Analysis.LipschitzHilbert.Fourier.PlaneVerticalLipschitz

namespace OAI

/-! Uniform actual signed-annular principal-value commutators for the
Euclidean Lipschitz slope fields in the target theorem. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def signedPVCommutatorConstant : ℝ :=
  32*lineCommutatorNormConstant*signedAnnularMihlinConstant

theorem signedPVCommutatorConstant_nonneg : 0≤signedPVCommutatorConstant :=
  mul_nonneg (mul_nonneg (by norm_num) lineCommutatorNormConstant_nonneg) signedAnnularMihlinConstant_nonneg

theorem signedPVCommutator_bound (N : ℕ) (s : ℕ → Bool)
    (field : Plane → ℝ) (hf : LipschitzWith 1 field) (hfb : ∀ z, |field z|≤1/4)
    (R : ℝ) (hR : 0<R) (hRs : R≤1/4) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    MemLp (principalValueProfileCommutator (signedAnnularSymbol N s) 1 0 R
      (fun z => field (planeCoordinates z)) f) 2 planeMeasure ∧
    eLpNorm (principalValueProfileCommutator (signedAnnularSymbol N s) 1 0 R
      (fun z => field (planeCoordinates z)) f) 2 planeMeasure≤
        ENNReal.ofReal ((signedPVCommutatorConstant*R)*‖f.toLp 2 planeMeasure‖) := by
  apply principalValueProfileCommutator_mihlin_bound _ signedAnnularMihlinConstant
    signedAnnularMihlinConstant_nonneg
  · intro r hr
    exact signedAnnularSymbol_mihlin_four N r (hr.trans (by norm_num)) s
  · exact hR
  · exact hRs
  · simpa only [mul_one] using product_slope_lipschitz field hf
  · exact product_slope_vertical_lipschitz field hf
  · intro z
    exact (hfb (planeCoordinates z)).trans (by norm_num)

end LipschitzHilbert.PacketRepresentation

end

end OAI
