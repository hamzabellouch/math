import OAI.Analysis.LipschitzHilbert.Fourier.ShortSlopeLinearity
import OAI.Analysis.LipschitzHilbert.Estimates.PhysicalBinAdjoint
import OAI.Analysis.LipschitzHilbert.Estimates.TotalBinErrorScale

namespace OAI

/-! The exact bin diagonalization of the actual localized time operator.
The error is the same projected commutator sum whose energy is estimated. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem actualBin_reconstruction (k : SchwartzMap ℝ ℂ) (N : ℕ)
    (topLength w W c C : ℝ) (htop : 0<topLength) (hw : 0<w) (hW : 0<W) (hc : 0<c)
    (u : (ℝ×ℝ) → ℝ) (hum : Measurable u) (f : SchwartzMap (ℝ×ℝ) ℂ)
    (hband : ∀ omega, planarFourier f omega≠0 → c≤w*omega.2 ∧ w*omega.2≤C)
    (z : ℝ×ℝ) :
    let J := ⌈C*W/w⌉₊
    let I := verticalBinLabels J w W c C
    shortSlopeOperator (finiteTimeKernel k N topLength) u f z=
      (∑ n : I, verticalConvolution (verticalProfileKernel verticalBinProfile W
        (verticalBinCenter J W n)) (shortSlopeOperator (finiteTimeKernel k N topLength) u
          (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) f)) z)-
        totalProjectedBinError k N topLength w W c C u f z := by
  intro J I
  let P := fun n : I => schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) f
  let T := finiteTimeKernel k N topLength
  have hr := shortSlopeOperator_bin_reconstruction T (finiteTimeKernel_integrable k N topLength htop)
    u f w W c C hw hW hc hband z
  have he (n : I) : shortSlopeOperator T u
      (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) (P n)) z=
    verticalConvolution (verticalProfileKernel verticalBinProfile W (verticalBinCenter J W n))
      (shortSlopeOperator T u (P n)) z-
      finiteBinError k verticalBinProfile N topLength W (verticalBinCenter J W n) u (P n) z := by
    have h := congrFun (finiteActualBinCommutator_eq k verticalBinProfile N topLength W
      (verticalBinCenter J W n) htop hW u hum (P n)) z
    have hp : verticalConvolution (verticalProfileKernel verticalBinProfile W (verticalBinCenter J W n))
        (P n)=(schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) (P n) :
          (ℝ×ℝ) → ℂ) := by
      funext x
      exact (schwartzVerticalProjection_eq_convolution _ W _ hW (P n) x).symm
    rw [hp] at h
    change _-shortSlopeOperator T u
      (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) (P n)) z=_ at h
    linear_combination -h
  calc
    _ = ∑ n : I, shortSlopeOperator T u
        (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) (P n)) z := hr
    _ = ∑ n : I, (verticalConvolution
        (verticalProfileKernel verticalBinProfile W (verticalBinCenter J W n))
          (shortSlopeOperator T u (P n)) z-
        finiteBinError k verticalBinProfile N topLength W (verticalBinCenter J W n) u (P n) z) :=
      Finset.sum_congr rfl (fun n _ => he n)
    _ = _ := by rw [Finset.sum_sub_distrib]; rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
