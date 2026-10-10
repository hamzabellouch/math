import OAI.Analysis.LipschitzHilbert.Fourier.VerticalBinVector

namespace OAI

/-! The number of retained vertical bins has the allowed exponential growth. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem verticalBinKernelCost_nonneg : 0≤verticalBinKernelCost :=
  integral_nonneg (fun _ => norm_nonneg _)

def verticalBinVectorCost (w W c C : ℝ) : ℝ :=
  ((verticalBinLabels ⌈C*W/w⌉₊ w W c C).card:ℝ)*verticalBinKernelCost

theorem verticalBinVectorCost_nonneg (w W c C : ℝ) : 0≤verticalBinVectorCost w W c C :=
  mul_nonneg (Nat.cast_nonneg _) verticalBinKernelCost_nonneg

theorem verticalBinVectorCost_growth (w W c C L m : ℝ) (hw : 0<w) (hW : 0<W)
    (hC : 0<C) (hL : 0≤L) (hWm : W=m*w) (hm : m≤2*Real.exp (L^(9/10:ℝ))) :
    verticalBinVectorCost w W c C≤
      ((4*C+3)*(verticalBinKernelCost+1))*Real.exp (L^(9/10:ℝ)) := by
  have hcard := verticalBinLabels_card w W c C hw hW hC.le
  have hquot : C*W/w=C*m := by rw [hWm]; field_simp
  have hcardBound : ((verticalBinLabels ⌈C*W/w⌉₊ w W c C).card:ℝ)≤2*(C*m)+3 := by
    calc
      _ ≤ 2*(C*W/w)+3 := hcard
      _ = _ := by rw [hquot]
  have he : 1≤Real.exp (L^(9/10:ℝ)) := Real.one_le_exp (Real.rpow_nonneg hL _)
  have hcard' : ((verticalBinLabels ⌈C*W/w⌉₊ w W c C).card:ℝ)≤
      (4*C+3)*Real.exp (L^(9/10:ℝ)) := by nlinarith
  have hcost := mul_le_mul_of_nonneg_right hcard' verticalBinKernelCost_nonneg
  dsimp only [verticalBinVectorCost]
  have hdiff : 0≤(4*C+3)*Real.exp (L^(9/10:ℝ)) := by positivity
  nlinarith only [hcost,hdiff]

end LipschitzHilbert.PacketRepresentation

end

end OAI
