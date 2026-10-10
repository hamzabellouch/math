import Mathlib
import OAI.Geometry.PrescribedPotential.ComplexKernel
import OAI.Geometry.PrescribedPotential.PatchCutoffs
import OAI.Geometry.PrescribedPotential.ConstantProjection
import OAI.Geometry.PrescribedPotential.FredholmRegularity
import OAI.Geometry.PrescribedPotential.GlobalSmooth

namespace OAI

/-! Fredholm Kernel. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped SchwartzMap ContDiff Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

def fredholmOperator (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) : D.localizers.Sobolev 0 →L[ℝ] D.localizers.Sobolev 0 :=
  (m^2 : ℝ) • D.resolventZero m hm he - P.proj

lemma fredholm_kernel (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) (w : D.localizers.Sobolev 0)
    (hw : D.fredholmOperator m hm he P w = w) : w = 0 := by
  obtain ⟨c, hc⟩ := P.value w
  have hw' : w = D.localizers.embed 0 (-Smooth.const c) +
      (m^2 : ℝ) • D.resolventZero m hm he w := by
    change (m^2 : ℝ) • D.resolventZero m hm he w - P.proj w = w at hw
    rw [hc] at hw
    rw [map_neg]
    calc
      w = (m^2 : ℝ) • D.resolventZero m hm he w -
          D.localizers.embed 0 (Smooth.const c) := hw.symm
      _ = _ := by abel
  obtain ⟨u, hu⟩ := D.allRegular_smooth (D.resolvent_feedback_regular m hm he w _ hw')
  have hs := D.smooth_shifted_equation m hm he w u hu
  have hL : complexL g u = Smooth.const c := by
    apply D.localizers.embed_injective 0
    have h := hs.trans hw'
    rw [map_sub, map_smul, map_neg, ← hu] at h
    apply sub_right_inj.mp
    calc
      (m^2 : ℝ) • D.localizers.embed 0 u - D.localizers.embed 0 (complexL g u) =
          -D.localizers.embed 0 (Smooth.const c) + (m^2 : ℝ) • D.localizers.embed 0 u := h
      _ = (m^2 : ℝ) • D.localizers.embed 0 u - D.localizers.embed 0 (Smooth.const c) := by abel
  have hc0 := complexL_constant_rhs_zero g u hL
  have hL0 : complexL g u = 0 := by rw [hL, hc0]; rfl
  obtain ⟨a, ha⟩ := complexL_kernel g u hL0
  have hwc : w = D.localizers.embed 0 (Smooth.const ((m^2 : ℝ) • a)) := by
    rw [hL0, sub_zero, ha] at hs
    exact hs.symm
  have hpw : P.proj w = w := by rw [hwc, P.fixed]
  rw [← hpw, hc, hc0]
  exact map_zero (D.localizers.embed 0)

end GluingData
end GlobalElliptic

end
end

end OAI
