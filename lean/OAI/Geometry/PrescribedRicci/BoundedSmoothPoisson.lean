import Mathlib
import OAI.Geometry.PrescribedPotential.BoundedPoisson
import OAI.Geometry.PrescribedPotential.ComplexOperator
import OAI.Geometry.PrescribedPotential.PatchCutoffs

namespace OAI

/-! Bounded Smooth Poisson. -/

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

theorem exists_complex_poisson_bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Smooth A,
    ∃ (u : Smooth A) (c : ℂ), complexL g u = F + Smooth.const c ∧
      ‖D.localizers.embed 0 u‖ ≤ C * ‖D.localizers.embed 0 F‖ := by
  obtain ⟨m, hm, he⟩ := D.exists_completedError_small
  obtain ⟨P⟩ := D.localizers.constantProjection_exists
  let T := D.resolventZero m hm he ∘L D.poissonInput m hm he P
  refine ⟨‖T‖, norm_nonneg T, fun F => ?_⟩
  let w := D.poissonInput m hm he P (D.localizers.embed 0 F)
  have hT := T.le_opNorm (D.localizers.embed 0 F)
  let c := D.poissonResidue m hm he P (D.localizers.embed 0 F)
  have hc : P.proj w = D.localizers.embed 0 (Smooth.const c) :=
    (P.coefficient_spec w).symm
  have hw : w = D.localizers.embed 0 (-F - Smooth.const c) +
      (m^2 : ℝ) • D.resolventZero m hm he w := by
    have hh := D.poissonInput_equation m hm he P (D.localizers.embed 0 F)
    change w = -D.localizers.embed 0 F - P.proj w + _ at hh
    rw [hc] at hh
    simpa only [map_sub, map_neg] using hh
  obtain ⟨u, hu⟩ := D.allRegular_smooth (D.resolvent_feedback_regular m hm he w _ hw)
  refine ⟨u, c, ?_, ?_⟩
  · have hs := (D.smooth_shifted_equation m hm he w u hu).trans hw
    rw [← hu, ← map_smul, ← map_add] at hs
    have hh := D.localizers.embed_injective 0 hs
    apply sub_right_inj.mp
    calc
      (m^2 : ℝ) • u - complexL g u = -F - Smooth.const c + (m^2 : ℝ) • u := hh
      _ = (m^2 : ℝ) • u - (F + Smooth.const c) := by abel
  · rw [hu]
    simpa only [T, ContinuousLinearMap.comp_apply, w] using hT

end GluingData
end GlobalElliptic

end
end

end OAI
