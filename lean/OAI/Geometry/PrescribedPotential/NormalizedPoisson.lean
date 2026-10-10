import Mathlib
import OAI.Geometry.PrescribedPotential.CompactAlternative
import OAI.Geometry.PrescribedPotential.ComplexKernel
import OAI.Geometry.PrescribedPotential.PatchCutoffs
import OAI.Geometry.PrescribedPotential.FredholmKernel
import OAI.Geometry.PrescribedPotential.GlobalRellich

namespace OAI

/-! Normalized Poisson. -/

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

omit [ConnectedSpace X] in
lemma resolventZero_compact (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1) :
    IsCompactOperator (D.resolventZero m hm he) :=
  D.lower_compact.comp_clm (D.completedResolvent m hm he)

omit [ConnectedSpace X] in
lemma fredholmOperator_compact (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) : IsCompactOperator (D.fredholmOperator m hm he P) :=
  ((D.resolventZero_compact m hm he).smul (m^2 : ℝ)).sub P.compact

lemma fredholm_surjective (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) :
    Function.Surjective (1 - D.fredholmOperator m hm he P :
      D.localizers.Sobolev 0 →L[ℝ] D.localizers.Sobolev 0) :=
  compact_one_sub_surjective _ (D.fredholmOperator_compact m hm he P) (D.fredholm_kernel m hm he P)

include D in
theorem exists_complex_poisson (F : Smooth A) :
    ∃ (u : Smooth A) (c : ℂ), complexL g u = F + Smooth.const c := by
  obtain ⟨m, hm, he⟩ := D.exists_completedError_small
  obtain ⟨P⟩ := D.localizers.constantProjection_exists
  obtain ⟨w, hw⟩ := D.fredholm_surjective m hm he P (-D.localizers.embed 0 F)
  obtain ⟨c, hc⟩ := P.value w
  have hw' : w = D.localizers.embed 0 (-F - Smooth.const c) +
      (m^2 : ℝ) • D.resolventZero m hm he w := by
    change w - ((m^2 : ℝ) • D.resolventZero m hm he w - P.proj w) = -D.localizers.embed 0 F at hw
    calc
      w = -D.localizers.embed 0 F +
          ((m^2 : ℝ) • D.resolventZero m hm he w - P.proj w) := sub_eq_iff_eq_add.mp hw
      _ = _ := by rw [hc, map_sub, map_neg]; abel
  obtain ⟨u, hu⟩ := D.allRegular_smooth (D.resolvent_feedback_regular m hm he w _ hw')
  refine ⟨u, c, ?_⟩
  have hs := (D.smooth_shifted_equation m hm he w u hu).trans hw'
  rw [← hu, ← map_smul, ← map_add] at hs
  have heq := D.localizers.embed_injective 0 hs
  apply sub_right_inj.mp
  calc
    (m^2 : ℝ) • u - complexL g u = -F - Smooth.const c + (m^2 : ℝ) • u := heq
    _ = (m^2 : ℝ) • u - (F + Smooth.const c) := by abel

end GluingData
end GlobalElliptic

namespace Anticanonical.SourceSmooth
open GlobalElliptic
variable (d : ℕ) (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] (A : ComplexAtlas d X)

 

theorem normalizedPoisson (g : KaehlerMetric A) (x₀ : X) (f : SmoothRealFunction A) :
    HasNormalizedPoissonSolution g x₀ f := by
  obtain ⟨S, ⟨D⟩⟩ := exists_gluingData g
  obtain ⟨u, c, hu⟩ := D.exists_complex_poisson (Smooth.ofReal f)
  refine ⟨(u.part Complex.reCLM).normalizeAt x₀, -c.re, SmoothRealFunction.normalizeAt_value _ _, ?_⟩
  intro i z hz
  rw [KaehlerMetric.linearizedMongeAmpere_normalizeAt,
    ← g.laplacian_localExpression _ i hz]
  change (g.laplacian (u.part Complex.reCLM)).value ((A.chart i).symm z) + -c.re = _
  rw [← complexL_re, hu, Smooth.add_apply, Complex.add_re, Smooth.ofReal_apply, Complex.ofReal_re]
  change f.localExpression i z + c.re + -c.re = f.localExpression i z
  ring

end Anticanonical.SourceSmooth

end
end

end OAI
