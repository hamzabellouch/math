import OAI.Analysis.CircleDomains.Transfer.LogarithmicCutCharts
import OAI.Analysis.CircleDomains.Selection.LiftedMeanBands
import OAI.Analysis.CircleDomains.Selection.GeometricIndexPeriod
import OAI.Analysis.CircleDomains.Selection.LocalBandTransitions

namespace OAI

/-! The actual mean branches have integer transitions before and after
adding a common smoothing correction. Thus their interval bands glue. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem mean_logarithmic_branches_eventually_add_int
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) {X : Type*} [TopologicalSpace X]
    (Q : X → ℂ) (a b : ℝ) (x : X)
    (ha : ContinuousAt (fun y => logarithmicCutChart a (Q y)) x)
    (hb : ContinuousAt (fun y => logarithmicCutChart b (Q y)) x) :
    ∃ k : ℤ, ∀ᶠ y in 𝓝 x,
      meanGeometricIndex hsch K hKS η (upperHalfPlaneClamp (logarithmicCutChart b (Q y))) =
      meanGeometricIndex hsch K hKS η (upperHalfPlaneClamp (logarithmicCutChart a (Q y))) + k := by
  have hquot (c : ℝ) (y : X) :
      ((logarithmicCutChart c (Q y)).re : UnitAddCircle) = normalizedArgument (Q y) := by
    simp only [logarithmicCutChart, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero, AddCircle.coe_equivIco]
  obtain ⟨k, hk⟩ := FiniteTransfer.eventually_lifts_differ_by_integer
    (Complex.continuous_re.continuousAt.comp hb) (Complex.continuous_re.continuousAt.comp ha)
    (Eventually.of_forall (fun y => (hquot b y).trans (hquot a y).symm))
  refine ⟨k, hk.mono fun y hy => ?_⟩
  have he : upperHalfPlaneClamp (logarithmicCutChart b (Q y)) =
      (upperHalfPlaneClamp (logarithmicCutChart a (Q y))).translate k := by
    apply Subtype.ext
    apply Complex.ext
    · simpa only [upperHalfPlaneClamp, ClosedUpperHalfPlane.translate,
        Complex.add_re, Complex.intCast_re, Function.comp_apply] using hy
    · simp [upperHalfPlaneClamp, ClosedUpperHalfPlane.translate, logarithmicCutChart]
  rw [he, meanGeometricIndex_translate hsch hsep K hK hKS η]

 theorem perturbed_mean_branches_eventually_add_int
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) {X : Type*} [TopologicalSpace X]
    (Q : X → ℂ) (a b : ℝ) (x : X)
    (ha : ContinuousAt (fun y => logarithmicCutChart a (Q y)) x)
    (hb : ContinuousAt (fun y => logarithmicCutChart b (Q y)) x)
    (r u v : X → ℝ)
    (hu : u =ᶠ[𝓝 x] fun y =>
      meanGeometricIndex hsch K hKS η (upperHalfPlaneClamp (logarithmicCutChart a (Q y))) + r y)
    (hv : v =ᶠ[𝓝 x] fun y =>
      meanGeometricIndex hsch K hKS η (upperHalfPlaneClamp (logarithmicCutChart b (Q y))) + r y) :
    ∃ k : ℤ, v =ᶠ[𝓝 x] fun y => u y + k := by
  obtain ⟨k, hk⟩ := mean_logarithmic_branches_eventually_add_int hsch hsep K hK hKS η Q a b x ha hb
  refine ⟨k, ?_⟩
  filter_upwards [hk, hu, hv] with y hy huy hvy
  rw [huy, hvy, hy]
  ring

end CircleDomainRigidity

end

end OAI
