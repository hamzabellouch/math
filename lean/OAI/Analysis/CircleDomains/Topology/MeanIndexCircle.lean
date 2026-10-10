import OAI.Analysis.CircleDomains.Selection.GeometricIndexPeriod
import OAI.Analysis.CircleDomains.Selection.LiftedMeanContinuity

namespace OAI

/-! The actual mean index descends through the logarithmic cover to a
circle-valued coordinate. Every continuous local lift represents the
same coordinate; no choice of branch is part of the resulting map. -/

open Set Function Filter MeasureTheory Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem diskRayProjection_eq_implies_translate
    (z w : ClosedUpperHalfPlane) (h : diskRayProjection z.val = diskRayProjection w.val) :
    ∃ n : ℤ, z = w.translate n := by
  have hi : z.val.im = w.val.im := by
    have hn := congrArg norm h
    rw [diskRayProjection_norm, diskRayProjection_norm] at hn
    have he := Real.exp_injective hn
    linarith
  have hr : (z.val.re : UnitAddCircle) = (w.val.re : UnitAddCircle) := by
    simpa only [diskRayProjection_argument] using congrArg normalizedArgument h
  obtain ⟨n, hn⟩ := (addCircle_eq_iff_exists_int 1 z.val.re w.val.re).mp hr
  refine ⟨n, Subtype.ext ?_⟩
  apply Complex.ext
  · simpa only [ClosedUpperHalfPlane.translate, Complex.add_re, Complex.intCast_re, mul_one] using hn
  · simpa only [ClosedUpperHalfPlane.translate, Complex.add_im, Complex.intCast_im, add_zero] using hi

 theorem meanGeometricIndex_mod_eq_of_projection_eq
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (z w : ClosedUpperHalfPlane)
    (h : diskRayProjection z.val = diskRayProjection w.val) :
    (meanGeometricIndex hsch K hKS η z : UnitAddCircle) =
      (meanGeometricIndex hsch K hKS η w : UnitAddCircle) := by
  obtain ⟨n, rfl⟩ := diskRayProjection_eq_implies_translate z w h
  apply (addCircle_eq_iff_exists_int 1 _ _).mpr
  exact ⟨n, by simpa only [mul_one] using meanGeometricIndex_translate hsch hsep K hK hKS η w n⟩

 def diskMeanCircle (hsch : PlanarSchoenflies)
    (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (w : ℂ) : UnitAddCircle :=
  if h : ∃ z : ClosedUpperHalfPlane, diskRayProjection z.val = w then
    (meanGeometricIndex hsch K hKS η (Classical.choose h) : UnitAddCircle) else 0

 theorem diskMeanCircle_projection
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (z : ClosedUpperHalfPlane) :
    diskMeanCircle hsch K hKS η (diskRayProjection z.val) =
      (meanGeometricIndex hsch K hKS η z : UnitAddCircle) := by
  have hex : ∃ w : ClosedUpperHalfPlane, diskRayProjection w.val = diskRayProjection z.val := ⟨z, rfl⟩
  rw [diskMeanCircle, dite_eq_left hex]
  exact meanGeometricIndex_mod_eq_of_projection_eq hsch hsep K hK hKS η
    (Classical.choose hex) z (Classical.choose_spec hex)

 theorem diskMeanCircle_eq_local_mean
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (Q Ψ : ℂ → ℂ) (z : ℂ)
    (hz : 0 ≤ (Ψ z).im) (hproj : diskRayProjection (Ψ z) = Q z) :
    diskMeanCircle hsch K hKS η (Q z) =
      (liftedMeanGeometricIndex hsch K hKS η Ψ z : UnitAddCircle) := by
  rw [liftedMeanGeometricIndex_eq hsch K hKS η Ψ z hz, ← hproj]
  exact diskMeanCircle_projection hsch hsep K hK hKS η ⟨Ψ z, hz⟩

 theorem continuousOn_diskMeanCircle_comp
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) {S : Set ℂ} (Q Ψ : ℂ → ℂ)
    (hΨ : ContinuousOn Ψ S) (hpos : ∀ z ∈ S, 0 ≤ (Ψ z).im)
    (hproj : ∀ z ∈ S, diskRayProjection (Ψ z) = Q z)
    (hmiss : ∀ z ∈ S, ∀ᵐ γ : K ∂(η : Measure K), Q z ∉ range γ.val) :
    ContinuousOn (diskMeanCircle hsch K hKS η ∘ Q) S := by
  have hm := continuousOn_liftedMeanGeometricIndex hsch hsep K hK hKS η Ψ hΨ hpos
    (fun z hz => by simpa only [hproj z hz] using hmiss z hz)
  have hc := (AddCircle.continuous_mk' (1 : ℝ)).comp_continuousOn hm
  apply hc.congr
  intro z hz
  exact diskMeanCircle_eq_local_mean hsch hsep K hK hKS η Q Ψ z (hpos z hz) (hproj z hz)

end CircleDomainRigidity

end

end OAI
