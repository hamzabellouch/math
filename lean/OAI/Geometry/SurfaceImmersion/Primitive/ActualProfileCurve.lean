import OAI.Geometry.SurfaceImmersion.Primitive.ActualProfileCrossing
import OAI.Geometry.SurfaceImmersion.Geometry.ActualCurveAvoidance

namespace OAI

/-! Nonvanishing and avoidance of the negative preferred normal for every
nonzero curve direction, transferred from the five leading profiles. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

theorem compact_actual_profile_curves (sLo K d : ℝ)
    (hsLo : 0 < sLo) (hK : 0 ≤ K) (hd : 0 ≤ d) :
    ∃ H : ℝ, 0 < H ∧ ∀ J : X → BoundaryProfile, Continuous J →
      (∀ x, J x ∈ regularBoundaryProfiles) →
      (∀ x, sLo ≤ profileCoefficients (J x) 0) →
      (∀ x, |profileCoefficients (J x) 1| ≤ d) →
      (∀ x, profileCoefficients (J x) 3 = 0 → H+2 < |profileCoefficients (J x) 2|) →
      ∃ η : ℝ, 0 < η ∧ ∀ z : ℝ, 0 < z → z < η → ∀ x : X,
      ∀ F : RField 4, ContDiff ℝ ∞ F → ∀ p : Base,
      ‖realBoundaryProfile F z p-J x‖ < η →
      -K ≤ coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p →
      ∀ b c : ℝ, (b ≠ 0 ∨ c ≠ 0) →
        realSecondForm F (b,c) (b,c) p ≠ 0 ∧
        normalize (realSecondForm F (b,c) (b,c) p) ≠
          -profilePreferred (realBoundaryProfile F z p) := by
  obtain ⟨H,hH,hcurve⟩ := compact_curve_avoidance (X := X)
    (sLo/2) K (d+1) (half_pos hsLo) hK (by linarith)
  refine ⟨H,hH,?_⟩
  intro J hJ hreg hlo hD hturn
  have hc : Continuous (fun x => profileCoefficients (J x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (contDiffAt_profileCoefficients (hreg x)).continuousAt.comp hJ.continuousAt
  let A : X → ℝ := fun x => profileCoefficients (J x) 3
  let N₀ : X → ℝ := fun x => profileCoefficients (J x) 2
  have hA : Continuous A := (continuous_apply 3).comp hc
  have hN₀ : Continuous N₀ := (continuous_apply 2).comp hc
  obtain ⟨η₀,hη₀,hpreserve⟩ := hcurve univ isCompact_univ A N₀ hA hN₀
    (fun x _ hx => hturn x hx)
  let ε := min 1 (min (sLo/2) η₀)
  have hε : 0 < ε := lt_min zero_lt_one (lt_min (half_pos hsLo) hη₀)
  obtain ⟨δ,hδ,hprofile⟩ := compact_boundary_profile_stability
    (isCompact_univ.image hJ) (by rintro _ ⟨x,_,rfl⟩; exact hreg x) ε hε
  refine ⟨min δ η₀,lt_min hδ hη₀,?_⟩
  intro z hz hzη x F hF p herror hcurv b c hbc
  obtain ⟨hactual,hnear⟩ := hprofile (J x) (mem_image_of_mem J (mem_univ x))
    (realBoundaryProfile F z p) (herror.trans_le (min_le_left _ _))
  obtain ⟨f,hn,hm,hcoef⟩ := exists_profile_secondFormFrame hF z p hactual
  have hdiff (j : Fin 4) :
      |(![f.S,f.D,f.N,z*f.L] j)-profileCoefficients (J x) j| < ε := by
    rw [← hcoef]
    exact (profileCoefficient_sub_le _ _ j).trans_lt hnear
  have hS : |f.S-profileCoefficients (J x) 0| < ε := by simpa using hdiff 0
  have hD' : |f.D-profileCoefficients (J x) 1| < ε := by simpa using hdiff 1
  have hN : |f.N-N₀ x| < η₀ := by
    exact (show |f.N-N₀ x| < ε by simpa [N₀] using hdiff 2).trans_le
      ((min_le_right 1 _).trans (min_le_right _ _))
  have hL : |z*f.L-A x| < η₀ := by
    exact (show |z*f.L-A x| < ε by simpa [A] using hdiff 3).trans_le
      ((min_le_right 1 _).trans (min_le_right _ _))
  have hεone : ε ≤ 1 := min_le_left _ _
  have hεS : ε ≤ sLo/2 := (min_le_right 1 _).trans (min_le_left _ _)
  have hsmin : sLo/2 ≤ f.S := by
    have hh := (abs_lt.mp hS).1
    linarith [hlo x]
  have hdbound : |f.D| ≤ d+1 := by
    have hh := abs_sub_le f.D (profileCoefficients (J x) 1) 0
    simp only [sub_zero] at hh
    linarith [hD x]
  have hh := hpreserve z hz (hzη.trans_le (min_le_right _ _)) x (mem_univ x)
    f.S f.D f.N f.L _ b c hsmin hcurv hdbound hbc hN hL
  simpa only [hn] using f.actual_curve_avoidance hF b c hh

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
