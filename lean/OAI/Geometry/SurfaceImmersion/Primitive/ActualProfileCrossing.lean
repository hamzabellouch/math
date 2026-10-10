import OAI.Geometry.SurfaceImmersion.Primitive.BoundaryProfileFrame
import OAI.Geometry.SurfaceImmersion.Primitive.ActualCrossingInvariant
import OAI.Geometry.SurfaceImmersion.Primitive.CompactCrossingPreservation

namespace OAI

/-! Transfer the compact turn/nonturn argument all the way to the two
ordered crossing invariants of an actual smooth surface. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

lemma profileCoefficient_sub_le (H J : BoundaryProfile) (i : Fin 4) :
    |profileCoefficients H i-profileCoefficients J i| ≤
      ‖profileGeometry H-profileGeometry J‖ := by
  have h := (norm_le_pi_norm ((profileGeometry H-profileGeometry J).2) i).trans
    (norm_snd_le (profileGeometry H-profileGeometry J))
  simpa only [profileGeometry,Prod.snd_sub,Pi.sub_apply,Real.norm_eq_abs] using h

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- The turn threshold is chosen from the fixed metric and slope bounds,
before the loop and its mixed/longitudinal derivatives are supplied. -/
theorem compact_actual_profile_crossings (sLo sHi K d T : ℝ)
    (hsLo : 0 < sLo) (hsHi : 0 < sHi) (hK : 0 ≤ K) (hd : 0 ≤ d) (hT : 0 ≤ T) :
    ∃ H : ℝ, 0 < H ∧ ∀ J : X → BoundaryProfile, Continuous J →
      (∀ x, J x ∈ regularBoundaryProfiles) →
      (∀ x, sLo ≤ profileCoefficients (J x) 0) →
      (∀ x, profileCoefficients (J x) 0 ≤ sHi) →
      (∀ x, |profileCoefficients (J x) 1| ≤ d) →
      (∀ x, profileCoefficients (J x) 3 = 0 → H+2 < |profileCoefficients (J x) 2|) →
      ∃ η : ℝ, 0 < η ∧ ∀ z : ℝ, 0 < z → z < η → ∀ x : X,
      ∀ F : RField 4, ContDiff ℝ ∞ F → ∀ p : Base,
      ‖realBoundaryProfile F z p-J x‖ < η →
      ∀ κ : ℝ,
      coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p =
        κ*gramDet (coordDeriv dx F p) (coordDeriv dy F p) →
      -K ≤ coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p →
      ∀ t u : ℝ, |t| ≤ T → |u| ≤ T →
        0 < orderedCrossing F (1,t) (1,u) p κ ∧
        0 < orderedCrossing F (1,u) (1,t) p κ := by
  obtain ⟨H,hH,hcross⟩ := compact_crossing_preservation (E := Space) (X := X)
    (sLo/2) (sHi+1) K (d+1) T (half_pos hsLo) (by linarith) hK (by linarith) hT
  refine ⟨H,hH,?_⟩
  intro J hJ hreg hlo hhi hD hturn
  have hc : Continuous (fun x => profileCoefficients (J x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (contDiffAt_profileCoefficients (hreg x)).continuousAt.comp hJ.continuousAt
  let A : X → ℝ := fun x => profileCoefficients (J x) 3
  let N₀ : X → ℝ := fun x => profileCoefficients (J x) 2
  have hA : Continuous A := (continuous_apply 3).comp hc
  have hN₀ : Continuous N₀ := (continuous_apply 2).comp hc
  obtain ⟨η₀,hη₀,hpreserve⟩ := hcross univ isCompact_univ A N₀ hA hN₀
    (fun x _ hx => hturn x hx)
  let ε := min 1 (min (sLo/2) η₀)
  have hε : 0 < ε := lt_min zero_lt_one (lt_min (half_pos hsLo) hη₀)
  obtain ⟨δ,hδ,hprofile⟩ := compact_boundary_profile_stability
    (isCompact_univ.image hJ) (by rintro _ ⟨x,_,rfl⟩; exact hreg x) ε hε
  refine ⟨min δ η₀,lt_min hδ hη₀,?_⟩
  intro z hz hzη x F hF p herror κ hk hcurv t u ht hu
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
  have hsmax : f.S ≤ sHi+1 := by
    have hh := (abs_lt.mp hS).2
    linarith [hhi x]
  have hdbound : |f.D| ≤ d+1 := by
    have hh := abs_sub_le f.D (profileCoefficients (J x) 1) 0
    simp only [sub_zero] at hh
    linarith [hD x]
  have hmn : inner ℝ (spaceCoordinates.symm f.m) (spaceCoordinates.symm f.n) = 0 := by
    rw [spaceCoordinates_symm_inner,dotProduct_comm]
    exact f.orthogonal
  have hh := hpreserve z hz (hzη.trans_le (min_le_right _ _)) x (mem_univ x)
    (spaceCoordinates.symm f.n) (spaceCoordinates.symm f.m)
    (spaceCoordinates_norm_unit f.unit_n) (spaceCoordinates_norm_unit f.unit_m) hmn
    f.S f.D f.N f.L _ t u hsmin hsmax hcurv hdbound ht hu hN hL
  rw [f.orderedCrossing_eq hF κ t u hk,f.orderedCrossing_eq hF κ u t hk]
  exact hh

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
