import OAI.Geometry.NodalSets.Charts.FiniteChartDerivativeSize
import OAI.Geometry.NodalSets.Coefficients.FiniteSphereCoefficientAtlas
import OAI.Geometry.NodalSets.Coefficients.SupportedCoefficientChartBounds

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Metric
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst3 intrinsicRoundPerturbationLocalInst4 intrinsicRoundPerturbationLocalInst5 intrinsicRoundPerturbationLocalInst6 intrinsicRoundPerturbationLocalInst7 intrinsicRoundPerturbationLocalInst8 intrinsicRoundPerturbationLocalInst9 intrinsicRoundPerturbationLocalInst10 intrinsicRoundPerturbationLocalInst11 intrinsicRoundPerturbationLocalInst12 intrinsicRoundPerturbationLocalInst13 intrinsicRoundPerturbationLocalInst14 intrinsicRoundPerturbationLocalInst15 intrinsicRoundPerturbationLocalInst16 intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

def sphereAtlasCore : Set BaseModel := seedCoordEquiv '' closedBall (0 : Yau.Jets.Coord) 1

lemma sphereAtlasCore_compact : IsCompact sphereAtlasCore :=
  (isCompact_closedBall _ _).image seedCoordEquiv.continuous

theorem finite_sphere_coefficient_atlas :
    ∃ P : Finset Base, ∀ x : Base, ∃ p ∈ P, ∃ z ∈ interior sphereAtlasCore,
      (extChartAt (𝓡 4) p).symm z = x := by
  obtain ⟨P,hP⟩ := finite_sphere_coordinate_cover
  refine ⟨P,?_⟩
  intro x
  obtain ⟨p,hp,z,hz,hzx⟩ := hP x
  refine ⟨p,hp,seedCoordEquiv z,?_,hzx⟩
  apply mem_interior_iff_mem_nhds.mpr
  exact Filter.mem_of_superset ((seedCoordEquiv.isOpenMap _ isOpen_ball).mem_nhds ⟨z,hz,rfl⟩)
    (image_mono ball_subset_closedBall)

def sphereCoefficientDistance (P : Finset Base) (J : ℕ)
    (A : IntrinsicTensor) (rho : Base → ℝ) (B : IntrinsicTensor) (sigma : Base → ℝ) : ℝ :=
  finiteChartDerivativeSize P sphereAtlasCore J (fun p z ↦
    intrinsicChartCoefficient B sigma p z-intrinsicChartCoefficient A rho p z)

theorem supported_finite_atlas_coefficient_bound (r : ℝ) (P : Finset Base) (J : ℕ) :
    ∃ C > 0, ∀ (A : IntrinsicTensor) (rho a b : Base → ℝ),
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a → ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b →
      tsupport a ⊆ seedSpherePatch r → tsupport b ⊆ seedSpherePatch r →
      ∀ eps : ℝ, 0 ≤ eps →
      (∀ x i, i ≤ J → ‖iteratedFDeriv ℝ i (fun y ↦ a (seedSphereFromCoord y)) x‖ ≤ eps) →
      (∀ x i, i ≤ J → ‖iteratedFDeriv ℝ i (fun y ↦ b (seedSphereFromCoord y)) x‖ ≤ eps) →
      sphereCoefficientDistance P J A rho (fun x ↦ A x+roundTensorPerturbation a x)
        (fun x ↦ rho x+b x) ≤ C*eps := by
  classical
  have hex (p : P) := supported_sphere_coefficient_bound r p sphereAtlasCore_compact J
  choose c hc hbound using hex
  let C : ℝ := 1+∑ p : P, c p
  have hsum : 0 ≤ ∑ p : P, c p := Finset.sum_nonneg (fun p _ ↦ (hc p).le)
  have hC : 0 < C := by change 0 < 1+∑ p : P, c p; linarith
  refine ⟨C,hC,?_⟩
  intro A rho a b ha hb has hbs eps heps hab hbb
  apply finiteChartDerivativeSize_le _ _ _ _ (mul_nonneg hC.le heps)
  intro p hp i hi z hz
  let q : P := ⟨p,hp⟩
  have hcC : c q ≤ C := by
    have := Finset.single_le_sum (fun p _ ↦ (hc p).le) (Finset.mem_univ q)
    change c q ≤ 1+∑ p : P, c p
    linarith
  exact (hbound q A rho a b ha hb has hbs eps heps hab hbb z hz i hi).trans
    (mul_le_mul_of_nonneg_right hcC heps)

end
end Yau.Target

end OAI
