import OAI.Geometry.NodalSets.Charts.SphereChartEnergyBounds
import OAI.Geometry.NodalSets.Charts.SphereEnergyCompletion
import OAI.Geometry.NodalSets.Elliptic.RealFinitePositiveBounds
import OAI.Geometry.NodalSets.Elliptic.RealPartialJetLinearity

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Analysis MeasureTheory Metric Set
open scoped ContDiff
noncomputable section
local instance sphereEnergyUpperMeasurable : MeasurableSpace Base := borel Base
local instance sphereEnergyUpperBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_finite_chart_energy_upper (d : SphereEnergyData) (P : Finset Base) (r : ℝ)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ ball (0 : Yau.Jets.Coord) r, sphereChartCoordMap p z=x) :
    ∃ K > 0, ∀ (u : SphereEnergySmooth d) (eps : ℝ), 0 ≤ eps →
      (∀ x : Base, |(SphereEnergySmooth.toSmooth d u : Base → ℝ) x| ≤ eps) →
      (∀ p ∈ P, ∀ x ∈ ball (0 : Yau.Jets.Coord) r, ∀ i : Fin 4,
        |partialJet ((SphereEnergySmooth.toSmooth d u : Base → ℝ) ∘ sphereChartCoordMap p) [i] x| ≤ eps) →
      ‖u‖^2 ≤ K*eps^2 := by
  choose c hc C hC hCb using (fun p : P ↦ intrinsic_real_uniform_ellipticity
    d.tensor d.smooth d.symm d.pos p (isCompact_closedBall (0 : Yau.Jets.Coord) r))
  obtain ⟨B,hB,hBC⟩ := Yau.real_finite_positive_majorant C
  obtain ⟨R,hR,hRb⟩ := (isCompact_univ.image d.continuous).isBounded.exists_pos_norm_le
  let I := ∫ _x : Base, (1 : ℝ) ∂sphereReferenceMeasure
  have hI : 0 ≤ I := integral_nonneg (fun _ ↦ zero_le_one)
  let K := (R+4*B)*I+1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro u eps heps hu hdu
  let f : Base → ℝ := SphereEnergySmooth.toSmooth d u
  have hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f := (SphereEnergySmooth.toSmooth d u).property
  have hm (x : Base) : d.density x*f x*f x ≤ R*eps^2 := by
    have hx : d.density x ≤ R := (le_abs_self _).trans (hRb _ ⟨x,mem_univ x,rfl⟩)
    have hf2 : f x^2 ≤ eps^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) heps).mpr (hu x)
    nlinarith [mul_le_mul hx hf2 (sq_nonneg (f x)) hR.le]
  have he (x : Base) : d.tensor x (sphereDifferential f x) (sphereDifferential f x) ≤ 4*B*eps^2 := by
    obtain ⟨p,hp,z,hz,rfl⟩ := hcover x
    rw [intrinsic_differential_pair_chart d.tensor f f hf hf]
    have hs : (∑ i : Fin 4, (Yau.coordPartial (f ∘ sphereChartCoordMap p) z i)^2) ≤ 4*eps^2 := by
      calc
        _ ≤ ∑ _i : Fin 4, eps^2 := Finset.sum_le_sum (fun i _ ↦ by
          simpa only [sq_abs,partialJet,Yau.coordPartial,f] using (sq_le_sq₀ (abs_nonneg _) heps).mpr (hdu p hp z hz i))
        _ = _ := by simp
    have hb := (hCb ⟨p,hp⟩ z (ball_subset_closedBall hz) (fun i ↦ Yau.coordPartial (f ∘ sphereChartCoordMap p) z i)).2
    exact hb.trans ((mul_le_mul (hBC ⟨p,hp⟩) hs
      (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)) hB.le).trans_eq (by ring))
  have hiM := sphereWeightedPairing_integrable d.density f f d.continuous hf.continuous hf.continuous
  have hiE := intrinsic_differential_pair_integrable d.tensor d.smooth d.symm d.pos f f hf hf
  let := sphereReferenceMeasure_finite
  calc
    ‖u‖^2 = ∫ x, d.density x*f x*f x+d.tensor x (sphereDifferential f x) (sphereDifferential f x)
        ∂sphereReferenceMeasure := by
      rw [SphereEnergySmooth.norm_sq,sphereWeightedPairing,sphereDirichletForm,integral_add hiM hiE]
    _ ≤ ∫ _x : Base, ((R+4*B)*eps^2)*1 ∂sphereReferenceMeasure := by
      apply integral_mono (hiM.add hiE) (integrable_const _)
      intro x
      change d.density x*f x*f x+d.tensor x (sphereDifferential f x) (sphereDifferential f x) ≤ (R+4*B)*eps^2*1
      nlinarith [hm x,he x]
    _ = ((R+4*B)*eps^2)*I := by rw [integral_const_mul]
    _ ≤ K*eps^2 := by dsimp [K]; nlinarith [sq_nonneg eps]

end
end Yau.Target

end OAI
