import Mathlib
import OAI.Analysis.AffineBernstein.AffineBoxArea
import OAI.Analysis.AffineBernstein.WeightedCapInverse
import OAI.Analysis.AffineBernstein.SmoothCapTest

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/-- The inward conormal of the actual affine-image graph, pulled back to its
original base. Its norm is NOT replaced by a vertical component. -/
def affineGraphConormal {n : ℕ} (u : Space n → ℝ)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (x : Space n) :
    (Space n × ℝ) →L[ℝ] ℝ :=
  ((ContinuousLinearMap.snd ℝ (Space n) ℝ) -
    (fderiv ℝ u x).comp (ContinuousLinearMap.fst ℝ (Space n) ℝ)).comp L.symm.toContinuousLinearMap

lemma affineGraphConormal_apply {n : ℕ} (u : Space n → ℝ)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (x : Space n) (z : Space n × ℝ) :
    affineGraphConormal u L x z = (L.symm z).2-fderiv ℝ u x (L.symm z).1 := rfl

lemma continuousAt_affineGraphConormal {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) :
    ContinuousAt (affineGraphConormal u L) x := by
  exact (continuousAt_const.sub
    (((hu.fderiv_right (m := ∞) (by simp)).continuousAt).clm_comp continuousAt_const)).clm_comp
      continuousAt_const

lemma affine_epigraph_support {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (hc : ConvexOn ℝ Ω u) {x : Space n} (hx : x ∈ Ω) (hd : DifferentiableAt ℝ u x)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
    {z : Space n × ℝ} (hz : z ∈ (fun p => L p+v) '' sourceEpigraph Ω u) :
    0 ≤ affineGraphConormal u L x (z-(L (x,u x)+v)) := by
  obtain ⟨p,hp,rfl⟩ := hz
  have hs := convex_fderiv_support hc hx hp.1 hd
  rw [show L p+v-(L (x,u x)+v) = L (p-(x,u x)) by simp only [map_sub]; abel,
    affineGraphConormal_apply,L.symm_apply_apply]
  change 0 ≤ p.2-u x-fderiv ℝ u x (p.1-x)
  have ht : u p.1 ≤ p.2 := hp.2
  linarith

/-- The actual inner ball produces the conormal-normalized radial support
bound required in the cap estimate. It is uniform under arbitrary affine maps. -/
lemma affine_inner_ball_radialSupport {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (hc : ConvexOn ℝ Ω u) {x : Space n} (hx : x ∈ Ω) (hd : DifferentiableAt ℝ u x)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
    (o : Space n) (c : ℝ) {r : ℝ} (hr : 0 < r)
    (hb : Metric.closedBall (L (o,c)+v) r ⊆ (fun p => L p+v) '' sourceEpigraph Ω u) :
    r*‖affineGraphConormal u L x‖ ≤ radialSupport u o c x := by
  have hh := ball_support_lower (affineGraphConormal u L x) (L (o,c)+v)
    (L (x,u x)+v) hr (fun z hz => affine_epigraph_support hc hx hd L v (hb hz))
  have he : affineGraphConormal u L x (L (o,c)+v-(L (x,u x)+v)) = radialSupport u o c x := by
    rw [show L (o,c)+v-(L (x,u x)+v) = L ((o,c)-(x,u x)) by simp only [map_sub]; abel,
      affineGraphConormal_apply,L.symm_apply_apply]
    change c-u x-fderiv ℝ u x (o-x) = c-u x+fderiv ℝ u x (x-o)
    rw [← neg_sub x o,map_neg,sub_neg_eq_add]
  rwa [he] at hh

/-- Uniform affine-image cap estimate, derived from the original PDE.
The scalar is the inverse second-form norm with the actual inward unit
conormal. The determinant on the left is the genuine affine-area covariance.
No transformed-PDE premise or conormal bound is assumed. -/
theorem affineMaximal_uniform_affine_cap_bound (n : ℕ)
    {ε r R : ℝ} (hε : 0 < ε) (hr : 0 < r) (hR : 0 ≤ R)
    (t₀ t₁ q₀ : ℝ) :
    ∃ C > 0, ∀ {Ω : Set (Space n)}, IsOpen Ω → Convex ℝ Ω →
      ∀ {u : Space n → ℝ}, ContDiffOn ℝ ∞ u Ω →
      (∀ x ∈ Ω, (hessian u x).PosDef) → AffineMaximalOn Ω u →
      ∀ (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
        (o : Space n) (c : ℝ) (a : Space n →L[ℝ] ℝ) (b d : ℝ),
      Metric.closedBall (L (o,c)+v) r ⊆ (fun p => L p+v) '' sourceEpigraph Ω u →
      a o+b*c+d = q₀ →
      ∀ {K Q : Set (Space n)}, IsCompact K → K ⊆ Ω → MeasurableSet Q → Q ⊆ K →
      (∀ x ∈ Ω, x ∉ K → t₁+ε ≤ graphAffineFunction u a b d x) →
      (∀ x ∈ K, graphAffineFunction u a b d x ∈ Icc t₀ (t₁+ε)) →
      (∀ x ∈ Q, graphAffineFunction u a b d x ≤ t₁-ε) →
      (∀ x ∈ K, ∀ j, |(L (x,u x)+v).1 j| ≤ R) →
      (∀ x ∈ K, |(L (x,u x)+v).2| ≤ R) →
      Real.rpow |L.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2)) *
        (∫ x in Q, affineAreaDensity u x *
          (‖affineGraphConormal u L x‖ * graphInverseMetric u a b d x)) ≤ C := by
  obtain ⟨C₁,hC₁pos,hC₁⟩ := smoothCapTest_lower_order_bound n ε t₁ t₀ q₀
  let B := (graphAreaBoxBound n (2*R)).toReal
  refine ⟨C₁*(B+1)/r,by dsimp [B]; positivity,?_⟩
  intro Ω hΩ hcv u hu hp hm L v o c a b d hball hq₀ K Q hK hKΩ hQ hQK hs hqK hqQ hxR htR
  have hcu := convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)
  have hZ (x) (hx : x ∈ Ω) : r*‖affineGraphConormal u L x‖ ≤ radialSupport u o c x :=
    affine_inner_ball_radialSupport hcu hx
      ((hu.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)) L v o c hr hball
  have hZ0 (x) (hx : x ∈ Ω) : 0 ≤ radialSupport u o c x :=
    (mul_nonneg hr.le (norm_nonneg _)).trans (hZ x hx)
  have hW : ContinuousOn (fun x => ‖affineGraphConormal u L x‖) K := fun x hx =>
    (continuousAt_affineGraphConormal (hu.contDiffAt (hΩ.mem_nhds (hKΩ hx))) L).norm.continuousWithinAt
  have hb := affineMaximal_graph_cap_weighted_inverse_bound hΩ hu hp hm o c a b d
    (smoothCapTest_smooth ε t₁) hK hKΩ hQ hQK
    (fun x hx hn => smoothCapTest_vanish hε (hs x hx hn))
    (fun x hx => hZ0 x (hKΩ hx))
    (fun x _ => smoothCapTest_second_nonneg ε t₁ (graphAffineFunction u a b d x))
    (fun x => ‖affineGraphConormal u L x‖) hW hr.le
    (fun x hx => hZ x (hKΩ (hQK hx)))
    (fun x hx => le_of_eq (smoothCapTest_second_one hε (hqQ x hx)).symm)
    (fun x hx => by rw [hq₀]; exact hC₁ _ (hqK x hx))
  let J := Real.rpow |L.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2))
  have hJ : 0 ≤ J := Real.rpow_nonneg (abs_nonneg _) _
  have harea := affine_image_graph_area_in_box hΩ hcv hK.measurableSet hKΩ hu hp L v hR hxR htR
  have hi := mul_le_mul_of_nonneg_left hb hJ
  have hi' : r*(J*(∫ x in Q, affineAreaDensity u x *
      (‖affineGraphConormal u L x‖*graphInverseMetric u a b d x))) ≤ C₁*(B+1) := by
    calc
      _ = J*(r*(∫ x in Q, affineAreaDensity u x *
          (‖affineGraphConormal u L x‖*graphInverseMetric u a b d x))) := by ring
      _ ≤ J*(C₁*∫ x in K, affineAreaDensity u x) := hi
      _ = C₁*(J*∫ x in K, affineAreaDensity u x) := by ring
      _ ≤ C₁*B := mul_le_mul_of_nonneg_left harea hC₁pos.le
      _ ≤ C₁*(B+1) := by nlinarith
  exact (le_div_iff₀ hr).mpr (by rwa [mul_comm] at hi')

end AffineBernstein
end

end OAI
