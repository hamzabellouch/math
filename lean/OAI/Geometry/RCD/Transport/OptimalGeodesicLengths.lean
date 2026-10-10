import OAI.Geometry.RCD.Transport.RenyiMidpointCompression

namespace OAI

/-! # Length localization of optimal geodesics

Two contacting quadratic-cost geodesics which meet at an interior time
have the same total length. A bounded RCD optimal plan therefore has a
compact full-measure set on which length is constant on every interior
evaluation fiber. This is the localization in Rajala, arXiv:1202.6514,
Lemma 2.6.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem equal_lengths_of_cross_cost {a b c d t : ℝ}
    (_ha : 0 ≤ a) (_hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ht0 : 0 < t) (ht1 : t < 1)
    (hcost : a^2+b^2 ≤ c^2+d^2)
    (hcross0 : c ≤ t*a+(1-t)*b) (hcross1 : d ≤ t*b+(1-t)*a) : a=b := by
  have h0 := pow_le_pow_left₀ hc hcross0 2
  have h1 := pow_le_pow_left₀ hd hcross1 2
  have he : (t*a+(1-t)*b)^2+(t*b+(1-t)*a)^2-(a^2+b^2) =
      -(2*t*(1-t)*(a-b)^2) := by ring
  have hz : 2*t*(1-t)*(a-b)^2 ≤ 0 := by linarith
  have hp : 0 < 2*t*(1-t) := by positivity
  have hs : (a-b)^2 ≤ 0 := le_of_not_gt fun hs => (not_lt_of_ge hz) (mul_pos hp hs)
  nlinarith [sq_nonneg (a-b)]

theorem contacting_geodesics_equal_length {φ ψ : X → ℝ}
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    {γ ζ : C(Time,X)} (hg : IsGeodesic γ) (hz : IsGeodesic ζ)
    (hγ : φ (γ 0)+ψ (γ 1)=dist (γ 0) (γ 1)^2/2)
    (hζ : φ (ζ 0)+ψ (ζ 1)=dist (ζ 0) (ζ 1)^2/2)
    {t : Time} (ht0 : 0 < (t:ℝ)) (ht1 : (t:ℝ) < 1) (hmeet : γ t=ζ t) :
    dist (γ 0) (γ 1)=dist (ζ 0) (ζ 1) := by
  have hcross0 : dist (γ 0) (ζ 1) ≤ (t:ℝ)*dist (γ 0) (γ 1)+(1-(t:ℝ))*dist (ζ 0) (ζ 1) := by
    calc
      _ ≤ dist (γ 0) (γ t)+dist (γ t) (ζ 1) := dist_triangle _ _ _
      _ = _ := by
        rw [hg 0 t,hmeet,hz t 1]
        change |(0:ℝ)-(t:ℝ)| *dist (γ 0) (γ 1)+|(t:ℝ)-1| *dist (ζ 0) (ζ 1) = _
        rw [zero_sub,abs_neg,abs_of_pos ht0]
        rw [abs_of_nonpos (by linarith : (t:ℝ)-1 ≤ 0)]
        ring
  have hcross1 : dist (ζ 0) (γ 1) ≤ (t:ℝ)*dist (ζ 0) (ζ 1)+(1-(t:ℝ))*dist (γ 0) (γ 1) := by
    calc
      _ ≤ dist (ζ 0) (ζ t)+dist (ζ t) (γ 1) := dist_triangle _ _ _
      _ = _ := by
        rw [hz 0 t,←hmeet,hg t 1]
        change |(0:ℝ)-(t:ℝ)| *dist (ζ 0) (ζ 1)+|(t:ℝ)-1| *dist (γ 0) (γ 1) = _
        rw [zero_sub,abs_neg,abs_of_pos ht0]
        rw [abs_of_nonpos (by linarith : (t:ℝ)-1 ≤ 0)]
        ring
  have hcost : dist (γ 0) (γ 1)^2+dist (ζ 0) (ζ 1)^2 ≤
      dist (γ 0) (ζ 1)^2+dist (ζ 0) (γ 1)^2 := by
    linarith [had (γ 0) (ζ 1),had (ζ 0) (γ 1)]
  exact equal_lengths_of_cross_cost dist_nonneg dist_nonneg dist_nonneg dist_nonneg
    ht0 ht1 hcost hcross0 hcross1

variable [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.optimal_length_fibers
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (hac : ν₀ ≪ hausdorff n X) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (π : Measure C(Time,X)) (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1)))) :
    ∃ E : Set C(Time,X), IsCompact E ∧ (∀ᵐ γ ∂π, γ∈E) ∧
      ∀ γ∈E, ∀ ζ∈E, ∀ t : Time, 0 < (t:ℝ) → (t:ℝ) < 1 → γ t=ζ t →
        dist (γ 0) (γ 1)=dist (ζ 0) (ζ 1) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  obtain ⟨u,φ,ψ,L,hφ,hψ,_,_,_,had,hcontact,_⟩ := hp.bounded_sobolev_potential
    (hausdorff n X) hX.quadratic hX.geodesic ν₀ ν₁ hac p hR hs0 hs1
  let G := {γ : C(Time,X) | IsGeodesic γ ∧ ∀ t, dist (γ t) p ≤ 3*R}
  let F := {γ : C(Time,X) | φ (γ 0)+ψ (γ 1)=dist (γ 0) (γ 1)^2/2}
  have hG : IsCompact G := isCompact_bounded_geodesics p (by positivity)
  have hF : IsClosed F := isClosed_eq
    ((hφ.continuous.comp (continuous_eval_const 0)).add
      (hψ.continuous.comp (continuous_eval_const 1)))
    ((((continuous_eval_const 0).dist (continuous_eval_const 1)).pow 2).div_const 2)
  have hcae : ∀ᵐ γ ∂π, γ∈F := ae_of_ae_map
    ((measurable_path_eval 0).prodMk (measurable_path_eval 1)).aemeasurable hcontact
  refine ⟨G∩F,hG.inter_right hF,?_,?_⟩
  · exact (optimal_geodesic_plan_bounded ν₀ ν₁ π hg hp p hR hs0 hs1).and hcae
  · intro γ hγ ζ hζ t ht0 ht1 hm
    exact contacting_geodesics_equal_length had hγ.1.1 hζ.1.1 hγ.2 hζ.2 ht0 ht1 hm

end RegularPointCoordinates

end

end OAI
