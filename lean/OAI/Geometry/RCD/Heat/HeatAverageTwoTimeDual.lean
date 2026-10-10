import OAI.Geometry.RCD.Heat.HeatExpansionCoarse

namespace OAI

/-! # Two-time heat transport duality on ball averages -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.heat_average_two_time_dual
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (hK : K ≤ 0) {dN : ℝ} (hNdim : (n:ℝ) ≤ dN)
    (f g : Lp ℝ 2 (hausdorff n X)) {φ ψ : X → ℝ}
    (hφ : Measurable φ) (hψ : Measurable ψ)
    (hf : φ =ᵐ[hausdorff n X] f) (hg : ψ =ᵐ[hausdorff n X] g)
    (M N : ℝ) (hM : ∀ x, |φ x| ≤ M) (hN : ∀ x, |ψ x| ≤ N)
    {c : ℝ} (hc0 : 0 ≤ c) (hd : ∀ x y, ψ x-φ y ≤ c*dist x y^2)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ x y : X, ∀ r : ℝ, 0 < r →
      (⨍z in closedBall x r, heatAt (hausdorff n X) hX.quadratic s g z ∂hausdorff n X) -
        (⨍z in closedBall y r, heatAt (hausdorff n X) hX.quadratic t f z ∂hausdorff n X) ≤
      c*Real.exp (-K*(s+t))*((dist x y+2*r)^2+2*dN*(Real.sqrt s-Real.sqrt t)^2) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  intro x y r hr
  let A := closedBall x r
  let B := closedBall y r
  have hA0 : μ A ≠ 0 := ne_of_gt ((hX.fullSupport x r hr).trans_le (measure_mono ball_subset_closedBall))
  have hB0 : μ B ≠ 0 := ne_of_gt ((hX.fullSupport y r hr).trans_le (measure_mono ball_subset_closedBall))
  have hAt : μ A ≠ ∞ := ne_of_lt (hX.finiteOnBounded A isBounded_closedBall)
  have hBt : μ B ≠ ∞ := ne_of_lt (hX.finiteOnBounded B isBounded_closedBall)
  let a := uniformDensityLp μ A measurableSet_closedBall hAt
  let b := uniformDensityLp μ B measurableSet_closedBall hBt
  have ha0 : 0 ≤ a := uniformDensityLp_nonneg μ A measurableSet_closedBall hAt
  have hb0 : 0 ≤ b := uniformDensityLp_nonneg μ B measurableSet_closedBall hBt
  have ham : ∫z, a z ∂μ = 1 := uniformDensityLp_integral μ A measurableSet_closedBall hAt hA0
  have hbm : ∫z, b z ∂μ = 1 := uniformDensityLp_integral μ B measurableSet_closedBall hBt hB0
  have has : ∀ᵐ z ∂μ, a z ≠ 0 → dist x z ≤ r := by
    filter_upwards [uniformDensityLp_ae μ A measurableSet_closedBall hAt] with z hz hne
    have hh : z ∈ A := by by_contra hh; exact hne (hz.trans (indicator_of_notMem hh _))
    simpa only [A,mem_closedBall,dist_comm] using hh
  have hbs : ∀ᵐ z ∂μ, b z ≠ 0 → dist x z ≤ dist x y+r := by
    filter_upwards [uniformDensityLp_ae μ B measurableSet_closedBall hBt] with z hz hne
    have hh : z ∈ B := by by_contra hh; exact hne (hz.trans (indicator_of_notMem hh _))
    have hh' : dist y z ≤ r := by simpa only [B,mem_closedBall,dist_comm] using hh
    exact (dist_triangle x y z).trans (add_le_add_right hh' _)
  let C : ℝ≥0 := ⟨max (μ A).toReal⁻¹ (μ B).toReal⁻¹,
    (inv_nonneg.mpr ENNReal.toReal_nonneg).trans (le_max_left _ _)⟩
  have haC : ∀ᵐ z ∂μ, a z ≤ C :=
    (uniformDensityLp_bound μ A measurableSet_closedBall hAt).mono fun z hz => hz.trans (le_max_left _ _)
  have hbC : ∀ᵐ z ∂μ, b z ≤ C :=
    (uniformDensityLp_bound μ B measurableSet_closedBall hBt).mono fun z hz => hz.trans (le_max_right _ _)
  let ν := heatMeasure μ hX.quadratic s a
  let σ := heatMeasure μ hX.quadratic t b
  obtain ⟨hνp,hνa,hνm,_⟩ := hX.heat_law K n hn x a ha0 ⟨r,has⟩ ham s hs.le
  obtain ⟨hσp,hσa,hσm,_⟩ := hX.heat_law K n hn x b hb0 ⟨dist x y+r,hbs⟩ hbm t ht.le
  let : IsProbabilityMeasure ν := hνp
  let : IsProbabilityMeasure σ := hσp
  obtain ⟨plan,_,_,hopt,_⟩ := hX.cd ν σ hνp hσp hνa hσa hνm hσm
  have hm := optimal_transport_quadratic_dual hνm hσm hopt hφ hψ M N hM hN hd
  have hc := hX.heat_two_time_expansion K n hn hK hNdim x a b C ha0 haC ham has hb0 hbC hbm hbs hs ht
  rw [uniformDensityLp_heat_zero μ hX.quadratic A measurableSet_closedBall hAt hA0,
    uniformDensityLp_heat_zero μ hX.quadratic B measurableSet_closedBall hBt hB0] at hc
  let : IsProbabilityMeasure (uniformOn μ A) := uniformOn_probability μ A hA0 hAt
  let : IsProbabilityMeasure (uniformOn μ B) := uniformOn_probability μ B hB0 hBt
  have hw := wassersteinSq_ball_bound x y hr.le
    (uniformOn_ae_mem μ A measurableSet_closedBall) (uniformOn_ae_mem μ B measurableSet_closedBall)
  have hh : (∫z, ψ z ∂ν)-(∫z, φ z ∂σ) ≤
      c*Real.exp (-K*(s+t))*((dist x y+2*r)^2+2*dN*(Real.sqrt s-Real.sqrt t)^2) := by
    calc _ ≤ c*(wassersteinSq ν σ).toReal := hm
      _ ≤ c*(Real.exp (-K*(s+t))*
          ((wassersteinSq (uniformOn μ A) (uniformOn μ B)).toReal+
            2*dN*(Real.sqrt s-Real.sqrt t)^2)) :=
        mul_le_mul_of_nonneg_left hc hc0
      _ ≤ c*(Real.exp (-K*(s+t))*
          ((dist x y+2*r)^2+2*dN*(Real.sqrt s-Real.sqrt t)^2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (add_le_add hw le_rfl) (Real.exp_pos _).le) hc0
      _ = _ := by ring
  rw [heat_uniformDensityLp_pair μ hX.quadratic A measurableSet_closedBall hAt g s hg,
    heat_uniformDensityLp_pair μ hX.quadratic B measurableSet_closedBall hBt f t hf] at hh
  exact hh

end RegularPointCoordinates

end OAI
