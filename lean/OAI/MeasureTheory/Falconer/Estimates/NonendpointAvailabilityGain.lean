import OAI.MeasureTheory.Falconer.Recursion.NonendpointScaleWindow
import OAI.MeasureTheory.Falconer.Radial.RadialWindowAvailability

namespace OAI

/-! # Strict improvement of the actual available radial exponent -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem CapAvailable.nonendpoint_improve (hpublished : PublishedPlanarFurstenberg)
    {h : ℕ} {α t q C D s : ℝ}
    (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2) (hqt : q < t)
    (ht : t-(h:ℝ) < 1) (htα : t < α) (hC : 0 ≤ C)
    (Q : DyadicCube (h+2)) (hQ : Q.side = 1)
    (hD : 1 ≤ D) (hDdim : Real.sqrt (h+2:ℕ) ≤ D) (hs : 0 < s)
    (μ ν : ProbabilityMeasure (Space (h+2)))
    (hμroot : (μ : Measure (Space (h+2))) Q.carrierᶜ = 0)
    (hνroot : (ν : Measure (Space (h+2))) Q.carrierᶜ = 0)
    (hμfrost : ∀ y : Space (h+2), ∀ r > 0, (μ : Measure (Space (h+2))) (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α))
    (hνfrost : ∀ y : Space (h+2), ∀ r > 0, (ν : Measure (Space (h+2))) (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α))
    (A P : Set (Space (h+2))) (hA : MeasurableSet A) (hP : MeasurableSet P)
    (hμA : (μ : Measure (Space (h+2))) Aᶜ = 0) (hνP : (ν : Measure (Space (h+2))) Pᶜ = 0)
    (hsep : ∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖)
    (hpin : ∀ y ∈ Q.carrier, ∀ x ∈ A ∪ P, ‖y-x‖ ≤ D)
    (Γ : ℕ → Set (Space (h+2) × Space (h+2))) (hΓ : ∀ N, MeasurableSet (Γ N))
    (havailable : CapAvailable μ ν Γ q) :
    ∃ q' : ℝ, q < q' ∧ CapAvailable μ ν Γ q' := by
  obtain ⟨ε,gain,hε,hgain,hwindow⟩ := Regularization.nonendpoint_scale_window_gain
    hpublished hq hq' hqt ht htα hC Q hQ hD hDdim hs
  refine ⟨q+gain,by linarith only [hgain],?_⟩
  intro e he
  have hq0 : 0 ≤ q := by have hh := Nat.cast_nonneg (α := ℝ) h; linarith only [hh,hq]
  obtain ⟨K,hK,hcoarse⟩ := exists_radial_window_denominator he (by positivity : 0 ≤ q+gain)
  obtain ⟨c,hc,Nw,hNw⟩ := hwindow K hK
  have hin : 0 < ε/(2*(K:ℝ)) := by positivity
  obtain ⟨c₀,C₀,hc₀,hC₀,Na,hNa⟩ := havailable (ε/(2*(K:ℝ))) hin
  obtain ⟨Nb,hNb⟩ := Regularization.fixed_constant_absorbed he ((2:ℝ)^(q+gain))
  refine ⟨min c₀ c,C₀+2,lt_min hc₀ hc,by positivity,max Na (max Nw Nb),?_⟩
  intro N hN
  simp only [max_le_iff] at hN
  obtain ⟨hNa',hNw',hNb'⟩ := hN
  obtain ⟨B,hB,hBΓ,hBcost,hcaps⟩ := hNa N hNa'
  let G := Γ N \ B
  have hG : MeasurableSet G := (hΓ N).diff hB
  have hcap₁ : ∀ᵐ z ∂(μ : Measure (Space (h+2))), ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      ∀ u : Space (h+2), ‖u‖ = 1 →
        (ν : Measure (Space (h+2))) {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(ε/(2*(K:ℝ)))*r^q) := by
    filter_upwards [Measure.support_mem_ae (μ := (μ : Measure (Space (h+2))))] with z hz
    intro r hr hr1 u hu
    exact hcaps.1 z hz u hu r (by simpa only [one_div] using hr) hr1
  have hcap₂ : ∀ᵐ x ∂(ν : Measure (Space (h+2))), ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      ∀ u : Space (h+2), ‖u‖ = 1 →
        (μ : Measure (Space (h+2))) {z | (z,x) ∈ G ∧ dist (normalize (z-x)) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(ε/(2*(K:ℝ)))*r^q) := by
    filter_upwards [Measure.support_mem_ae (μ := (ν : Measure (Space (h+2))))] with x hx
    intro r hr hr1 u hu
    exact hcaps.2 x hx u hu r (by simpa only [one_div] using hr) hr1
  obtain ⟨H,hH,hHG,hHcost,hHcaps⟩ := hNw N hNw' μ ν hμroot hνroot hμfrost hνfrost
    A P hA hP hμA hνP hsep hpin G hG hcap₁ hcap₂
  have hHΓ : H ⊆ Γ N := hHG.trans sdiff_subset
  refine ⟨Γ N \ H,(hΓ N).diff hH,sdiff_subset,?_,?_⟩
  · have hfirst : ((μ : Measure (Space (h+2))).prod ν) (Γ N \ G) ≤
        ENNReal.ofReal (C₀*((2:ℝ)^N)^(-c₀)) := by
      apply (measure_mono (show Γ N \ G ⊆ B from ?_)).trans hBcost
      intro z hz
      by_contra hn
      exact hz.2 ⟨hz.1,hn⟩
    have htotal := relative_pruning_cost_trans ((μ : Measure (Space (h+2))).prod ν)
      (Γ N) G H hfirst hHcost
    apply htotal.trans
    have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
    have hp₀ : ((2:ℝ)^N)^(-c₀) ≤ ((2:ℝ)^N)^(-min c₀ c) :=
      Real.rpow_le_rpow_of_exponent_le hR (neg_le_neg (min_le_left _ _))
    have hp : ((2:ℝ)^N)^(-c) ≤ ((2:ℝ)^N)^(-min c₀ c) :=
      Real.rpow_le_rpow_of_exponent_le hR (neg_le_neg (min_le_right _ _))
    calc
      _ ≤ ENNReal.ofReal (C₀*((2:ℝ)^N)^(-min c₀ c))+
          2*ENNReal.ofReal (((2:ℝ)^N)^(-min c₀ c)) :=
        add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hp₀ hC₀.le))
          (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hp))
      _ = _ := by
        rw [add_mul,ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),ENNReal.ofReal_ofNat]
  · have hbound := radialCapBound_of_window μ ν H (Nat.div_le_self N K)
      (by positivity : 0 ≤ q+gain) le_rfl (hcoarse N) (hNb N hNb') hHcaps
    have heq : Γ N \ (Γ N \ H) = H := by
      ext z
      constructor
      · intro hz
        by_contra hn
        exact hz.2 ⟨hz.1,hn⟩
      · intro hz
        exact ⟨hHΓ hz,fun hn => hn.2 hz⟩
    simpa only [heq] using hbound

end Falconer

end OAI
