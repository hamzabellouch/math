import OAI.Geometry.RCD.Coordinates.CompactHeatOsmoticRegular
import OAI.Geometry.RCD.Heat.CompactHeatOsmoticTransfer
import OAI.Geometry.RCD.Heat.CompactHeatUniformDensity
import OAI.Geometry.RCD.Coordinates.FixedGaugeRegularGradient
import OAI.Geometry.RCD.Heat.BoundedHeatMixedMovingDensity

namespace OAI

/-! # Vanishing of the actual mixed osmotic/forward Hessian term -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2≤n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0<ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

theorem local_mixed_osmotic_hessian_vanishes (hK : K≤0) (hε1 : ∀ k, ε k≤1)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0≤ρ₀ x) (hp₁ : ∀ x, 0≤ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x|≤C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x|≤C₁)
    (hμ : μ.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    (z : X) {R r δ : ℝ} (hR : 1≤R) (hr : 0<r)
    (hS : ∀ a:S, dist z a≤R) (hT : ∀ b:T, dist z b≤R) (hδ : 0<δ)
    (φ : X → ℝ) (Lφ : ℝ≥0) (hφ : LipschitzWith Lφ φ) (hφc : HasCompactSupport φ)
    (hφ01 : ∀ x, φ x∈Icc (0:ℝ) 1) (hsupp : tsupport φ⊆closedBall z r)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x|≤A) {a : ℝ} (ha : 0<a) :
    let m := hausdorff n X
    let Q := hX.quadratic
    let w := heatSobolev m Q a ha f
    ∃ η u WG WV GV : ℕ → InteriorHeatTime δ → SobolevSpace m Q,
      (∀ k t, SobolevSpace.toLp m Q (η k t) =ᵐ[m.restrict (closedBall z r)] D.osmoticPotential k t.val) ∧
      (∀ k t, SobolevSpace.toLp m Q (u k t) =ᵐ[m.restrict (closedBall z r)]
        hX.fixedGaugeScaledPotential hn p μ (D.left k) (ε k) (hε k) (δ/2) (by positivity) z (t.val/2)) ∧
      (∀ k t, SobolevSpace.toLp m Q (WG k t) =ᵐ[m.restrict (closedBall z r)] localGamma m Q w (η k t)) ∧
      (∀ k t, SobolevSpace.toLp m Q (WV k t) =ᵐ[m.restrict (closedBall z r)] localGamma m Q w (u k t)) ∧
      (∀ k t, SobolevSpace.toLp m Q (GV k t) =ᵐ[m.restrict (closedBall z r)] localGamma m Q (η k t) (u k t)) ∧
      TendstoUniformly (fun k t => ∫ x in closedBall z r, φ x*D.interpolationDensity k t.val x*
        |localHessianAction m Q w (η k t) (u k t) (WG k t) (WV k t) (GV k t) x| ∂m)
        (fun _ => 0) atTop := by
  intro m Q w
  classical
  have hδ2 : 0 < δ/2 := half_pos hδ
  choose η dq V L B hdq hV hB hη0 hη using fun k (t : InteriorHeatTime δ) =>
    D.osmotic_regular ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν k t.val (isCompact_closedBall z r)
  choose u du U Lu Bu hdu hU hBu hu0 hu using fun k (t : InteriorHeatTime δ) =>
    hX.fixed_gauge_heat_regular hn p μ ρ₀ hm₀ hp₀ hC₀ hμ (D.left k) (D.left_pos k) (hε k) hδ2
      (show δ/2 ≤ (t.val:ℝ)/2 by linarith [t.property.1]) z (isCompact_closedBall z r)
  have hηB k t : ∀ᵐ x ∂m, |SobolevSpace.toLp m Q (η k t) x| ≤ B k t := by
    filter_upwards [hη0 k t] with x hx
    rw [hx]
    exact hB k t x
  have huB k t : ∀ᵐ x ∂m, |SobolevSpace.toLp m Q (u k t) x| ≤ Bu k t := by
    filter_upwards [hu0 k t] with x hx
    rw [hx]
    exact hBu k t x
  obtain ⟨P,hP,hgrad⟩ := hX.fixed_gauge_gradient_bound hn p μ ρ₀ hm₀ hp₀ hC₀ hμ z
    (r := r) (zero_le_one.trans hR) hS hδ2
  have hgu k (t : InteriorHeatTime δ) : ∀ᵐ x ∂m.restrict (closedBall z r),
      localGamma m Q (u k t) (u k t) x ≤ P :=
    hgrad (D.left k) (D.left_pos k) (ε k) (hε k) (hε1 k) (t.val/2)
      ⟨by linarith [t.property.1],by linarith [t.val.property.2]⟩ (u k t) (hu k t)
  obtain ⟨C,hC,hbound⟩ := D.interpolationDensity_uniform_bound hK hε1
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν z hR hS hT
  let W k (t : InteriorHeatTime δ) x := φ x*D.interpolationDensity k t.val x
  have hW k t : AEStronglyMeasurable (W k t) m :=
    (hφ.continuous.mul (D.interpolationDensity_continuous k t.val)).aestronglyMeasurable
  have hWb k t : ∀ᵐ x ∂m, 0 ≤ W k t x ∧ W k t x ≤ C := Eventually.of_forall fun x =>
    ⟨mul_nonneg (hφ01 x).1 (D.interpolationDensity_pos k t.val x).le,
      (mul_le_of_le_one_left (D.interpolationDensity_pos k t.val x).le (hφ01 x).2).trans (hbound k t.val x)⟩
  have hzero k t x (hx : x ∉ closedBall z r) : W k t x = 0 := by
    dsimp only [W]
    rw [image_eq_zero_of_notMem_tsupport (fun hm => hx (hsupp hm)),zero_mul]
  have hE := D.local_osmotic_vanishes_of_rep hK hε1 hε0
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν z (zero_le_one.trans hR) hS hT hδ
    φ Lφ hφ hφc hφ01 hsupp η (fun k t => ae_restrict_of_ae_restrict_of_subset hsupp (hη k t))
  obtain ⟨WG,WV,GV,hWG,hWV,hGV,hlim⟩ := hX.bounded_heat_mixed_moving_density hn z hK f A hf ha hr
    η u dq du hdq hdu V U L Lu B Bu hV hU hη0 hu0 hηB huB hP hgu W hW C hC.le hWb hzero hE
  exact ⟨η,u,WG,WV,GV,hη,hu,hWG,hWV,hGV,hlim⟩

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
