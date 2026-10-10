import OAI.Geometry.RCD.Heat.CompactHeatScaledHessianBound
import OAI.Geometry.RCD.Heat.GaussianBochnerTail
import OAI.Geometry.RCD.Heat.CompactHeatDensityGaussianTail
import OAI.Geometry.RCD.Heat.CompactHeatUniformDensity

namespace OAI

/-! # Uniform tails of the original scaled heat Hessian

The estimates concern the actual globally defined factor Hessians in the
second derivative formula, for every noise index and every interior time.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

theorem scaled_hessian_uniform_tails (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    {R δ : ℝ} (hR : 1 ≤ R) (hδ : 0 < δ)
    (hS : ∀ y:S, dist p y ≤ R) (hT : ∀ y:T, dist p y ≤ R)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {a : ℝ} (ha : 0 < a)
    (u v WU WV UV : ℕ → InteriorHeatTime δ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : ∀ k t, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k t) =ᵐ[hausdorff n X]
      hX.compactHeatFactor hn p μ (D.left k) (ε k/4*t.val)
        (mul_pos (div_pos (hε k) (by norm_num)) t.val.property.1))
    (hv : ∀ k t, SobolevSpace.toLp (hausdorff n X) hX.quadratic (v k t) =ᵐ[hausdorff n X]
      hX.compactHeatFactor hn p ν (D.right k) (ε k/4*(1-t.val))
        (mul_pos (div_pos (hε k) (by norm_num)) (sub_pos.mpr t.val.property.2)))
    (hWU : ∀ k t, SobolevSpace.toLp (hausdorff n X) hX.quadratic (WU k t) =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic a ha f) (u k t))
    (hWV : ∀ k t, SobolevSpace.toLp (hausdorff n X) hX.quadratic (WV k t) =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic a ha f) (v k t))
    (hUV : ∀ k t, SobolevSpace.toLp (hausdorff n X) hX.quadratic (UV k t) =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic (u k t) (v k t)) :
    let m := hausdorff n X
    let q := hX.quadratic
    let w := heatSobolev m q a ha f
    ∃ L : ℝ, 1 ≤ L ∧ TendstoUniformly
      (fun N (y : ℕ × InteriorHeatTime δ) => ∫ x in (ball p (2^N*L))ᶜ,
        |(ε y.1/2)^2*localHessianAction m q w (u y.1 y.2) (v y.1 y.2)
          (WU y.1 y.2) (WV y.1 y.2) (UV y.1 y.2) x| ∂m) (fun _ => 0) atTop := by
  intro m q w
  obtain ⟨M,C,E,hM,hC,hE,hmeasure⟩ := D.scaled_hessian_density_bound hK hε1
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν (zero_le_one.trans hR) hδ hS hT f A hf ha
  obtain ⟨V,B,_hV,hB,hvol⟩ := hX.exponential_volume K n hn p
  obtain ⟨Aρ,ℓ,hAρ,_hℓ,htail⟩ := D.interpolationDensity_gaussian_tail hε1 p hR hS hT
  obtain ⟨Dρ,hDρ,hden⟩ := D.interpolationDensity_uniform_bound hK hε1
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν p hR hS hT
  let Q₀ := Real.exp |K| *(4*C/δ+32*E*R^2/δ^2)
  let Q₁ := Real.exp |K| *(32*E/δ^2)
  have hQ₀ : 0 ≤ Q₀ := by dsimp only [Q₀]; positivity
  have hQ₁ : 0 ≤ Q₁ := by dsimp only [Q₁]; positivity
  let F (y : ℕ × InteriorHeatTime δ) x := (ε y.1/2)^2*
    localHessianAction m q w (u y.1 y.2) (v y.1 y.2) (WU y.1 y.2) (WV y.1 y.2) (UV y.1 y.2) x
  let ρ (y : ℕ × InteriorHeatTime δ) := D.interpolationDensity y.1 y.2.val
  have hFi (y : ℕ × InteriorHeatTime δ) : Integrable (F y) m :=
    (localHessianAction_integrable m q w (u y.1 y.2) (v y.1 y.2)
      (WU y.1 y.2) (WV y.1 y.2) (UV y.1 y.2)).const_mul _
  apply gaussian_bochner_uniform_tail m p hM.le hB hAρ.le hDρ.le hQ₀ hQ₁ hvol
    ρ F hFi (fun y x => hden y.1 y.2.val x) (fun y x hx => htail y.1 y.2.val x hx)
  intro r hr
  obtain ⟨σ,hσ,hmass,hpoint⟩ := hmeasure r hr
  let := hσ
  refine ⟨σ,hσ,hmass,?_⟩
  intro y
  have hbound := hpoint y.1 y.2 (u y.1 y.2) (v y.1 y.2) (WU y.1 y.2)
    (WV y.1 y.2) (UV y.1 y.2) (hu y.1 y.2) (hv y.1 y.2)
    (hWU y.1 y.2) (hWV y.1 y.2) (hUV y.1 y.2)
  filter_upwards [hbound] with x hx
  have hp : Real.exp |K| *(4*C/δ+16*E*(R+dist p x)^2/δ^2) ≤
      Q₀+Q₁*(dist x p)^2 := by
    have hsq : (R+dist p x)^2 ≤ 2*R^2+2*(dist p x)^2 := by
      nlinarith only [sq_nonneg (R-dist p x)]
    have hh := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 16*E))
        (sq_nonneg δ)) (Real.exp_pos |K|).le
    calc
      _ = Real.exp |K| *(4*C/δ)+Real.exp |K| *(16*E*(R+dist p x)^2/δ^2) := by ring
      _ ≤ Real.exp |K| *(4*C/δ)+Real.exp |K| *(16*E*(2*R^2+2*(dist p x)^2)/δ^2) :=
        add_le_add_right hh _
      _ = _ := by dsimp only [Q₀,Q₁]; rw [dist_comm x p]; ring
  apply hx.trans
  dsimp only [F,ρ]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (D.interpolationDensity_pos y.1 y.2.val x).le)
    (by positivity)

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
