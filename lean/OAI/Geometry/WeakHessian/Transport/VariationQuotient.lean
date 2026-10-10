import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.SubConst
import OAI.Geometry.WeakHessian.Transport.IntegrableEvalBounded

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessianTransport
open Filter Set MeasureTheory
open scoped Topology

lemma variation_quotient_le {a t A P C F I : ℝ} (ht : 0 < t) (hP : P ≤ A)
    (hC : t*(1-t/2)*A ≤ C) (hY : C+a*F ≤ (I+t*A)/2) :
    a*(F/t) ≤ ((I/t)-P+t*A)/2 := by
  have h : a*F ≤ (I-t*A+t^2*A)/2 := by nlinarith
  calc
    a*(F/t) = (a*F)/t := by ring
    _ ≤ ((I-t*A+t^2*A)/2)/t := div_le_div_of_nonneg_right h ht.le
    _ = ((I/t)-A+t*A)/2 := by field_simp [ne_of_gt ht]
    _ ≤ _ := by linarith
end WeakHessianTransport

namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma IsTestPlan.contact_first_variation (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    (hb : BoundedTracks π) (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {φ ψ f : X → ℝ} {L T : ℝ≥0} (hφ : LipschitzWith L φ) (hf : LipschitzWith T f)
    (hdual : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hcontact : ∀ᵐ γ ∂π, φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2) :
    Tendsto (fun t : ℝ => (∫ γ, f (γ timeZero)-f (evalReal γ t) ∂π)/t)
      (𝓝[>] 0) (𝓝 (∫ γ, gamma m φ f (γ timeZero) ∂π)) := by
  let : IsProbabilityMeasure π := hπ.1
  let A := ∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂π
  let P := ∫ γ, (weakGradient m φ (γ timeZero))^2 ∂π
  let Q := (∫ γ, (weakGradient m f (γ timeZero))^2 ∂π)/2
  have hP : P ≤ A := hπ.contact_gradient_energy_le hfin hb hφ hdual hcontact
  apply WeakHessianTransport.tendsto_of_quadratic_variations (Q := Q)
  intro a
  let u : X → ℝ := fun x => φ x+a*f x
  have hu : LipschitzWith (L+‖a‖₊*T) u := hφ.add (lipschitz_const_mul_real hf a)
  let I : ℝ → ℝ := fun t => ∫ s in 0..t, ∫ γ, (weakGradient m u (evalReal γ s))^2 ∂π
  refine ⟨fun t => (I t/t-P+t*A)/2,?_,?_⟩
  · have H := ((hπ.tendsto_average_gradient_energy hfin hb hu).sub_const P).add
      ((tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0)).mul_const A)
    have HH := H.div_const (2:ℝ)
    have he : ((∫ γ, (weakGradient m u (γ timeZero))^2 ∂π)-P+0*A)/2 =
        a*(∫ γ, gamma m φ f (γ timeZero) ∂π)+a^2*Q := by
      dsimp only [u]
      rw [hπ.perturbation_energy hfin hpar hφ hf timeZero a]
      dsimp [P,Q]
      ring
    rw [he] at HH
    exact HH
  · have hevent : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t ∧ t < 1 := by
      have hgt : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
      have hlt : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
        (eventually_lt_nhds (by norm_num : (0:ℝ) < 1)).filter_mono nhdsWithin_le_nhds
      exact hgt.and hlt
    filter_upwards [hevent] with t ht
    let τ : Time := ⟨t,ht.1.le,ht.2.le⟩
    have hc : clampTime t = τ := Subtype.ext (clampTime_of_mem τ.property)
    have hU := (weakGradient_isMinimal (localSobolev_of_lipschitz hfin hu).2).1
    have hUb : ∀ᵐ x ∂m, |weakGradient m u x| ≤ ((L+‖a‖₊*T : ℝ≥0):ℝ) := by
      filter_upwards [weakGradient_nonneg (m := m) u,weakGradient_le_lipschitz hfin hu] with x hn hx
      simpa only [abs_of_nonneg hn] using hx
    have hY := hU.geodesic_young_time hu.continuous.aemeasurable (L+‖a‖₊*T).coe_nonneg hUb hπ hb hgeo τ ht.1
    have hiφ (s : Time) := hb.integrable_lipschitz_eval hφ s
    have hif (s : Time) := hb.integrable_lipschitz_eval hf s
    have hcomb : (∫ γ, u (γ timeZero)-u (γ τ) ∂π) =
        (∫ γ, φ (γ timeZero)-φ (γ τ) ∂π)+a*(∫ γ, f (γ timeZero)-f (γ τ) ∂π) := by
      have H : (fun γ : Curve X => u (γ timeZero)-u (γ τ)) =
          fun γ => (φ (γ timeZero)-φ (γ τ))+a*(f (γ timeZero)-f (γ τ)) := by
        funext γ; dsimp [u]; ring
      have hi1 := (hiφ timeZero).sub (hiφ τ)
      have hi2 := ((hif timeZero).sub (hif τ)).const_mul a
      change Integrable (fun γ => φ (γ timeZero)-φ (γ τ)) π at hi1
      change Integrable (fun γ => a*(f (γ timeZero)-f (γ τ))) π at hi2
      rw [H,integral_add hi1 hi2,integral_const_mul]
    rw [hcomb] at hY
    have hC : t*(1-t/2)*A ≤ (∫ γ, φ (γ timeZero)-φ (γ τ) ∂π) := by
      rw [← integral_const_mul]
      apply integral_mono_ae (hb.integrable_length_sq.const_mul _) ((hiφ timeZero).sub (hiφ τ))
      filter_upwards [hgeo,hcontact] with γ hγ hg
      exact contact_geodesic_decrease hdual hγ hg τ
    have H := WeakHessianTransport.variation_quotient_le ht.1 hP hC hY
    simpa only [I,τ,evalReal,hc] using H
end WeakHessian

end
end InlinedFile0

end OAI
