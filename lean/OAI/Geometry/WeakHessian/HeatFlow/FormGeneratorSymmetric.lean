import Mathlib
import OAI.Geometry.WeakHessian.Entropy.IntegralDensityMeasureLp

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
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace WeakHessianFunctional
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

omit [CompleteSpace E] in
lemma ClosedQuadraticEnergy.formGenerator_symmetric {u v A B : E}
    (hu : hQ.IsFormGenerator u A) (hv : hQ.IsFormGenerator v B) :
    ⟪A,v⟫_ℝ = ⟪u,B⟫_ℝ := by
  have H := hu.2 ⟨v,hv.1⟩
  have H' := hv.2 ⟨u,hu.1⟩
  rw [hQ.form_comm] at H'
  change 2*hQ.form ⟨u,hu.1⟩ ⟨v,hv.1⟩ = -⟪B,u⟫_ℝ at H'
  rw [real_inner_comm u B] at H'
  linarith

end WeakHessianFunctional
namespace WeakHessian
open WeakHessianFunctional WeakHessianTransport MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}

lemma cheeger_scaled_resolvent_bounded (h : QuadraticCheegerEnergy m)
    {t B : ℝ} (ht : 0 < t) (hB : 0 ≤ B) (u : Lp ℝ 2 m)
    (hu : ∀ᵐ x ∂m, |u x| ≤ B) :
    ∀ᵐ x ∂m, |((cheeger_closedQuadraticEnergy h).scale ht).resolvent u x| ≤ B := by
  let η : ℝ → ℝ := fun r => max (-B) (min r B)
  have hη : LipschitzWith 1 η := (LipschitzWith.id.min_const B).const_max (-B)
  have hη0 : η 0 = 0 := by simp only [η, min_eq_left hB, max_eq_right (neg_nonpos.mpr hB)]
  have hfixu : hη.compLp hη0 u = u := by
    apply Lp.ext
    filter_upwards [hη.coeFn_compLp hη0 u, hu] with x hx hu
    simpa only [Function.comp_apply, η, min_eq_left (abs_le.mp hu).2,
      max_eq_right (abs_le.mp hu).1] using hx
  have hQη (f : Lp ℝ 2 m) :
      cheegerEnergy m (hη.compLp hη0 f : X → ℝ) ≤ cheegerEnergy m (f : X → ℝ) := by
    rw [cheegerEnergy_congr_ae (hη.coeFn_compLp hη0 f)]
    exact cheegerEnergy_normalContraction hη hη0 f
  have hfix := ((cheeger_closedQuadraticEnergy h).scale ht).resolvent_normal_fixed m hη hη0
    (fun f => by gcongr; exact hQη f) u hfixu
  filter_upwards [hη.coeFn_compLp hη0 (((cheeger_closedQuadraticEnergy h).scale ht).resolvent u)] with x hx
  rw [hfix] at hx
  change ((cheeger_closedQuadraticEnergy h).scale ht).resolvent u x =
    max (-B) (min (((cheeger_closedQuadraticEnergy h).scale ht).resolvent u x) B) at hx
  rw [hx]
  exact abs_le.mpr ⟨le_max_left _ _,max_le (by linarith) (min_le_right _ _)⟩

variable [IsProbabilityMeasure m]
lemma cheeger_generator_const (h : QuadraticCheegerEnergy m) (c : ℝ) :
    (cheeger_closedQuadraticEnergy h).IsFormGenerator (constLp c) 0 := by
  rw [(cheeger_closedQuadraticEnergy h).isFormGenerator_iff, sub_zero]
  apply (cheeger_closedQuadraticEnergy h).resolvent_fixed_of_energy_zero
  rw [cheegerEnergy_congr_ae (constLp_coe c), cheegerEnergy_const]

variable [CompactSpace X] [BorelSpace X]
lemma CurvatureDimension.weak_generator_pairing {K N : ℝ} (hcd : CurvatureDimension m K N)
    (h : QuadraticCheegerEnergy m)
    {u A : Lp ℝ 2 m} (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {B : ℝ} (hB : 0 ≤ B) (hub : ∀ᵐ x ∂m, |u x| ≤ B)
    {f D : Lp ℝ 2 m} (hf : IsLocalWeakUpperGradient m (f : X → ℝ) (D : X → ℝ)) :
    |⟪f,A⟫_ℝ| ≤ Real.sqrt (2*(cheegerEnergy m (u : X → ℝ)).toReal)*‖D‖ := by
  let c : ℝ := ∫ x, u x ∂m
  let v : Lp ℝ 2 m := u-constLp c
  have hc := cheeger_generator_const h c
  have hv : (cheeger_closedQuadraticEnergy h).IsFormGenerator v A := by
    simpa only [sub_zero] using (cheeger_closedQuadraticEnergy h).formGenerator_sub hu hc
  have hAm : ⟪A,constLp c⟫_ℝ = 0 := by
    simpa only [inner_zero_right] using (cheeger_closedQuadraticEnergy h).formGenerator_symmetric hu hc
  have heq : cheegerEnergy m (v : X → ℝ) = cheegerEnergy m (u : X → ℝ) := by
    apply (ENNReal.toReal_eq_toReal_iff' hv.1.ne hu.1.ne).mp
    have H := (cheeger_closedQuadraticEnergy h).formGenerator_energy hv
    rw [show v = u-constLp c from rfl, inner_sub_right,hAm,sub_zero] at H
    have H' := (cheeger_closedQuadraticEnergy h).formGenerator_energy hu
    change 2*(cheegerEnergy m (v : X → ℝ)).toReal = _ at H
    change 2*(cheegerEnergy m (u : X → ℝ)).toReal = _ at H'
    linarith
  have hvcoe : (v : X → ℝ) =ᵐ[m] (fun x => u x-c) := by
    filter_upwards [Lp.coeFn_sub u (constLp c),constLp_coe (m := m) c] with x hx hc
    simp only [v,hx,Pi.sub_apply,hc]
  have hvmass : ∫ x, v x ∂m = 0 := by
    rw [integral_congr_ae hvcoe, integral_sub ((Lp.memLp u).integrable (by norm_num)) (integrable_const _)]
    simp [c]
  have hvb : ∀ᵐ x ∂m, |v x| ≤ B+|c| := by
    filter_upwards [hub,hvcoe] with x hb hx
    rw [hx]
    exact (abs_sub _ _).trans (add_le_add hb le_rfl)
  have H := hcd.weak_generator_pairing_centered h hv hvmass
    (add_nonneg hB (abs_nonneg c)) hvb hf
  rwa [heq] at H

end WeakHessian
namespace WeakHessianFunctional
open Set Filter
open scoped Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

lemma ClosedQuadraticEnergy.scaled_resolvent_generator_error {u A : E}
    (hu : hQ.IsFormGenerator u A) {t : ℝ} (ht : 0 < t) :
    ‖(hQ.scale ht).resolvent u-u‖ ≤ t*‖A‖ := by
  have H : (hQ.scale ht).resolvent (u-t • A) = u := by
    rw [hQ.scaled_resolvent_iff ht, sub_sub_cancel, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
    exact hu
  have he : (hQ.scale ht).resolvent u-u = t • (hQ.scale ht).resolvent A := by
    change (hQ.scale ht).resolventLinear (u-t • A) = u at H
    rw [map_sub, map_smul] at H
    change (hQ.scale ht).resolvent u - t • (hQ.scale ht).resolvent A = u at H
    exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp H).trans (add_comm _ _))
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  apply mul_le_mul_of_nonneg_left _ ht.le
  have H := (hQ.scale ht).resolvent_nonexpansive A 0
  simpa only [(hQ.scale ht).resolvent_zero, sub_zero] using H

lemma ClosedQuadraticEnergy.scaled_resolvent_tendsto
    (hd : hQ.domain.topologicalClosure = ⊤) {ι : Type*} {l : Filter ι}
    {t : ι → ℝ} (ht : ∀ i, 0 < t i) (hlim : Tendsto t l (𝓝 0)) (u : E) :
    Tendsto (fun i => (hQ.scale (ht i)).resolvent u) l (𝓝 u) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hd' := Submodule.dense_iff_topologicalClosure_eq_top.mpr (hQ.resolvent_range_dense hd)
  obtain ⟨w,hw,hwR⟩ := Metric.dense_iff.mp hd' u (ε/4) (by positivity)
  obtain ⟨v,rfl⟩ := hwR
  have hv : dist (hQ.resolvent v) u < ε/4 := hw
  have hbound : Tendsto (fun i => t i*‖hQ.resolvent v-v‖) l (𝓝 0) := by
    simpa using hlim.mul_const ‖hQ.resolvent v-v‖
  filter_upwards [hbound.eventually_lt_const (by positivity : (0:ℝ) < ε/2)] with i hi
  have he := hQ.scaled_resolvent_generator_error (hQ.isFormGenerator_resolvent v) (ht i)
  have hc := (hQ.scale (ht i)).resolvent_nonexpansive u (hQ.resolvent v)
  have H := dist_triangle ((hQ.scale (ht i)).resolvent u)
    ((hQ.scale (ht i)).resolvent (hQ.resolvent v)) u
  have H' := dist_triangle ((hQ.scale (ht i)).resolvent (hQ.resolvent v)) (hQ.resolvent v) u
  simp only [dist_eq_norm] at H H' hv ⊢
  rw [norm_sub_rev u (hQ.resolvent v)] at hc
  nlinarith

lemma ClosedQuadraticEnergy.energy_le_of_resolvent_pairing
    (hd : hQ.domain.topologicalClosure = ⊤) (f : E) {D : ℝ} (hD : 0 ≤ D)
    (hpair : ∀ (t : ℝ) (ht : 0 < t),
      |⟪f,t⁻¹ • ((hQ.scale ht).resolvent f-f)⟫_ℝ| ≤
        Real.sqrt (2*(Q ((hQ.scale ht).resolvent f)).toReal)*D) :
    Q f ≤ ENNReal.ofReal (D^2/2) := by
  have hb (t : ℝ) (ht : 0 < t) : Q ((hQ.scale ht).resolvent f) ≤ ENNReal.ofReal (D^2/2) := by
    let u := (hQ.scale ht).resolvent f
    let A := t⁻¹ • (u-f)
    have hg : hQ.IsFormGenerator u A := (hQ.scaled_resolvent_iff ht f u).mp rfl
    have he : u = f+t • A := by
      dsimp [A]
      rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
      abel
    have H := hQ.formGenerator_energy hg
    have Hp := hpair t ht
    change |⟪f,A⟫_ℝ| ≤ Real.sqrt (2*(Q u).toReal)*D at Hp
    have hneg : 2*(Q u).toReal ≤ |⟪f,A⟫_ℝ| := by
      conv_rhs at H => rw [he]
      rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at H
      have hN := mul_nonneg ht.le (sq_nonneg ‖A‖)
      rw [real_inner_comm f A] at H
      linarith [neg_le_abs ⟪f,A⟫_ℝ]
    have hx : 0 ≤ 2*(Q u).toReal := by positivity
    have hs := Real.sqrt_nonneg (2*(Q u).toReal)
    have hsq := Real.sq_sqrt hx
    have hsD : Real.sqrt (2*(Q u).toReal) ≤ D := by
      by_contra hn
      have hpos : 0 < Real.sqrt (2*(Q u).toReal) := hD.trans_lt (lt_of_not_ge hn)
      have hm := mul_lt_mul_of_pos_left (lt_of_not_ge hn) hpos
      nlinarith
    have hreal : (Q u).toReal ≤ D^2/2 := by
      have Hsq := sq_le_sq₀ hs hD |>.mpr hsD
      nlinarith
    exact (ENNReal.toReal_le_toReal hg.1.ne ENNReal.ofReal_ne_top).mp
      (by simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ D^2/2)] using hreal)
  let t : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have ht : ∀ n, 0 < t n := fun n => by dsimp [t]; positivity
  have hl : Tendsto t atTop (𝓝 0) := by
    simpa only [t, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact (hQ.lowerSemicontinuous.isClosed_preimage (ENNReal.ofReal (D^2/2))).mem_of_tendsto
    (hQ.scaled_resolvent_tendsto hd ht hl f) (Eventually.of_forall fun n => hb (t n) (ht n))

end WeakHessianFunctional

end
end InlinedFile0

end OAI
