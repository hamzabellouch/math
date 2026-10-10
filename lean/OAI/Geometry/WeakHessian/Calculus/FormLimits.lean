import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.SubConst
import OAI.Geometry.WeakHessian.HeatFlow.FormGeneratorSymmetric
import OAI.Geometry.WeakHessian.Sobolev.AddConst

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile13
noncomputable section
namespace WeakHessianFunctional
open Set Filter
open scoped Topology ENNReal NNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

omit [CompleteSpace E] in
lemma ClosedQuadraticEnergy.form_cauchySchwarz (u v : hQ.domain) :
    (hQ.form u v)^2 ≤ hQ.realEnergy u*hQ.realEnergy v :=
  hQ.realEnergy_quadratic.polar_cauchySchwarz u v

lemma ClosedQuadraticEnergy.scaled_resolvent_energy_le {t : ℝ} (ht : 0 < t) (u : E) :
    Q ((hQ.scale ht).resolvent u) ≤ Q u := by
  have H := (hQ.scale ht).resolvent_energy_le u
  exact (ENNReal.mul_le_mul_iff_right (ne_of_gt (ENNReal.ofReal_pos.mpr ht)) ENNReal.ofReal_ne_top).mp H

lemma ClosedQuadraticEnergy.scaled_resolvent_energy_tendsto
    (hd : hQ.domain.topologicalClosure = ⊤) {ι : Type*} {l : Filter ι}
    {ts : ι → ℝ} (hts : ∀ i, 0 < ts i) (hl : Tendsto ts l (𝓝 0)) (v : hQ.domain) :
    Tendsto (fun i => (Q ((hQ.scale (hts i)).resolvent v)).toReal) l (𝓝 (hQ.realEnergy v)) := by
  have hv := hQ.scaled_resolvent_tendsto hd hts hl (v:E)
  have H : Tendsto (fun i => Q ((hQ.scale (hts i)).resolvent v)) l (𝓝 (Q v)) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact hv (hQ.lowerSemicontinuous v a ha)
    · intro b hb
      exact Eventually.of_forall fun i => (hQ.scaled_resolvent_energy_le (hts i) v).trans_lt hb
  exact (ENNReal.continuousAt_toReal v.property.ne).tendsto.comp H

lemma ClosedQuadraticEnergy.scaled_resolvent_form_error_le (v : hQ.domain) {t : ℝ} (ht : 0 < t) :
    (Q ((v:E)-(hQ.scale ht).resolvent v)).toReal ≤
      hQ.realEnergy v-(Q ((hQ.scale ht).resolvent v)).toReal := by
  let r : E := (hQ.scale ht).resolvent v
  let A : E := t⁻¹ • (r-v)
  have hg : hQ.IsFormGenerator r A := (hQ.scaled_resolvent_iff ht v r).mp rfl
  let u : hQ.domain := ⟨r,hg.1⟩
  have he : t • A = r-v := by dsimp [A]; rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
  have hp := hg.2 (v-u)
  have hi : 0 ≤ -⟪A,(v-u:E)⟫_ℝ := by
    change 0 ≤ -⟪A,(v:E)-r⟫_ℝ
    have H : (v:E)-r = -(t • A) := by rw [he]; abel
    rw [H,inner_neg_right,neg_neg,real_inner_smul_right,real_inner_self_eq_norm_sq]
    positivity
  change 0 ≤ -⟪A,((v-u : hQ.domain):E)⟫_ℝ at hi
  change 2*hQ.form u (v-u) = _ at hp
  have H := hQ.realEnergy_add u (v-u)
  rw [add_sub_cancel] at H
  change (Q ((v:E)-r)).toReal ≤ _
  change hQ.realEnergy (v-u) ≤ hQ.realEnergy v-hQ.realEnergy u
  linarith

lemma ClosedQuadraticEnergy.exists_formGenerator_approx
    (hd : hQ.domain.topologicalClosure = ⊤) (v : hQ.domain) {ε : ℝ} (hε : 0 < ε) :
    ∃ u A : E, hQ.IsFormGenerator u A ∧ (Q ((v:E)-u)).toReal < ε := by
  let t : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  have hl : Tendsto t atTop (𝓝 0) := by
    simpa only [t,one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have H := (tendsto_const_nhds (x := hQ.realEnergy v)).sub (hQ.scaled_resolvent_energy_tendsto hd ht hl v)
  simp only [sub_self] at H
  obtain ⟨n,hn⟩ := (H.eventually_lt_const hε).exists
  refine ⟨(hQ.scale (ht n)).resolvent v,(t n)⁻¹ • ((hQ.scale (ht n)).resolvent v-v),
    (hQ.scaled_resolvent_iff (ht n) v _).mp rfl,?_⟩
  exact (hQ.scaled_resolvent_form_error_le v (ht n)).trans_lt hn

lemma ClosedQuadraticEnergy.form_tendsto_zero_of_bounded_energy
    (hd : hQ.domain.topologicalClosure = ⊤) {ι : Type*} {l : Filter ι}
    (us : ι → hQ.domain) (hu : Tendsto (fun i => (us i:E)) l (𝓝 0))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ i, hQ.realEnergy (us i) ≤ M) (v : hQ.domain) :
    Tendsto (fun i => hQ.form (us i) v) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨r,A,hg,hr⟩ := hQ.exists_formGenerator_approx hd v
    (show 0 < (ε/2)^2/(M+1) by positivity)
  let r' : hQ.domain := ⟨r,hg.1⟩
  have hrem (i : ι) : |hQ.form (us i) (v-r')| < ε/2 := by
    have H := hQ.form_cauchySchwarz (us i) (v-r')
    have hener : hQ.realEnergy (v-r') < (ε/2)^2/(M+1) := hr
    have hn := hQ.realEnergy_quadratic.nonneg (v-r')
    have H' := mul_le_mul_of_nonneg_right (hbound i) hn
    have hp : (M+1)*hQ.realEnergy (v-r') < (ε/2)^2 := by
      have hh := (lt_div_iff₀ (by linarith : (0:ℝ) < M+1)).mp hener
      nlinarith
    rw [abs_lt]
    constructor <;> nlinarith
  have he (i : ι) : hQ.form (us i) r' = -⟪A,(us i:E)⟫_ℝ/2 := by
    rw [hQ.form_comm]
    have H := hg.2 (us i)
    change 2*hQ.form r' (us i) = _ at H
    linarith
  have Hinner : Tendsto (fun i => hQ.form (us i) r') l (𝓝 0) := by
    simp_rw [he]
    simpa using ((tendsto_const_nhds (x := A)).inner (𝕜 := ℝ) hu).neg.div_const 2
  have Habs := Hinner.norm
  simp only [norm_zero,Real.norm_eq_abs] at Habs
  filter_upwards [Habs.eventually_lt_const (half_pos hε)] with i hi
  have H : hQ.form (us i) v = hQ.form (us i) (v-r')+hQ.form (us i) r' := by rw [map_sub]; ring
  rw [Real.dist_eq,sub_zero,H]
  exact (abs_add_le _ _).trans_lt (by linarith [hrem i])

lemma ClosedQuadraticEnergy.form_tendsto_of_bounded_energy
    (hd : hQ.domain.topologicalClosure = ⊤) {ι : Type*} {l : Filter ι}
    (us : ι → hQ.domain) (u v : hQ.domain)
    (hu : Tendsto (fun i => (us i:E)) l (𝓝 (u:E)))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ i, hQ.realEnergy (us i) ≤ M) :
    Tendsto (fun i => hQ.form (us i) v) l (𝓝 (hQ.form u v)) := by
  have hsub : Tendsto (fun i => ((us i-u : hQ.domain):E)) l (𝓝 0) := by simpa using hu.sub_const (u:E)
  have he (i : ι) : hQ.realEnergy (us i-u) ≤ 2*M+2*hQ.realEnergy u := by
    have H := hQ.realEnergy_quadratic.parallelogram (us i) u
    have hn := hQ.realEnergy_quadratic.nonneg (us i+u)
    linarith [hbound i]
  have H := hQ.form_tendsto_zero_of_bounded_energy hd (fun i => us i-u) hsub
    (show 0 ≤ 2*M+2*hQ.realEnergy u from by have h := hQ.realEnergy_quadratic.nonneg u; positivity) he v
  simp only [map_sub,LinearMap.sub_apply] at H
  simpa using H.add_const (hQ.form u v)

lemma ClosedQuadraticEnergy.form_energy_sub_tendsto
    (hd : hQ.domain.topologicalClosure = ⊤) {ι : Type*} {l : Filter ι}
    (us : ι → hQ.domain) (u : hQ.domain)
    (hu : Tendsto (fun i => (us i:E)) l (𝓝 (u:E)))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ i, hQ.realEnergy (us i) ≤ M)
    (hener : Tendsto (fun i => hQ.realEnergy (us i)) l (𝓝 (hQ.realEnergy u))) :
    Tendsto (fun i => hQ.realEnergy (us i-u)) l (𝓝 0) := by
  have hf := hQ.form_tendsto_of_bounded_energy hd us u u hu hM hbound
  rw [hQ.form_self] at hf
  have he (i : ι) : hQ.realEnergy (us i-u) =
      hQ.realEnergy (us i)+hQ.realEnergy u-2*hQ.form (us i) u := by
    rw [← hQ.form_self (us i-u)]
    simp only [map_sub,LinearMap.sub_apply,hQ.form_self,hQ.form_comm u (us i)]
    ring
  simp_rw [he]
  simpa only [two_mul, sub_self] using
    (hener.add_const (hQ.realEnergy u)).sub (hf.const_mul 2)

end WeakHessianFunctional

end
end InlinedFile13

end OAI
