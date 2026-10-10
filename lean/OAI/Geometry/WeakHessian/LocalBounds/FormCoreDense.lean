import Mathlib
import OAI.Geometry.WeakHessian.Calculus.FormLimits

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile162
noncomputable section
namespace WeakHessianFunctional
open Set Filter
open scoped Topology ENNReal NNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

lemma ClosedQuadraticEnergy.form_linear_zero_of_graph_core
    (hd : hQ.domain.topologicalClosure = ⊤) (S : E → E → Prop)
    (hS : ∀ u A,S u A → hQ.IsFormGenerator u A)
    (hcore : ∀ u A,hQ.IsFormGenerator u A → ∃ us As : ℕ → E,
      (∀ n,S (us n) (As n)) ∧ Tendsto us atTop (𝓝 u) ∧ Tendsto As atTop (𝓝 A))
    (F : hQ.domain →ₗ[ℝ] ℝ) {C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ u,|F u| ≤ C*(‖(u:E)‖+Real.sqrt (hQ.realEnergy u)))
    (hz : ∀ u A,(hs : S u A) → F ⟨u,(hS u A hs).1⟩ = 0) : ∀ u,F u = 0 := by
  have hgen : ∀ u A,(hg : hQ.IsFormGenerator u A) → F ⟨u,hg.1⟩=0 := by
    intro u A hg
    obtain ⟨us,As,hs,hu,hA⟩ := hcore u A hg
    let vs (n : ℕ) : hQ.domain := ⟨us n,(hS _ _ (hs n)).1⟩
    let v : hQ.domain := ⟨u,hg.1⟩
    have he : Tendsto (fun n => hQ.realEnergy (vs n-v)) atTop (𝓝 0) := by
      have HE (n : ℕ) : hQ.realEnergy (vs n-v) = -⟪As n-A,us n-u⟫_ℝ/2 := by
        have H := hQ.formGenerator_energy (hQ.formGenerator_sub (hS _ _ (hs n)) hg)
        change 2*hQ.realEnergy (vs n-v) = _ at H
        linarith only [H]
      simp_rw [HE]
      simpa only [sub_self,inner_zero_right,neg_zero,zero_div] using ((hA.sub_const A).inner (𝕜 := ℝ) (hu.sub_const u)).neg.div_const 2
    have hn : Tendsto (fun n => ‖((vs n-v : hQ.domain):E)‖) atTop (𝓝 0) := by
      change Tendsto (fun n => ‖us n-u‖) atTop (𝓝 0)
      simpa only [sub_self,norm_zero] using (hu.sub_const u).norm
    have ht := (hn.add he.sqrt).const_mul C
    simp only [Real.sqrt_zero,add_zero,mul_zero] at ht
    have hlim : Tendsto (fun n => F (vs n-v)) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => by simpa only [Real.norm_eq_abs] using hb (vs n-v)) ht
    have hzero (n : ℕ) : F (vs n-v) = -F v := by rw [map_sub,hz _ _ (hs n),zero_sub]
    simp_rw [hzero] at hlim
    exact neg_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hlim)
  intro v
  let t (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  let us (n : ℕ) := (hQ.scale (ht n)).resolvent (v:E)
  let As (n : ℕ) := (t n)⁻¹ • (us n-(v:E))
  have hg (n : ℕ) : hQ.IsFormGenerator (us n) (As n) :=
    (hQ.scaled_resolvent_iff (ht n) (v:E) (us n)).mp rfl
  let vs (n : ℕ) : hQ.domain := ⟨us n,(hg n).1⟩
  have hu := hQ.scaled_resolvent_tendsto hd ht tendsto_one_div_add_atTop_nhds_zero_nat (v:E)
  have hE := (tendsto_const_nhds (x := hQ.realEnergy v)).sub
    (hQ.scaled_resolvent_energy_tendsto hd ht tendsto_one_div_add_atTop_nhds_zero_nat v)
  simp only [sub_self] at hE
  have he : Tendsto (fun n => hQ.realEnergy (v-vs n)) atTop (𝓝 0) :=
    squeeze_zero (fun n => hQ.realEnergy_quadratic.nonneg _) (fun n => hQ.scaled_resolvent_form_error_le v (ht n)) hE
  have hn : Tendsto (fun n => ‖((v-vs n : hQ.domain):E)‖) atTop (𝓝 0) := by
    change Tendsto (fun n => ‖(v:E)-us n‖) atTop (𝓝 0)
    simpa only [sub_self,norm_zero] using ((tendsto_const_nhds (x := (v:E))).sub hu).norm
  have hlim : Tendsto (fun n => F (v-vs n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => by simpa only [Real.norm_eq_abs] using hb (v-vs n))
    simpa only [Real.sqrt_zero,add_zero,mul_zero] using (hn.add he.sqrt).const_mul C
  have hzero (n : ℕ) : F (v-vs n) = F v := by rw [map_sub,hgen _ _ (hg n),sub_zero]
  simp_rw [hzero] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim
end WeakHessianFunctional

end
end InlinedFile162

end OAI
