import Mathlib
import OAI.Probability.SKValue.Equations.ResponseJets

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue
lemma responseJet_zero (c:ℝ) (ψ f:ℝ → ℝ) (x:ℝ) : responseJet c ψ f 0 0 x=f x := by
  simp only [responseJet,iteratedDeriv_zero,heat_zero]
  exact mul_div_cancel_left₀ _ (Real.exp_ne_zero _)

lemma baseJet_one_eq {ψ:ℝ → ℝ} (hψ:SmoothTerminal ψ) {c:ℝ} (hc:0≤c) (t x:ℝ) :
    baseJet c ψ 1 t x=c*deriv (coleHopf c t ψ) x := by
  rcases hc.eq_or_lt with rfl | hc
  · have he : heat t (fun _ : ℝ ↦ (1:ℝ))=fun _ ↦ (1:ℝ) := by
      funext y
      simp [heat]
    simp only [baseJet,normalizedJet,zero_mul,Real.exp_zero,iteratedDeriv_one,he]
    simp
  · rw [coleHopf_deriv_eq_normalizedJet hψ.lipschitz hψ.smooth hψ.jets hc t]
    dsimp only [baseJet]
    rw [mul_inv_cancel_left₀ hc.ne']

lemma responseJet_time_lipschitz {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0≤c) (n:ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (s t x : ℝ), (0 ≤ s) → (0 ≤ t) →
      |iteratedDeriv n (responseJet c ψ f 0 s) x-iteratedDeriv n (responseJet c ψ f 0 t) x|≤C*|s-t| := by
  obtain ⟨d,hdc,⟨C,hC,hb⟩,hd⟩ := responseJet_time_jets hψ hf hc n
  refine ⟨C,hC,?_⟩
  intro s t x hs ht
  exact nonneg_time_lipschitz hC
    ((responseJet_joint_jets hψ hf hc n).comp (continuous_id.prodMk continuous_const))
    (hdc.comp (continuous_id.prodMk continuous_const))
    (fun r hr ↦ hd r x hr) (fun r _ ↦ hb r x) hs ht

structure LinearEvolution (T:ℝ) (γ:ℝ → ℝ) (A V:ℝ → ℝ → ℝ) : Prop where
  slices : ∀ t∈Icc (0:ℝ) T,BoundedSmooth (V t)
  continuous_jet : ∀ n x,ContinuousOn (fun t ↦ iteratedDeriv n (V t) x) (Icc (0:ℝ) T)
  bound : ∀ n,∃ C:ℝ,0≤C ∧ ∀ t∈Icc (0:ℝ) T,∀ x,|iteratedDeriv n (V t) x|≤C
  temporal : ∀ n,∃ C:ℝ,0≤C ∧ ∀ s∈Icc (0:ℝ) T,∀ t∈Icc (0:ℝ) T,∀ x,
    |iteratedDeriv n (V s) x-iteratedDeriv n (V t) x|≤C*|s-t|
  pde : ∀ t∈Icc (0:ℝ) T,∀ s∈Icc (0:ℝ) T,∀ x,V s x-V t x=
    -(∫ r in t..s,(1/2:ℝ)*deriv (deriv (V r)) x+γ r*(deriv (A r) x*deriv (V r) x))

lemma responseJet_backward_pde {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0≤c) (T:ℝ) {s t:ℝ} (ht:t∈Icc (0:ℝ) T) (hs:s∈Icc (0:ℝ) T) (x:ℝ) :
    responseJet c ψ f 0 (T-s) x-responseJet c ψ f 0 (T-t) x=
      -(∫ r in t..s,(1/2:ℝ)*deriv (deriv (responseJet c ψ f 0 (T-r))) x+
        c*(deriv (coleHopf c (T-r) ψ) x*deriv (responseJet c ψ f 0 (T-r)) x)) := by
  let V := fun r ↦ responseJet c ψ f 0 (T-r)
  let A := fun r ↦ coleHopf c (T-r) ψ
  let g := fun r ↦ (1/2:ℝ)*deriv (deriv (V r)) x+c*(deriv (A r) x*deriv (V r) x)
  have hm : Continuous (fun r : ℝ ↦ (T-r,x)) :=
    (continuous_const.sub continuous_id).prodMk continuous_const
  have hcj (n:ℕ) : Continuous (fun r ↦ iteratedDeriv n (V r) x) := by
    have hh := (responseJet_joint_jets hψ hf hc n).comp hm
    change Continuous (fun r ↦ iteratedDeriv n (responseJet c ψ f 0 (T-r)) x)
    exact hh
  have hgc:Continuous g := by
    have h1:Continuous (fun r ↦ deriv (V r) x) := by simpa only [iteratedDeriv_one] using hcj 1
    have h2:Continuous (fun r ↦ deriv (deriv (V r)) x) := by
      simpa only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using hcj 2
    exact (continuous_const.mul h2).add (continuous_const.mul ((hψ.backward_gradient_continuous hc T x).mul h1))
  have hd (r:ℝ) (hr:r∈Ioo (0:ℝ) T) : HasDerivAt (fun r ↦ V r x) (-g r) r := by
    have hh := (responseJet_heat_drift hψ hf hc (sub_pos.mpr hr.2) 0 x).comp r
      ((hasDerivAt_const r T).sub (hasDerivAt_id r))
    rw [baseJet_one_eq hψ hc] at hh
    convert! hh using 1
    dsimp only [V,A,g]
    ring
  have he := integral_from_deriv_on_strip (by simpa only [iteratedDeriv_zero] using (hcj 0).continuousOn)
    hgc.neg.continuousOn hd hs ht
  change _=∫ r in t..s,-(g r) at he
  rw [intervalIntegral.integral_neg] at he
  exact he

lemma SmoothTerminal.linear_constant {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0≤c) (T:ℝ) :
    LinearEvolution T (fun _ ↦ c) (fun t ↦ coleHopf c (T-t) ψ) (fun t ↦ responseJet c ψ f 0 (T-t)) := by
  refine ⟨fun t _ ↦ responseJet_boundedSmooth hψ hf hc 0 _,?_,?_,?_,?_⟩
  · intro n x
    have hm : Continuous (fun r : ℝ ↦ (T-r,x)) :=
      (continuous_const.sub continuous_id).prodMk continuous_const
    exact ((responseJet_joint_jets hψ hf hc n).comp hm).continuousOn
  · intro n
    obtain ⟨C,hC,hb⟩ := responseJet_uniform_jets hψ hf hc n 0
    exact ⟨C,hC,fun t _ x ↦ hb (T-t) x⟩
  · intro n
    obtain ⟨C,hC,hb⟩ := responseJet_time_lipschitz hψ hf hc n
    refine ⟨C,hC,?_⟩
    intro s hs t ht x
    have hh := hb (T-s) (T-t) x (sub_nonneg.mpr hs.2) (sub_nonneg.mpr ht.2)
    simpa only [sub_sub_sub_cancel_left,abs_sub_comm] using hh
  · intro t ht s hs x
    exact responseJet_backward_pde hψ hf hc T ht hs x
end SKValue

end

end OAI
