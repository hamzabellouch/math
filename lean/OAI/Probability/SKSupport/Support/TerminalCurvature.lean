import Mathlib
import OAI.Probability.SKSupport.Regularity.Regularity

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat
variable {Ω : Type*} [MeasurableSpace Ω]

lemma parameter_bound_of_terminal_plateau (γ : OrderParameter) {a c : ℝ} (ha : a < 1)
    (hc : ∀ t ∈ Ioo a 1, extend γ.val t=c) : ∀ t : Time, γ.val t ≤ c := by
  intro t
  let s : ℝ := (max (t:ℝ) a+1)/2
  have hm : max (t:ℝ) a < 1 := max_lt t.property.2 ha
  have hts : (t:ℝ) ≤ s := by dsimp [s];linarith [le_max_left (t:ℝ) a]
  have has : a < s := by dsimp [s];linarith [le_max_right (t:ℝ) a]
  have hs1 : s < 1 := by dsimp [s];linarith
  have hs : s ∈ Ico (0:ℝ) 1 := ⟨t.property.1.trans hts,hs1⟩
  have hh := hc s ⟨has,hs1⟩
  rw [extend,dite_eq_left hs] at hh
  exact (γ.monotone (a := t) (b := ⟨s,hs⟩) hts).trans_eq hh

lemma finite_terminal_curvature_bound {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) {D t b : ℝ}
    (ht0 : 0 ≤ t) (htb : t < b) (hb : b ≤ (N:ℝ)*h) (hD : 0 ≤ D)
    (hc : ∀ r ∈ Icc t b, finiteCoeff c h N i r ≤ D)
    (hsmall : 8*kernelConstant*D*Real.sqrt (b-t) ≤ 1/2) (x : ℝ) :
    |deriv (deriv (finiteValue c h f N i t)) x| ≤ 2*kernelConstant/Real.sqrt (b-t) := by
  let V := fun r => deriv (finiteValue c h f N i r)
  let G := finiteBurgersSource c h f N i
  have hV := finiteGradient_family hf hLip c h N i
  have hG := finiteBurgersSource_family hf hLip c h N i
  obtain ⟨A₀,hA₀⟩ := hG.bound
  obtain ⟨B₀,hB₀⟩ := hG.deriv.bound
  obtain ⟨C₀,hC₀⟩ := hV.deriv.bound
  have hu (r x : ℝ) : |V r x| ≤ 1 := by
    simpa only [V,Real.norm_eq_abs,NNReal.coe_one] using
      norm_deriv_le_of_lipschitz (x₀ := x) (finiteValue_lipschitz hLip c h N i r)
  have hsource (r : ℝ) (hr : r ∈ Icc t b) (z : ℝ) : |G r z| ≤ D*|deriv (V r) z|+0 := by
    have hh := iteratedDeriv_finiteBurgersSource_bound hf hLip c h N i 0
      (by norm_num : (0:ℝ) ≤ 1) hD (hc r hr) (fun j hj y => by
        have hj0 : j=0 := Nat.eq_zero_of_le_zero hj
        subst j
        exact hu r y) z
    simpa only [G,V,iteratedDeriv_zero,iteratedDeriv_one,Finset.range_zero,Finset.sum_empty,mul_zero,zero_mul] using hh
  have hh := uniform_gradient_bound_of_mild htb (by norm_num : (0:ℝ) ≤ 1) hD (by norm_num : (0:ℝ) ≤ 0)
    (hV.regular b) hG.measurable hG.regular hA₀ hB₀ (fun r _ z => hC₀ r z) (hu b) hsource
    (fun r hr z => finiteGradient_mild hf hLip c h N i (ht0.trans hr.1) hr.2.le hb z) hsmall x
  simpa only [V,mul_zero,zero_mul,add_zero,mul_one] using hh

lemma approxGamma_global_cap (γ : OrderParameter) {D : ℝ} (hcap : ∀ t : Time, γ.val t ≤ D)
    (n : ℕ) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) : approxGamma γ n s ≤ D := by
  obtain ⟨j,hj,he,_,_⟩ := finiteCoeff_sample (approxCoeff γ n) (approxMesh_pos n) (n+1) 0 hs.1
    (by rw [approxMesh_horizon];exact hs.2) (by omega)
  change finiteCoeff (approxCoeff γ n) (approxMesh n) (n+1) 0 s ≤ D
  rw [he]
  simpa only [Nat.zero_add,approxCoeff_eq γ n j hj] using hcap ⟨(j:ℝ)*approxMesh n,sample_mem n j hj⟩

lemma curvature_terminal_bound (W : BrownianSystem Ω) (γ : OrderParameter) {D t : ℝ}
    (hD : 0 ≤ D) (hcap : ∀ s : Time, γ.val s ≤ D) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hsmall : 8*kernelConstant*D*Real.sqrt (1-t) ≤ 1/2) (x : ℝ) :
    |curvature W γ t x| ≤ 2*kernelConstant/Real.sqrt (1-t) := by
  have hl := (approxValue_derivative_uniform_spatial W γ ht0 ht1 2).tendsto_at x |>.abs
  have hb (n : ℕ) : |iteratedDeriv 2 (approxValue γ n t) x| ≤ 2*kernelConstant/Real.sqrt (1-t) := by
    have hh := finite_terminal_curvature_bound (regularDatum_softAbs (M := ((n+1:ℕ):ℝ)) (by positivity)) (softAbs_lipschitz (M := ((n+1:ℕ):ℝ)) (by positivity))
      (approxCoeff γ n) (approxMesh n) (n+1) 0 ht0 ht1 (by rw [approxMesh_horizon]) hD
      (fun r hr => approxGamma_global_cap γ hcap n ⟨ht0.trans hr.1,hr.2⟩) hsmall x
    simpa only [approxValue,iteratedDeriv_succ,iteratedDeriv_zero] using hh
  have hh := le_of_tendsto hl (Eventually.of_forall hb)
  unfold curvature gradient
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hh

lemma gradient_terminal_small (W : BrownianSystem Ω) (γ : OrderParameter) {D t y : ℝ}
    (hD : 0 ≤ D) (hcap : ∀ s : Time, γ.val s ≤ D) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hsmall : 8*kernelConstant*D*Real.sqrt (1-t) ≤ 1/2)
    (hy : |y| ≤ Real.sqrt (1-t)/(4*kernelConstant+2)) :
    |gradient W γ t y| ≤ 1/2 := by
  have hκ := kernelConstant_nonneg
  have hden : 0 < 4*kernelConstant+2 := by positivity
  have hroot := Real.sqrt_pos.mpr (sub_pos.mpr ht1)
  have hd : Differentiable ℝ (gradient W γ t) := by
    unfold gradient
    simpa only [iteratedDeriv_one] using (value_contDiff W γ ht0 ht1).differentiable_iteratedDeriv 1 (by simp)
  have hL := (lipschitzWith_of_nnnorm_deriv_le hd (C := Real.toNNReal (2*kernelConstant/Real.sqrt (1-t))) (fun x => by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ (by positivity)]
    exact curvature_terminal_bound W γ hD hcap ht0 ht1 hsmall x))
  have hh := hL.norm_sub_le y 0
  rw [gradient_zero W γ ht0 ht1,sub_zero,Real.norm_eq_abs,sub_zero,Real.norm_eq_abs,
    Real.coe_toNNReal _ (by positivity)] at hh
  apply hh.trans
  calc
    (2*kernelConstant/Real.sqrt (1-t))*|y| ≤ (2*kernelConstant/Real.sqrt (1-t))*(Real.sqrt (1-t)/(4*kernelConstant+2)) :=
      mul_le_mul_of_nonneg_left hy (by positivity)
    _ = 2*kernelConstant/(4*kernelConstant+2) := by field_simp
    _ ≤ 1/2 := by apply (div_le_iff₀ hden).mpr;linarith

end ZeroTemperatureSK

end
end

end OAI
