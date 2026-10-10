import Mathlib

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FiniteFieldConcentration
open Classical MeasureTheory ProbabilityTheory
open scoped NNReal

theorem subgaussian_parameter_mono {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {c d : ℝ≥0} (h : HasSubgaussianMGF X c μ) (hcd : c≤d) :
    HasSubgaussianMGF X d μ where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := (h.mgf_le t).trans (Real.exp_le_exp.mpr (by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hcd) (sq_nonneg t)) (by norm_num)))

theorem finite_weighted_noise_tail {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (hind : iIndepFun X μ)
    (hm : ∀i,AEMeasurable (X i) μ) (hb : ∀i,∀ᵐω ∂μ,X i ω∈Set.Icc (-1:ℝ) 1)
    (hc : ∀i,∫ω,X i ω ∂μ=0) (S : Finset ι) (b : ι → ℝ)
    {V ε : ℝ} (hV : 0≤V) (he : ∑i∈S,(b i)^2 ≤ V) (hε : 0≤ε) :
    μ.real {ω | ε ≤ |∑i∈S,b i*X i ω|} ≤ 2*Real.exp (-ε^2/(2*V)) := by
  have hsub (i : ι) : HasSubgaussianMGF (X i) 1 μ := by
    have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hm i) (hb i) (hc i)
    norm_num at h
    exact h
  have hi := hind.comp (fun i x => b i*x) (fun i => measurable_const.mul measurable_id)
  have hs : HasSubgaussianMGF (fun ω => ∑i∈S,b i*X i ω)
      (∑i∈S,NNReal.mk ((b i)^2) (sq_nonneg _)) μ := by
    apply HasSubgaussianMGF.sum_of_iIndepFun hi
    intro i hi
    have h := (hsub i).const_mul (b i)
    change HasSubgaussianMGF (fun ω => b i*X i ω) ((NNReal.mk ((b i)^2) (sq_nonneg _))*1) μ at h
    simpa only [mul_one,Function.comp_def] using h
  have hv : HasSubgaussianMGF (fun ω => ∑i∈S,b i*X i ω) (NNReal.mk V hV) μ := by
    apply subgaussian_parameter_mono hs
    apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_sum,NNReal.coe_mk] using he
  have hset : {ω | ε ≤ |∑i∈S,b i*X i ω|} ⊆
      {ω | ε ≤ ∑i∈S,b i*X i ω} ∪ {ω | ε ≤ -(∑i∈S,b i*X i ω)} := by
    intro ω hω
    change ε ≤ |∑i∈S,b i*X i ω| at hω
    rcases le_abs.mp hω with h|h
    · exact Or.inl h
    · exact Or.inr h
  have hh := (measureReal_mono (μ:=μ) hset).trans (measureReal_union_le _ _)
  have hpos := hv.measure_ge_le hε
  have hneg := hv.neg.measure_ge_le hε
  dsimp at hpos hneg
  linarith

theorem finite_matrix_noise_tail {Ω ι ζ : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (hind : iIndepFun X μ)
    (hm : ∀i,AEMeasurable (X i) μ) (hb : ∀i,∀ᵐω ∂μ,X i ω∈Set.Icc (-1:ℝ) 1)
    (hc : ∀i,∫ω,X i ω ∂μ=0) (S : Finset ι) (T : Finset ζ) (B : ζ → ι → ℝ)
    {V ε : ℝ} (hV : 0≤V) (he : ∀z∈T,∑i∈S,(B z i)^2 ≤ V) (hε : 0≤ε) :
    μ.real {ω | ∃z∈T,ε ≤ |∑i∈S,B z i*X i ω|} ≤
      2*(T.card:ℝ)*Real.exp (-ε^2/(2*V)) := by
  have heq : {ω | ∃z∈T,ε ≤ |∑i∈S,B z i*X i ω|}=
      ⋃z∈T,{ω | ε ≤ |∑i∈S,B z i*X i ω|} := by ext; simp
  rw [heq]
  calc
    _ ≤ ∑z∈T,μ.real {ω | ε ≤ |∑i∈S,B z i*X i ω|} := measureReal_biUnion_finset_le _ _
    _ ≤ ∑_z∈T,2*Real.exp (-ε^2/(2*V)) := Finset.sum_le_sum (fun z hz =>
      finite_weighted_noise_tail μ X hind hm hb hc S (B z) hV (he z hz) hε)
    _ = _ := by simp; ring

end FiniteFieldConcentration

end SimpleAmenable
end
end

end OAI
