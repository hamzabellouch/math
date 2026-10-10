import OAI.Dynamics.StandardMap.TruncationArrays

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma capG_linear_near_unit {α q:ℝ} {d:DistanceArray} (hx:unitDefect d<q) (hq:q≤1/10000) :
    capG α d=α*arrayJ 0 (dyadicInt 2) d := by
  have hj:=arrayJ_nonneg 0 (dyadicInt 2) (by norm_num) d
  have hm: max (arrayShortfall 0 (dyadicInt 1) d) (arrayShortfall (dyadicInt 1) (dyadicInt 2) d)+arrayJ 0 (dyadicInt 2) d<q := hx
  have h1:arrayShortfall 0 (dyadicInt 1) d≤1/10000 := by linarith [le_max_left (arrayShortfall 0 (dyadicInt 1) d) (arrayShortfall (dyadicInt 1) (dyadicInt 2) d)]
  have h2:arrayShortfall (dyadicInt 1) (dyadicInt 2) d≤1/10000 := by linarith [le_max_right (arrayShortfall 0 (dyadicInt 1) d) (arrayShortfall (dyadicInt 1) (dyadicInt 2) d)]
  have h3:arrayShortfall 0 (dyadicInt 2) d≤1/10000 := by
    simp only [arrayJ,dyadicMid_zero_two] at hm
    linarith [le_max_left (arrayShortfall 0 (dyadicInt 1) d) (arrayShortfall (dyadicInt 1) (dyadicInt 2) d),le_max_right (arrayShortfall 0 (dyadicInt 1) d) (arrayShortfall (dyadicInt 1) (dyadicInt 2) d)]
  simp only [capG,entropyCap_linear h1,entropyCap_linear h2,entropyCap_linear h3,arrayJ,dyadicMid_zero_two]
  ring
lemma cut_alignment (p b:ℕ) (hb:b≤p) :
    ((2^p:ℕ):ℝ)*(cutLeft b:ℝ)=(((2^p:ℤ)-2^(p-b)):ℝ) ∧
    ((2^p:ℕ):ℝ)*(cutRight b:ℝ)=(((2^p:ℤ)-2^(p-b)):ℝ)+2*((2^(p-b):ℕ):ℝ) := by
  have he:(2:ℝ)^p/(2:ℝ)^b=(2:ℝ)^(p-b) := by rw [div_eq_mul_inv,←pow_sub₀ (2:ℝ) (by norm_num) hb]
  rw [cutLeft_val,cutRight_val]
  push_cast
  constructor
  · rw [mul_sub,mul_one,mul_one_div,he]
  · rw [mul_add,mul_one,mul_one_div,he]; ring
lemma integral_cut_test (k:ℝ) (hk:0≤k) (p b l:ℕ) (hb:b≤p) (ε:ℝ) (hε:0<ε) :
    (∫d,arrayTest ⟨(cutLeft b,cutRight b),cut_order b⟩ d ∂scaleLaw k hk p l ε)≤9*meanDeficit k (2^(p-b+l))/ε := by
  have h:=integral_test_scalelaw k hk p l ε hε (cutLeft b) (cutRight b) (cut_order b)
    ((2^p:ℤ)-2^(p-b)) (2^(p-b)) (by positivity) (by simpa only [Int.cast_sub,Int.cast_pow,Int.cast_ofNat] using (cut_alignment p b hb).1) (by simpa only [Int.cast_sub,Int.cast_pow,Int.cast_ofNat] using (cut_alignment p b hb).2)
  simpa only [pow_add] using h
lemma weight_unit_scale_bound (k:ℝ) (hk:0≤k) (p b l:ℕ) (hb:b≤p) (ε:ℝ) (hε:0<ε)
    {α:ℝ} (hα:0≤α) (hq:1/(2:ℝ)^b≤1/10000) (F:DistanceArray→ℝ) (hF:Continuous F)
    (hFB:∀d,F d≤|capG α d|) (hz:∀d,¬unitDefect d<1/(2:ℝ)^b → F d=0) :
    (∫d,F d ∂scaleLaw k hk p l ε)≤
      α*((1/(2:ℝ)^b)*(9*meanDeficit k (2^(p-b+l))/ε)+6/(((2^p:ℕ):ℝ)*ε)) := by
  let Jc:DistanceArray→ℝ:=arrayJ (cutLeft b) (cutRight b)
  have hB (j:ℕ) (z:Torus):F (sampleArray k hk z (2^(p+j)) (by positivity))≤
      α*((1/(2:ℝ)^b)*Jc (sampleArray k hk z (2^(p+j)) (by positivity))+3/(2:ℝ)^(p+j)) := by
    let d:=sampleArray k hk z (2^(p+j)) (by positivity)
    by_cases hx:unitDefect d<1/(2:ℝ)^b
    · have ht:=truncation_array_bound k hk z (p+j) b (by omega) hx
      have hg:|capG α d|=α*arrayJ 0 (dyadicInt 2) d := by
        rw [capG_linear_near_unit hx hq,abs_of_nonneg (mul_nonneg hα (arrayJ_nonneg _ _ (by norm_num) d))]
      exact (hFB d).trans (hg.le.trans (mul_le_mul_of_nonneg_left ht hα))
    · rw [hz d hx]
      exact mul_nonneg hα (add_nonneg (mul_nonneg (by positivity) (arrayJ_nonneg _ _ (cut_order b) d)) (by positivity))
  have hsamp (j:ℕ):(∫d,F d ∂sampleLaw k hk (2^(p+j)) (by positivity))≤
      α*((1/(2:ℝ)^b)*(∫d,Jc d ∂sampleLaw k hk (2^(p+j)) (by positivity))+3/(2:ℝ)^(p+j)) := by
    rw [integral_sampleLaw _ _ _ _ _ hF,integral_sampleLaw _ _ _ _ _ (continuous_arrayJ _ _)]
    have hc:Continuous (fun z:Torus => Jc (sampleArray k hk z (2^(p+j)) (by positivity))) :=
      (continuous_arrayJ _ _).comp (continuous_sampleArray _ _ _ _)
    have h:=integral_mono (μ:=area) ((hF.comp (continuous_sampleArray _ _ _ _)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (((hc.const_mul _).add continuous_const).const_mul α |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (hB j)
    have hi : Integrable (fun z:Torus => Jc (sampleArray k hk z (2^(p+j)) (by positivity))) area := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    simp only [Function.comp_apply,Pi.add_apply] at h
    simpa [integral_const_mul,integral_add (hi.const_mul _) (integrable_const _)] using h
  have hsum: (∑j∈Finset.range l,∫d,F d ∂sampleLaw k hk (2^(p+j)) (by positivity)) ≤
      α*((1/(2:ℝ)^b)*(∑j∈Finset.range l,∫d,Jc d ∂sampleLaw k hk (2^(p+j)) (by positivity))+6/((2^p:ℕ):ℝ)) := by
    have h:=Finset.sum_le_sum (fun j (_:j∈Finset.range l) => hsamp j)
    simp only [Finset.sum_add_distrib,←Finset.mul_sum] at h
    have herr:(∑j∈Finset.range l,3/(2:ℝ)^(p+j))≤6/((2^p:ℕ):ℝ) := by
      have he:∀j:ℕ,3/(2:ℝ)^(p+j)=3*(1/(((2^p)*2^j:ℕ):ℝ)) := by intro j; push_cast; rw [pow_add]; ring
      simp_rw [he]; rw [←Finset.mul_sum]
      have h:=sum_scaled_inverse (2^p) l (by positivity)
      convert! mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ)≤3) using 1 ; ring
    exact h.trans (mul_le_mul_of_nonneg_left (add_le_add_right herr _) hα)
  rw [integral_scaleLaw _ _ _ _ _ hε F hF]
  have hJ : (∫d,Jc d ∂scaleLaw k hk p l ε)≤9*meanDeficit k (2^(p-b+l))/ε := by
    refine (integral_mono ((continuous_arrayJ _ _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((continuous_arrayTest _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (fun d => ?_)).trans (integral_cut_test k hk p b l hb ε hε)
    exact le_add_of_nonneg_right (arrayV_nonneg _ _ d)
  rw [integral_scaleLaw _ _ _ _ _ hε Jc (continuous_arrayJ _ _)] at hJ
  have hh:=div_le_div_of_nonneg_right hsum hε.le
  apply hh.trans
  have hmul:=mul_le_mul_of_nonneg_left hJ (mul_nonneg hα (by positivity : 0≤1/(2:ℝ)^b))
  calc
    _ = α*(1/(2:ℝ)^b)*((∑j∈Finset.range l,∫d,Jc d ∂sampleLaw k hk (2^(p+j)) (by positivity))/ε)+α*(6/(((2^p:ℕ):ℝ)*ε)) := by ring
    _ ≤ _ := by nlinarith
end StandardMapEntropy

end OAI
