import Mathlib
import OAI.Probability.SphericalField.Fields.HeightCost
import OAI.Probability.SphericalField.Heat.WordStability

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

lemma finiteFieldCDFLeft_mem {d : ℕ} (w h : Fin (d+1) → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1) (t : ℝ) :
    finiteFieldCDFLeft w h t ∈ Icc (0:ℝ) 1 := by
  constructor
  · apply Finset.sum_nonneg
    intro i _
    split_ifs <;> first | exact hw i | rfl
  · rw [← hw1]
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> first | exact le_rfl | exact hw i

def sphericalContinuityConstant (n : ℕ) (H : ℝ) : ℝ :=
  2*gaussianEntropicParamConstant (stdGaussian (Spin (n+1)))
    |Real.sqrt (n+1:ℕ)| (Real.sqrt (2*H))/(n+1:ℕ)

lemma sphericalContinuityConstant_nonneg (n : ℕ) (H : ℝ) :
    0 ≤ sphericalContinuityConstant n H := by
  unfold sphericalContinuityConstant
  exact div_nonneg (mul_nonneg (by norm_num) (gaussianEntropicParamConstant_nonneg _ _ _)) (by positivity)

lemma sphericalHeatValue_parameter_bound (n N : ℕ) (a b σ : Fin N → ℝ) (S : ℝ)
    (ha : ∀ i, a i ∈ Icc (0:ℝ) 1) (hb : ∀ i, b i ∈ Icc (0:ℝ) 1)
    (hσ : ∀ i, σ i ∈ Icc (0:ℝ) S) :
    |sphericalHeatValue n (List.ofFn fun i => (a i,σ i))-
      sphericalHeatValue n (List.ofFn fun i => (b i,σ i))| ≤
      gaussianEntropicParamConstant (stdGaussian (Spin (n+1))) |Real.sqrt (n+1:ℕ)| S *
        (∑ i, (σ i)^2*|a i-b i|)/(n+1:ℕ) := by
  have H := gaussianBackward_ofFn_parameter_bound (stdGaussian (Spin (n+1)))
    (logSphericalExp_lipschitz n (Real.sqrt (n+1:ℕ))) N a b σ ha hb hσ 0
  have hn : (0:ℝ) < (n+1:ℕ) := by positivity
  have Hd := div_le_div_of_nonneg_right H hn.le
  have hs (x y c : ℝ) : |(x/(n+1:ℕ)-c)-(y/(n+1:ℕ)-c)|=|x-y|/(n+1:ℕ) := by
    rw [show (x/(n+1:ℕ)-c)-(y/(n+1:ℕ)-c)=(x-y)/(n+1:ℕ) by ring]
    rw [abs_div,abs_of_pos hn]
  simp only [sphericalHeatValue,List.map_ofFn,List.sum_ofFn,Function.comp_def,hs]
  convert Hd using 1
  rfl

theorem finiteSphericalFieldValue_coupling_bound {d e : ℕ} (w h : Fin (d+1) → ℝ)
    (v g : Fin (e+1) → ℝ) (c : Fin (d+1)×Fin (e+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1)
    (hv : ∀ j, 0 < v j) (hv1 : ∑ j, v j=1)
    (hh : Monotone h) (hh0 : 0 ≤ h 0) (hg : Monotone g) (hg0 : 0 ≤ g 0)
    (hcn : ∀ a, 0 ≤ c a) (hr : ∀ i, ∑ j, c (i,j)=w i) (hc : ∀ j, ∑ i, c (i,j)=v j)
    (H : ℝ) (hH : 0 ≤ H) (hhH : h (Fin.last d) ≤ H) (hgH : g (Fin.last e) ≤ H) (n : ℕ) :
    |finiteSphericalFieldValue n d w h-finiteSphericalFieldValue n e v g| ≤
      sphericalContinuityConstant n H*(∑ a, c a*|h a.1-g a.2|) := by
  have hhb : ∀ i, h i ∈ Icc (0:ℝ) H := fun i =>
    ⟨hh0.trans (hh (Fin.zero_le i)),(hh (Fin.le_last i)).trans hhH⟩
  have hgb : ∀ i, g i ∈ Icc (0:ℝ) H := fun i =>
    ⟨hg0.trans (hg (Fin.zero_le i)),(hg (Fin.le_last i)).trans hgH⟩
  obtain ⟨K,z,hz,hz0,hzH,hm,gm⟩ := exists_common_height_partition h g H hH hhb hgb
  rw [finiteSphericalFieldValue_height_word w h hw hw1 hh hh0 z hz hz0 hm n,
    finiteSphericalFieldValue_height_word v g hv hv1 hg hg0 z hz hz0 gm n]
  have hσ : ∀ j, Real.sqrt (heightVariances z j) ∈ Icc (0:ℝ) (Real.sqrt (2*H)) := by
    intro j
    refine ⟨Real.sqrt_nonneg _,Real.sqrt_le_sqrt ?_⟩
    have Hsum := heightVariances_sum z
    rw [hz0,hzH,sub_zero] at Hsum
    rw [← Hsum]
    exact Finset.single_le_sum (fun i _ => heightVariances_nonneg z hz i) (Finset.mem_univ j)
  have hp := sphericalHeatValue_parameter_bound n K _ _ _ (Real.sqrt (2*H))
    (fun j => finiteFieldCDFLeft_mem w h (fun i => (hw i).le) hw1 (z j.succ))
    (fun j => finiteFieldCDFLeft_mem v g (fun i => (hv i).le) hv1 (z j.succ)) hσ
  simp only [Real.sq_sqrt (heightVariances_nonneg z hz _)] at hp
  have hcst := gaussianEntropicParamConstant_nonneg (stdGaussian (Spin (n+1)))
    |Real.sqrt (n+1:ℕ)| (Real.sqrt (2*H))
  have hcost := finiteFieldCDFLeft_partition_cost w h v g c hcn hr hc z hz hm gm
  calc
    _ ≤ _ := hp
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcost hcst) (by positivity)
    _ = _ := by unfold sphericalContinuityConstant; ring

end SphericalPerceptron
end
end

end OAI
