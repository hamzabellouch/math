import Mathlib
import OAI.Probability.SphericalField.Fields.Transport

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

lemma integral_finite_label {I : Type*} [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (a : Time → I) (ha : Measurable a) (F : I → ℝ) :
    (∫ u, F (a u) ∂timeLaw)=∑ i, timeLaw.real (a ⁻¹' {i})*F i := by
  classical
  have he (u : Time) : F (a u)=∑ i, (if a u=i then F i else 0) := by simp
  simp_rw [he]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    change (∫ u, (a ⁻¹' {i}).indicator (fun _ => F i) u ∂timeLaw)=_
    rw [integral_indicator (ha (measurableSet_singleton i)),integral_const]
    simp only [Measure.restrict_apply_univ,smul_eq_mul,Measure.real]
  · intro i _
    exact (integrable_const (F i)).indicator (ha (measurableSet_singleton i))

lemma FiniteFieldModel.weight_pos {f : Time → ℝ} (M : FiniteFieldModel f) (i : Fin (M.depth+1)) :
    0 < M.weight i := M.positive i

lemma FiniteFieldModel.weight_sum {f : Time → ℝ} (M : FiniteFieldModel f) : ∑ i, M.weight i=1 := by
  have h := integral_finite_label M.label M.measurable_label (fun _ => 1)
  simpa [FiniteFieldModel.weight] using h.symm

lemma FiniteFieldModel.integral {f : Time → ℝ} (M : FiniteFieldModel f) (F : ℝ → ℝ) :
    (∫ u, F (f u) ∂timeLaw)=∑ i, M.weight i*F (M.value i) := by
  unfold FiniteFieldModel.weight
  rw [← integral_finite_label M.label M.measurable_label (fun i => F (M.value i))]
  apply integral_congr_ae
  filter_upwards [M.agrees] with u hu
  rw [hu]

def FiniteFieldModel.coupling {f g : Time → ℝ} (M : FiniteFieldModel f) (N : FiniteFieldModel g)
    (a : Fin (M.depth+1)×Fin (N.depth+1)) : ℝ :=
  timeLaw.real ((fun u => (M.label u,N.label u)) ⁻¹' {a})

lemma FiniteFieldModel.coupling_nonneg {f g : Time → ℝ} (M : FiniteFieldModel f) (N : FiniteFieldModel g)
    (a : Fin (M.depth+1)×Fin (N.depth+1)) : 0 ≤ M.coupling N a := measureReal_nonneg

lemma FiniteFieldModel.coupling_fst {f g : Time → ℝ} (M : FiniteFieldModel f) (N : FiniteFieldModel g)
    (i : Fin (M.depth+1)) : ∑ j, M.coupling N (i,j)=M.weight i := by
  classical
  have h := integral_finite_label (fun u => (M.label u,N.label u))
    (M.measurable_label.prodMk N.measurable_label) (fun a => if a.1=i then 1 else 0)
  have he := integral_finite_label M.label M.measurable_label (fun a => if a=i then 1 else 0)
  simp only [FiniteFieldModel.coupling,FiniteFieldModel.weight] at *
  simp only [Fintype.sum_prod_type,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at h he
  rw [Finset.sum_comm] at h
  simpa only [Finset.sum_ite_eq',Finset.mem_univ,ite_true] using h.symm.trans he

lemma FiniteFieldModel.coupling_snd {f g : Time → ℝ} (M : FiniteFieldModel f) (N : FiniteFieldModel g)
    (j : Fin (N.depth+1)) : ∑ i, M.coupling N (i,j)=N.weight j := by
  classical
  have h := integral_finite_label (fun u => (M.label u,N.label u))
    (M.measurable_label.prodMk N.measurable_label) (fun a => if a.2=j then 1 else 0)
  have he := integral_finite_label N.label N.measurable_label (fun a => if a=j then 1 else 0)
  simp only [FiniteFieldModel.coupling,FiniteFieldModel.weight] at *
  simp only [Fintype.sum_prod_type,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at h he
  exact h.symm.trans he

lemma FiniteFieldModel.coupling_cost {f g : Time → ℝ} (M : FiniteFieldModel f) (N : FiniteFieldModel g) :
    (∑ a, M.coupling N a*|M.value a.1-N.value a.2|)=∫ u, |f u-g u| ∂timeLaw := by
  unfold FiniteFieldModel.coupling
  rw [← integral_finite_label (fun u => (M.label u,N.label u))
    (M.measurable_label.prodMk N.measurable_label) (fun a => |M.value a.1-N.value a.2|)]
  apply integral_congr_ae
  filter_upwards [M.agrees,N.agrees] with u hu hv
  rw [hu,hv]

lemma FiniteFieldModel.values_mem {f : Time → ℝ} (M : FiniteFieldModel f)
    {H : ℝ} (hf : ∀ᵐ u ∂timeLaw, f u ∈ Icc (0:ℝ) H) (i : Fin (M.depth+1)) :
    M.value i ∈ Icc (0:ℝ) H := by
  have hi : timeLaw (M.label ⁻¹' {i}) ≠ 0 := by
    intro hi
    have hp := M.positive i
    change 0 < (timeLaw (M.label ⁻¹' {i})).toReal at hp
    rw [hi] at hp
    simp at hp
  have hne : ∃ u, M.label u=i ∧ M.value (M.label u) ∈ Icc (0:ℝ) H := by
    by_contra! hn
    have hzero : ∀ᵐ u ∂timeLaw, u ∉ M.label ⁻¹' {i} := by
      filter_upwards [M.agrees,hf] with u hu hv
      intro hm
      exact hn u hm (hu ▸ hv)
    exact hi (by simpa only [not_not,Set.ofPred_mem_eq] using ae_iff.mp hzero)
  obtain ⟨u,hu,hv⟩ := hne
  simpa [hu] using hv

lemma FiniteFieldModel.pressure_bound {f g : Time → ℝ} (M : FiniteFieldModel f) (N : FiniteFieldModel g)
    {H : ℝ} (hH : 0 ≤ H) (hf : ∀ᵐ u ∂timeLaw, f u ∈ Icc (0:ℝ) H)
    (hg : ∀ᵐ u ∂timeLaw, g u ∈ Icc (0:ℝ) H) (n : ℕ) :
    |M.pressure n-N.pressure n| ≤ sphericalContinuityConstant n H*(∫ u, |f u-g u| ∂timeLaw) := by
  have h := finiteSphericalFieldValue_coupling_bound M.weight M.value N.weight N.value (M.coupling N)
    M.weight_pos M.weight_sum N.weight_pos N.weight_sum M.monotone_value (M.values_mem hf 0).1
    N.monotone_value (N.values_mem hg 0).1 (M.coupling_nonneg N) (M.coupling_fst N) (M.coupling_snd N)
    H hH (M.values_mem hf _).2 (N.values_mem hg _).2 n
  rwa [M.coupling_cost N] at h

end SphericalPerceptron
end
end

end OAI
