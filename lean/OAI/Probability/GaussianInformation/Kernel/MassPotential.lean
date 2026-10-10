import Mathlib
import OAI.Probability.GaussianInformation.Kernel.OutgoingLaws

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.MassPotential
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Coercivity Sphere
noncomputable def normalized {d : ℕ} (ρ : Measure (Ambient d)) : Measure (Ambient d) := (ρ univ)⁻¹ • ρ
noncomputable def energy {d : ℕ} (ρ : Measure (Ambient d)) : ℝ := (ρ univ).toReal*Phi (normalized ρ)
noncomputable def proper {d : ℕ} (ρ : Measure (Ambient d)) : Measure (Ambient d) :=
  if ρ univ=0 then sphereProbability d else normalized ρ
lemma normalized_probability {d : ℕ} (ρ : Measure (Ambient d)) [IsFiniteMeasure ρ] (hρ : ρ univ≠0) :
    IsProbabilityMeasure (normalized ρ) := by
  constructor
  simp only [normalized,Measure.smul_apply,smul_eq_mul]
  exact ENNReal.inv_mul_cancel hρ (measure_ne_top _ _)
lemma proper_probability {d : ℕ} (ρ : Measure (Ambient d)) [IsFiniteMeasure ρ] : IsProbabilityMeasure (proper ρ) := by
  unfold proper
  split_ifs with h
  · infer_instance
  · exact normalized_probability ρ h
lemma proper_bounded {d : ℕ} (ρ : Measure (Ambient d)) [IsFiniteMeasure ρ] (hρ : ρ ≤ sphereProbability d) :
    BoundedDensity (proper ρ) := by
  unfold proper
  split_ifs with h
  · exact ⟨1,zero_lt_one,by simp⟩
  · have hp : 0 < (ρ univ).toReal := ENNReal.toReal_pos h (measure_ne_top _ _)
    refine ⟨1/(ρ univ).toReal,one_div_pos.mpr hp,?_⟩
    unfold normalized
    have he : ENNReal.ofReal (1/(ρ univ).toReal)=(ρ univ)⁻¹ := by
      rw [one_div,ENNReal.ofReal_inv_of_pos hp,ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [he]
    exact smul_le_smul_left _ hρ
lemma mass_smul_proper {d : ℕ} (ρ : Measure (Ambient d)) [IsFiniteMeasure ρ] :
    ENNReal.ofReal (ρ univ).toReal • proper ρ=ρ := by
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  by_cases h : ρ univ=0
  · rw [h,zero_smul]
    exact (Measure.measure_univ_eq_zero.mp h).symm
  · rw [proper,ite_eq_right h,normalized,smul_smul,ENNReal.mul_inv_cancel h (measure_ne_top _ _),one_smul]
lemma energy_proper {d : ℕ} (ρ : Measure (Ambient d)) : energy ρ=(ρ univ).toReal*Phi (proper ρ) := by
  unfold energy proper
  split_ifs with h
  · simp [h]
  · rfl
lemma energy_smul_probability {d : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (a : ℝ) (ha : 0 ≤ a) : energy (ENNReal.ofReal a • ν)=a*Phi ν := by
  by_cases haz : a=0
  · simp [haz,energy,normalized]
  · have hp := lt_of_le_of_ne ha (Ne.symm haz)
    have hz : ENNReal.ofReal a≠0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp)
    have hu : (ENNReal.ofReal a • ν) univ=ENNReal.ofReal a := by simp
    unfold energy normalized
    rw [hu,ENNReal.toReal_ofReal ha,smul_smul,ENNReal.inv_mul_cancel hz ENNReal.ofReal_ne_top,one_smul]
lemma energy_mixture {d q : ℕ} (hd : 16 ≤ d) (ρ : Fin q → Measure (Ambient d))
    (hρf : ∀ i,IsFiniteMeasure (ρ i)) (hρ : ∀ i,ρ i ≤ sphereProbability d) :
    energy (∑ i,ρ i) ≤ ∑ i,energy (ρ i) := by
  have (i : Fin q) : IsFiniteMeasure (ρ i) := hρf i
  let a := fun i => (ρ i univ).toReal
  let A := ∑ i,a i
  have ha (i) : 0 ≤ a i := ENNReal.toReal_nonneg
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => ha i)
  have he : (∑ i,ρ i) univ=ENNReal.ofReal A := by
    rw [Measure.finsetSum_apply]
    dsimp [A,a]
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => ENNReal.toReal_nonneg)]
    apply Finset.sum_congr rfl
    intro i _
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hrepr : (∑ i,ENNReal.ofReal (a i) • proper (ρ i))=∑ i,ρ i := by
    apply Finset.sum_congr rfl
    intro i _
    exact mass_smul_proper (ρ i)
  by_cases hAz : A=0
  · have haz (i) : a i=0 := by
      have hh : a i ≤ A := Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)
      rw [hAz] at hh
      exact le_antisymm hh (ha i)
    simp only [energy_proper]
    rw [he,hAz,ENNReal.ofReal_zero,ENNReal.toReal_zero,zero_mul]
    change 0 ≤ ∑ i,a i*Phi (proper (ρ i))
    simp [haz]
  · have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
    let w := fun i => a i/A
    have hw (i) : 0 ≤ w i := div_nonneg (ha i) hA
    have hw1 : ∑ i,w i=1 := by simp [w,← Finset.sum_div,A,hAz]
    have hnorm : normalized (∑ i,ρ i)=∑ i,ENNReal.ofReal (w i) • proper (ρ i) := by
      rw [normalized,he,← hrepr,Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul]
      congr 1
      dsimp [w]
      rw [ENNReal.ofReal_div_of_pos hAp,div_eq_mul_inv,mul_comm]
    have hh := finite_convexity hd q w hw hw1 (fun i => proper (ρ i))
      (fun i => proper_probability _) (fun i => proper_bounded _ (hρ i))
    have := mul_le_mul_of_nonneg_left hh hA
    rw [← hnorm] at this
    calc energy (∑ i,ρ i) = A*Phi (normalized (∑ i,ρ i)) := by
           rw [energy,he,ENNReal.toReal_ofReal hA]
         _ ≤ ∑ i,a i*Phi (proper (ρ i)) := by
           simpa only [Finset.mul_sum,w,← mul_assoc,mul_div_cancel₀ _ hAz] using this
         _ = ∑ i,energy (ρ i) := by simp only [energy_proper,a]
end KernelPotential.MassPotential

end OAI
