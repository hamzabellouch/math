import Mathlib
import OAI.Probability.Perceptron.Variational.CoupledDual
import OAI.Probability.Perceptron.Variational.UniformGrid

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma varianceLevels_gridVariance {k : ℕ} (l : List (Fin (k+2)×ℝ)) (i : Fin (k+1)) :
    varianceLevels (fun j => gridVariance l j.castSucc) i =
      (l.map fun c => if c.1 ≤ i.castSucc then c.2 else 0).sum/2 := by
  unfold varianceLevels
  congr 1
  have H := gridVariance_weighted_sum l (fun j => if j ≤ i.castSucc then 1 else 0)
  simp only [ite_mul,one_mul,zero_mul] at H
  rw [Fin.sum_univ_castSucc] at H
  simpa only [Fin.castSucc_le_castSucc_iff,ite_eq_right (not_le.mpr (Fin.castSucc_lt_last i)),add_zero] using H

lemma grid_prefix_step_gap {k N : ℕ} (A B : Fin N → Fin (k+2)) (v : Fin N → ℝ)
    (hv : ∀ r, 0 ≤ v r) (hAB : ∀ r, A r ≤ B r)
    (hBA : ∀ r, (B r).val ≤ (A r).val+1) (i : Fin (k+1)) :
    let hA := varianceLevels (fun j => gridVariance (List.ofFn fun r => (A r,v r)) j.castSucc)
    let hB := varianceLevels (fun j => gridVariance (List.ofFn fun r => (B r,v r)) j.castSucc)
    0 ≤ hA i-hB i ∧ hA i-hB i ≤
      gridVariance (List.ofFn fun r => (A r,v r)) i.castSucc/2 := by
  dsimp only
  rw [varianceLevels_gridVariance,varianceLevels_gridVariance]
  simp only [gridVariance,List.map_ofFn,List.sum_ofFn]
  rw [← sub_div,← Finset.sum_sub_distrib]
  have H (r : Fin N) :
      0 ≤ (if A r ≤ i.castSucc then v r else 0)-(if B r ≤ i.castSucc then v r else 0) ∧
      (if A r ≤ i.castSucc then v r else 0)-(if B r ≤ i.castSucc then v r else 0) ≤
        if A r=i.castSucc then v r else 0 := by
    by_cases ha : A r ≤ i.castSucc
    · by_cases hb : B r ≤ i.castSucc
      · simp only [ite_eq_left ha,ite_eq_left hb,sub_self]
        constructor
        · rfl
        · split_ifs <;> first | exact hv r | rfl
      · have he : A r=i.castSucc := by
          apply Fin.ext
          have h₁ := hBA r
          have h₂ : (A r).val ≤ i.val := ha
          have h₃ : i.val < (B r).val := lt_of_not_ge hb
          omega
        simp [hb,he,hv r]
    · have hb : ¬B r ≤ i.castSucc := fun hb => ha ((hAB r).trans hb)
      have he : A r ≠ i.castSucc := fun he => ha he.le
      simp [ha,hb,he]
  exact ⟨div_nonneg (Finset.sum_nonneg (fun r _ => (H r).1)) (by norm_num),
    div_le_div_of_nonneg_right (Finset.sum_le_sum (fun r _ => (H r).2)) (by norm_num)⟩

lemma grid_step_weighted_gap {k N : ℕ} (A B : Fin N → Fin (k+2)) (v : Fin N → ℝ)
    (hv : ∀ r, 0 ≤ v r) (hAB : ∀ r, A r ≤ B r)
    (hBA : ∀ r, (B r).val ≤ (A r).val+1) :
    (∑ i, uniformWeights k i *
      |varianceLevels (fun j => gridVariance (List.ofFn fun r => (A r,v r)) j.castSucc) i-
       varianceLevels (fun j => gridVariance (List.ofFn fun r => (B r,v r)) j.castSucc) i|) ≤
      (∑ r, v r)/(2*(k+1:ℕ)) := by
  have hV : ∀ c ∈ List.ofFn (fun r => (A r,v r)), 0 ≤ c.2 := by
    intro c hc; obtain ⟨r,rfl⟩ := List.mem_ofFn.mp hc; exact hv r
  calc
    _ ≤ ∑ i : Fin (k+1), uniformWeights k i *
        (gridVariance (List.ofFn fun r => (A r,v r)) i.castSucc/2) := by
      apply Finset.sum_le_sum
      intro i _
      have H := grid_prefix_step_gap A B v hv hAB hBA i
      rw [abs_of_nonneg H.1]
      exact mul_le_mul_of_nonneg_left H.2 (uniformWeights_pos k i).le
    _ = (∑ i : Fin (k+1), gridVariance (List.ofFn fun r => (A r,v r)) i.castSucc)/(2*(k+1:ℕ)) := by
      simp only [uniformWeights]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ (∑ i, gridVariance (List.ofFn fun r => (A r,v r)) i)/(2*(k+1:ℕ)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [Fin.sum_univ_castSucc (gridVariance (List.ofFn fun r => (A r,v r)))]
      exact le_add_of_nonneg_right (gridVariance_nonneg _ hV _)
    _ = _ := by rw [gridVariance_sum,List.map_ofFn,List.sum_ofFn]; rfl

lemma sphericalGridDual_step_gap {k N : ℕ} (A B : Fin N → Fin (k+2)) (v : Fin N → ℝ)
    (hv : ∀ r, 0 ≤ v r) (hAB : ∀ r, A r ≤ B r)
    (hBA : ∀ r, (B r).val ≤ (A r).val+1) :
    |sphericalGridDual k (gridVariance (List.ofFn fun r => (A r,v r)))-
     sphericalGridDual k (gridVariance (List.ofFn fun r => (B r,v r)))| ≤
      (∑ r, v r)/(2*(k+1:ℕ)) := by
  have hVA : ∀ i, 0 ≤ gridVariance (List.ofFn fun r => (A r,v r)) i := by
    apply gridVariance_nonneg
    intro c hc; obtain ⟨r,rfl⟩ := List.mem_ofFn.mp hc; exact hv r
  have hVB : ∀ i, 0 ≤ gridVariance (List.ofFn fun r => (B r,v r)) i := by
    apply gridVariance_nonneg
    intro c hc; obtain ⟨r,rfl⟩ := List.mem_ofFn.mp hc; exact hv r
  exact (finiteSphericalDual_abs_sub_le (uniformWeights k) _ _ (uniformWeights_pos k)
    (uniformWeights_sum k)
    (varianceLevels_monotone _ (fun i => hVA i.castSucc))
    (varianceLevels_nonneg _ (fun i => hVA i.castSucc) 0)
    (varianceLevels_monotone _ (fun i => hVB i.castSucc))
    (varianceLevels_nonneg _ (fun i => hVB i.castSucc) 0)).trans
    (grid_step_weighted_gap A B v hv hAB hBA)

end SphericalPerceptronFreeEnergy
end

end OAI
