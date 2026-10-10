import Mathlib
import OAI.Probability.SKBarriers.Coverage.EnergyTail
import OAI.Probability.SKBarriers.Coverage.FiniteCoverage
import OAI.Probability.SKBarriers.Coverage.WeightedCoverage

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem finiteOverlapMass_mono {n : ℕ} (ν : Config n → ℝ)
    (hν : ∀ x, 0 ≤ ν x) {T S : Finset (Config n)} (hTS : T ⊆ S) (q : ℝ) :
    finiteOverlapMass ν T q ≤ finiteOverlapMass ν S q := by
  unfold finiteOverlapMass
  apply le_trans (Finset.sum_le_sum (g := fun x => ∑ y ∈ S,
    if q ≤ |overlap x y| then ν x*ν y else 0) (fun x _ => ?_))
  · exact Finset.sum_le_sum_of_subset_of_nonneg hTS (fun x _ _ =>
      Finset.sum_nonneg (fun y _ => by split_ifs; exact mul_nonneg (hν x) (hν y); rfl))
  · exact Finset.sum_le_sum_of_subset_of_nonneg hTS (fun y _ _ => by split_ifs; exact mul_nonneg (hν x) (hν y); rfl)

theorem weightedOverlapMass_conditional_mono {n : ℕ} (ν : Config n → ℝ)
    (hν : ∀ x, 0 ≤ ν x) {T S : Finset (Config n)} (hTS : T ⊆ S)
    (hT : 0 < finiteMass ν T) (q : ℝ) :
    weightedOverlapMass (conditionalWeights ν T) q ≤
      (finiteMass ν S/finiteMass ν T)^2*weightedOverlapMass (conditionalWeights ν S) q := by
  have hS : 0 < finiteMass ν S := hT.trans_le (finiteMass_mono ν hν hTS)
  rw [weightedOverlapMass_conditional,weightedOverlapMass_conditional]
  have HE : (finiteMass ν S/finiteMass ν T)^2*(finiteOverlapMass ν S q/(finiteMass ν S)^2) =
      finiteOverlapMass ν S q/(finiteMass ν T)^2 := by
    field_simp
  rw [HE]
  exact div_le_div_of_nonneg_right (finiteOverlapMass_mono ν hν hTS q) (sq_nonneg _)

def energyTrim {n : ℕ} (J : Disorder n) (e : ℝ) (S : Finset (Config n)) : Finset (Config n) :=
  S.filter (fun x => hamiltonian J x ≤ (n:ℝ)*e)

theorem gibbsMass_energyTrim {n : ℕ} (β e : ℝ) (J : Disorder n) (S : Finset (Config n)) :
    finiteMass (gibbs β J) S-gibbsEnergyTail β e J ≤
      finiteMass (gibbs β J) (energyTrim J e S) := by
  have Hadd := Finset.sum_filter_add_sum_filter_not S
    (fun x => hamiltonian J x ≤ (n:ℝ)*e) (gibbs β J)
  have Hle : (∑ x ∈ S.filter (fun x => ¬hamiltonian J x ≤ (n:ℝ)*e), gibbs β J x) ≤
      gibbsEnergyTail β e J := by
    unfold gibbsEnergyTail
    simp only [not_le]
    rw [Finset.sum_filter]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun x _ _ => by split_ifs; exact le_of_lt (gibbs_pos β J x); rfl)
  change (∑ x ∈ S, gibbs β J x)-gibbsEnergyTail β e J ≤
    ∑ x ∈ S.filter (fun x => hamiltonian J x ≤ (n:ℝ)*e), gibbs β J x
  linarith

theorem partition_ratio_mix {n : ℕ} (β a b : ℝ) (J G : Disorder n) :
    partition β (mixDisorder a b (J,G))/partition β J =
      ∑ x : Config n, gibbs β J x*
        Real.exp (β*(a-1)*hamiltonian J x+β*b*hamiltonian G x) := by
  unfold partition gibbs
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  rw [hamiltonian_mix]
  rw [div_mul_eq_mul_div,← Real.exp_add]
  congr 2
  ring

theorem conditionalWeightedPartition {n : ℕ} (ν : Config n → ℝ)
    (S : Finset (Config n)) (hS : 0 < finiteMass ν S) (b : ℝ) (G : Disorder n) :
    finiteMass ν S*weightedPartition (conditionalWeights ν S) b G =
      ∑ x ∈ S, ν x*Real.exp (b*hamiltonian G x) := by
  unfold weightedPartition conditionalWeights
  rw [Finset.mul_sum]
  have HE (x : Config n) : finiteMass ν S*((if x ∈ S then ν x/finiteMass ν S else 0)*
      Real.exp (b*hamiltonian G x)) =
      if x ∈ S then ν x*Real.exp (b*hamiltonian G x) else 0 := by
    split_ifs
    · field_simp
    · ring
  simp_rw [HE]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]

theorem partition_ratio_mix_lower {n : ℕ} {β a : ℝ} (hβ : 0 ≤ β) (ha : a ≤ 1)
    (b e : ℝ) (J G : Disorder n) (T : Finset (Config n))
    (hT : 0 < finiteMass (gibbs β J) T)
    (henergy : ∀ x ∈ T, hamiltonian J x ≤ (n:ℝ)*e) :
    finiteMass (gibbs β J) T*Real.exp (β*(a-1)*(n:ℝ)*e)*
      weightedPartition (conditionalWeights (gibbs β J) T) (β*b) G ≤
        partition β (mixDisorder a b (J,G))/partition β J := by
  rw [partition_ratio_mix]
  calc
    _ = Real.exp (β*(a-1)*(n:ℝ)*e)*
        ∑ x ∈ T, gibbs β J x*Real.exp ((β*b)*hamiltonian G x) := by
      rw [← conditionalWeightedPartition (gibbs β J) T hT]
      ring
    _ ≤ ∑ x ∈ T, gibbs β J x*
        Real.exp (β*(a-1)*hamiltonian J x+β*b*hamiltonian G x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro x hx
      rw [Real.exp_add]
      have he : β*(a-1)*(n:ℝ)*e ≤ β*(a-1)*hamiltonian J x := by
        have HH := mul_le_mul_of_nonpos_left (henergy x hx)
          (mul_nonpos_of_nonneg_of_nonpos hβ (sub_nonpos.mpr ha))
        nlinarith
      have HH := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
        (mul_nonneg (gibbs_pos β J x).le (Real.exp_nonneg ((β*b)*hamiltonian G x)))
      nlinarith
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
      (fun x _ _ => mul_nonneg (gibbs_pos β J x).le (Real.exp_nonneg _))

theorem logPartition_mix_lower {n : ℕ} {β a : ℝ} (hβ : 0 ≤ β) (ha : a ≤ 1)
    (b e : ℝ) (J G : Disorder n) (T : Finset (Config n))
    (hT : 0 < finiteMass (gibbs β J) T)
    (henergy : ∀ x ∈ T, hamiltonian J x ≤ (n:ℝ)*e) :
    Real.log (finiteMass (gibbs β J) T)+β*(a-1)*(n:ℝ)*e+
      Real.log (weightedPartition (conditionalWeights (gibbs β J) T) (β*b) G) ≤
        logPartition β (mixDisorder a b (J,G))-logPartition β J := by
  have hw := weightedPartition_pos (conditionalWeights (gibbs β J) T)
    (conditionalWeights_nonneg (gibbs β J) (fun x => (gibbs_pos β J x).le) T)
    (conditionalWeights_sum (gibbs β J) T hT) (β*b) G
  have H := Real.log_le_log (mul_pos (mul_pos hT (Real.exp_pos _)) hw)
    (partition_ratio_mix_lower hβ ha b e J G T hT henergy)
  rw [Real.log_mul (mul_ne_zero hT.ne' (Real.exp_ne_zero _)) hw.ne',
    Real.log_mul hT.ne' (Real.exp_ne_zero _),Real.log_exp,
    Real.log_div (partition_pos β (mixDisorder a b (J,G))).ne' (partition_pos β J).ne'] at H
  exact H
end SK.Analytic

end
end

end

end OAI
