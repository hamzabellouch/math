import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.WeightedMoments
import OAI.Probability.SKBarriers.Coverage.PaleyZygmund
import OAI.Probability.SKBarriers.Coverage.WeightedConcentration
import OAI.Probability.SKBarriers.Coverage.SubGaussianQuantile

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem weightedPartition_pos {n : ℕ} (ν : Config n → ℝ)
    (hνpos : ∀ x, 0 ≤ ν x) (hν : ∑ x, ν x = 1) (b : ℝ) (G : Disorder n) :
    0 < weightedPartition ν b G := by
  let : Weighted.Weights n := ⟨ν,hνpos,hν⟩
  exact Weighted.partition_pos b G

theorem continuous_weightedPartition {n : ℕ} (ν : Config n → ℝ) (b : ℝ) :
    Continuous (weightedPartition ν b) := by
  unfold weightedPartition
  exact continuous_finsetSum _ (fun x _ => continuous_const.mul
    (Real.continuous_exp.comp (continuous_const.mul (continuous_hamiltonian x))))

theorem weightedLogPartition_subGaussian {n : ℕ} (hn : 0 < n)
    (ν : Config n → ℝ) (hνpos : ∀ x, 0 ≤ ν x) (hν : ∑ x, ν x = 1) (b : ℝ) :
    HasSubgaussianMGF (fun G : Disorder n => Real.log (weightedPartition ν b G)-
      ∫ K, Real.log (weightedPartition ν b K) ∂disorderLaw n)
      (logPartitionProxy b n) (disorderLaw n) := by
  let : Weighted.Weights n := ⟨ν,hνpos,hν⟩
  exact Weighted.logPartition_subGaussian hn b

theorem weightedPartition_paleyZygmund {n : ℕ} (hn : 0 < n)
    (ν : Config n → ℝ) (hνpos : ∀ x, 0 ≤ ν x) (hν : ∑ x, ν x = 1)
    (b q : ℝ) (hq : 0 ≤ q)
    (hr : weightedOverlapMass ν q*Real.exp (b^2*(n:ℝ)/2) ≤
      Real.exp (b^2*(n:ℝ)*q^2/2)) :
    Real.exp (-(b^2*(n:ℝ)*q^2/2+Real.log 8)) ≤
      (disorderLaw n).real {G | b^2*((n:ℝ)-1)/4-Real.log 2 ≤
        Real.log (weightedPartition ν b G)} := by
  let M := Real.exp (b^2*((n:ℝ)-1)/4)
  let E := Real.exp (b^2*(n:ℝ)*q^2/2)
  let S := ∫ G, (weightedPartition ν b G)^2 ∂disorderLaw n
  have hM : 0 < M := Real.exp_pos _
  have hE : 0 < E := Real.exp_pos _
  have hS : 0 < S := by
    apply (integral_pos_iff_support_of_nonneg (fun G => sq_nonneg _)
      (weightedPartition_sq_integrable ν b)).mpr
    have hsupp : Function.support (fun G => (weightedPartition ν b G)^2) = Set.univ := by
      ext G
      simp only [Function.mem_support,Set.mem_univ,iff_true]
      exact pow_ne_zero 2 (weightedPartition_pos ν hνpos hν b G).ne'
    rw [hsupp]
    simp
  have hm := weightedPartition_mean hn ν hν b
  have hR := (weightedPartition_secondMoment_le hn ν hνpos hν b q hq).trans
    (add_le_add_right hr _)
  rw [hm] at hR
  have hR' : S ≤ (2*E)*M^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hM)).mp
    change S/M^2 ≤ 2*E
    change S/M^2 ≤ E+E at hR
    linarith
  have hp := paleyZygmund_half (disorderLaw n) (weightedPartition ν b)
    (continuous_weightedPartition ν b).measurable
    (fun G => (weightedPartition_pos ν hνpos hν b G).le)
    (weightedPartition_integrable ν b) (weightedPartition_sq_integrable ν b)
    (by rw [hm]; exact hM)
  rw [hm] at hp
  have he : Real.exp (-(b^2*(n:ℝ)*q^2/2+Real.log 8)) = 1/(8*E) := by
    rw [Real.exp_neg,Real.exp_add,Real.exp_log (by norm_num)]
    dsimp only [E]
    ring
  have hbound : Real.exp (-(b^2*(n:ℝ)*q^2/2+Real.log 8)) ≤ M^2/(4*S) := by
    rw [he]
    apply (div_le_div_iff₀ (by positivity : 0 < 8*E) (by positivity : 0 < 4*S)).mpr
    nlinarith
  have hex : Real.exp (b^2*((n:ℝ)-1)/4-Real.log 2) = M/2 := by
    rw [Real.exp_sub,Real.exp_log (by norm_num)]
  have hevent : {G : Disorder n | M/2 ≤ weightedPartition ν b G} =
      {G | b^2*((n:ℝ)-1)/4-Real.log 2 ≤ Real.log (weightedPartition ν b G)} := by
    ext G
    simp only [Set.mem_ofPred_eq]
    symm
    rw [← Real.exp_le_exp,
      Real.exp_log (weightedPartition_pos ν hνpos hν b G),hex]
  rw [← hevent]
  exact hbound.trans hp

theorem weightedPartition_half_gain {n : ℕ} (hn : 0 < n)
    (ν : Config n → ℝ) (hνpos : ∀ x, 0 ≤ ν x) (hν : ∑ x, ν x = 1)
    (b q : ℝ) (hb : b ≠ 0) (hq : 0 ≤ q)
    (hr : weightedOverlapMass ν q*Real.exp (b^2*(n:ℝ)/2) ≤
      Real.exp (b^2*(n:ℝ)*q^2/2)) :
    (1/2:ℝ) ≤ (disorderLaw n).real {G | b^2*((n:ℝ)-1)/4-Real.log 2-
      Real.sqrt (2*(logPartitionProxy b n:ℝ)*(b^2*(n:ℝ)*q^2/2+Real.log 8))-
      Real.sqrt (2*(logPartitionProxy b n:ℝ)*Real.log 2) ≤
        Real.log (weightedPartition ν b G)} := by
  apply subGaussian_half_lower
    ((continuous_weightedPartition ν b).log
      (fun G => (weightedPartition_pos ν hνpos hν b G).ne')).measurable
    (show 0 < (logPartitionProxy b n:ℝ) from by
      change 0 < Real.pi^2*b^2*(n:ℝ)/8
      have hn' : (0:ℝ) < n := by exact_mod_cast hn
      have hb' := sq_pos_of_ne_zero hb
      positivity)
    (weightedLogPartition_subGaussian hn ν hνpos hν b)
    (by positivity)
    (weightedPartition_paleyZygmund hn ν hνpos hν b q hq hr)
end SK.Analytic

end
end

end

end OAI
