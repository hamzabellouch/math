import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyReplicaBound
import OAI.Probability.SKBarriers.Hierarchy.AverageTrace

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

theorem uniform_subprobability_sqrt (k : ℕ) (B : Fin k → ℝ) (hB : ∀ j, 0 ≤ B j) :
    (∑ j : Fin k, ((k+1 : ℕ) : ℝ)⁻¹*Real.sqrt (B j)) ≤
      Real.sqrt (∑ j : Fin k, ((k+1 : ℕ) : ℝ)⁻¹*B j) := by
  let K : ℝ := ((k+1 : ℕ) : ℝ)
  have hK : 0 < K := by dsimp [K]; positivity
  have hsum : 0 ≤ ∑ j, B j := Finset.sum_nonneg (fun j _ => hB j)
  have HC := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j : Fin k => Real.sqrt (B j)) (fun _ => (1 : ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at HC
  simp_rw [Real.sq_sqrt (hB _)] at HC
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  apply (Real.le_sqrt (by positivity) (by positivity)).2
  change (K⁻¹*(∑ j, Real.sqrt (B j)))^2 ≤ K⁻¹*(∑ j, B j)
  have hkk : (k : ℝ) ≤ K := by dsimp [K]; norm_num
  have HH := mul_le_mul_of_nonneg_left (HC.trans (mul_le_mul_of_nonneg_left hkk hsum)) (sq_nonneg K⁻¹)
  have hc : K⁻¹^2*((∑ j, B j)*K) = K⁻¹*(∑ j, B j) := by
    field_simp [ne_of_gt hK]
  rw [hc] at HH
  nlinarith

attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem block_average_overlap_explicit {D N k : ℕ} (hN : 0 < N)
    (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ)
    (Δ : Fin (k+1) → ℝ) {δ : ℝ} (hδ : 0 < δ) (hΔ : ∀ b, δ ≤ Δ b) :
    let n := blockDimension D N k
    let m := blockMass D N k
    let U := blockExponent I a (fun b => Real.sqrt (Δ b))
    let v : Config N → Fin N → ℝ := fun s i => spin (s i)
    let E := 1/((k+1 : ℕ) : ℝ)+2*((k+1 : ℕ) : ℝ)/((N : ℝ)*δ)
    (∑ j : Fin (k+1), ((k+1 : ℕ) : ℝ)⁻¹*hierarchyOverlapError n m U v (blockLevel D N k j)) ≤
      (k : ℝ)*Real.sqrt (2/((N : ℝ)*δ))+3*Real.sqrt (k : ℝ)/((k+1 : ℕ) : ℝ)+E+2*Real.sqrt E+4/((k+1 : ℕ) : ℝ) := by
  let n := blockDimension D N k
  let m := blockMass D N k
  let U := blockExponent I a (fun b => Real.sqrt (Δ b))
  let μ := hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0
  let v : Config N → Fin N → ℝ := fun s i => spin (s i)
  let K : ℝ := ((k+1 : ℕ) : ℝ)
  let E : ℝ := 1/K+2*K/((N : ℝ)*δ)
  let B : Fin k → ℝ := fun j => (∫ z, hierarchyTraceSquare n m U v (blockLevel D N k j.castSucc) z ∂μ)/(N : ℝ)^2
  let V : Fin k → ℝ := fun j => ProbabilityTheory.variance
    (hierarchyMeanSquare n m U (fun i s => v s i) (blockLevel D N k j.castSucc)) μ
  have hv (s : Config N) (i : Fin N) : |v s i| ≤ 1 := by dsimp [v]; cases s i <;> norm_num [spin]
  have hK : 0 < K := by dsimp [K]; positivity
  have hB j : 0 ≤ B j := div_nonneg (integral_nonneg (fun z => finiteCovariance_trace_square_nonneg _ v
    (hierarchySpinWeight_nonneg n m U _ z) (hierarchySpinWeight_sum n m U _ z))) (sq_nonneg _)
  have HT : (∑ j, K⁻¹*B j) ≤ E := equalBlock_average_trace D N k hN U Δ hδ hΔ v hv
    (fun s b i => blockExponent_field I a (fun b => Real.sqrt (Δ b)) b i s)
  have HV : (∑ j, K⁻¹*V j) ≤ (k : ℝ)*Real.sqrt (2/((N : ℝ)*δ))+3*Real.sqrt (k : ℝ)/K :=
    blockMeanSquare_average_variance hN I a Δ hδ hΔ
  have HS : (∑ j, K⁻¹*Real.sqrt (B j)) ≤ Real.sqrt E :=
    (uniform_subprobability_sqrt k B hB).trans (Real.sqrt_le_sqrt HT)
  have H := Finset.sum_le_sum (s := Finset.univ) (fun (j : Fin k) _ =>
    mul_le_mul_of_nonneg_left (hierarchyOverlapError_le hN n m U v hv (blockLevel D N k j.castSucc)) (inv_nonneg.2 hK.le))
  change (∑ j : Fin k, K⁻¹*hierarchyOverlapError n m U v (blockLevel D N k j.castSucc)) ≤
    ∑ j, K⁻¹*(V j+B j+2*Real.sqrt (B j)) at H
  have he : (∑ j, K⁻¹*(V j+B j+2*Real.sqrt (B j))) =
      (∑ j, K⁻¹*V j)+(∑ j, K⁻¹*B j)+2*(∑ j, K⁻¹*Real.sqrt (B j)) := by
    simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl; intro j _; ring
  rw [he] at H
  have HL := mul_le_mul_of_nonneg_left (hierarchyOverlapError_bounds n m U v hv (blockLevel D N k (Fin.last k))).2
    (inv_nonneg.2 hK.le)
  dsimp only
  rw [Fin.sum_univ_castSucc]
  change (∑ j : Fin k, K⁻¹*hierarchyOverlapError n m U v (blockLevel D N k j.castSucc))+
    K⁻¹*hierarchyOverlapError n m U v (blockLevel D N k (Fin.last k)) ≤ _
  change _ ≤ (k : ℝ)*Real.sqrt (2/((N : ℝ)*δ))+3*Real.sqrt (k : ℝ)/K+E+2*Real.sqrt E+4/K
  calc
    _ ≤ ((k : ℝ)*Real.sqrt (2/((N : ℝ)*δ))+3*Real.sqrt (k : ℝ)/K)+E+2*Real.sqrt E+K⁻¹*4 := by linarith
    _ = _ := by ring
end SK.Analytic

end
end

end

end OAI
