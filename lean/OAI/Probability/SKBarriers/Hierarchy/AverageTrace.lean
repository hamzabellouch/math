import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.BlockTrace
import OAI.Probability.SKBarriers.Gaussian.ReciprocalSquares

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section AverageTrace
variable {S : Type} [Fintype S] [Nonempty S]

theorem equalBlock_average_trace (D N k : ℕ) (hN : 0 < N)
    (U : S → ParameterSpace (blockDimension D N k) →L[ℝ] ℝ)
    (Δ : Fin (k+1) → ℝ) {δ : ℝ} (hδ : 0 < δ) (hΔ : ∀ b, δ ≤ Δ b)
    (v : S → Fin N → ℝ) (hvb : ∀ s i, |v s i| ≤ 1)
    (hv : ∀ s b i, U s (coordinateAxis (blockDimension D N k) (fieldIndex D N k b i)) = Real.sqrt (Δ b)*v s i) :
    (∑ j : Fin k, ((k+1 : ℕ) : ℝ)⁻¹ *
      ((∫ z, hierarchyTraceSquare (blockDimension D N k) (blockMass D N k) U v (blockLevel D N k j.castSucc) z
      ∂hierarchyPathLaw (blockDimension D N k) (blockMass D N k) (affineLogPartition (fun _ => 0) U) 0)/(N : ℝ)^2)) ≤
      1/((k+1 : ℕ) : ℝ)+2*((k+1 : ℕ) : ℝ)/((N : ℝ)*δ) := by
  let n := blockDimension D N k
  let m := blockMass D N k
  let K : ℝ := ((k+1 : ℕ) : ℝ)
  let A : ℝ := K^2/((N : ℝ)*δ)
  let r : Fin (k+1) → ℝ := fun j => hierarchyMeanOverlap n m U (fun i s => v s i) (blockLevel D N k j)
  have hc (i : Fin N) (s : S) : ‖v s i‖ ≤ 1 := by simpa only [Real.norm_eq_abs] using hvb s i
  have hr0 : 0 ≤ r 0 := (hierarchyMeanOverlap_bounds n m U (fun i s => v s i) hc _).1
  have hr1 : r (Fin.last k) ≤ 1 := (hierarchyMeanOverlap_bounds n m U (fun i s => v s i) hc _).2
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hK : 0 < K := by dsimp [K]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hpos b : 0 < Δ b := hδ.trans_le (hΔ b)
  have he (j : Fin k) : 1/((N : ℝ)*(Real.sqrt (Δ j.succ))^2*
      (((j.val+1 : ℕ) : ℝ)/K)^2) ≤ A*(1/((j.val+1 : ℕ) : ℝ)^2) := by
    rw [Real.sq_sqrt (hpos j.succ).le]
    have hJ : (0 : ℝ) < ((j.val+1 : ℕ) : ℝ) := by positivity
    calc
      _ ≤ 1/((N : ℝ)*δ*(((j.val+1 : ℕ) : ℝ)/K)^2) :=
        one_div_le_one_div_of_le (by positivity) (by gcongr; exact hΔ j.succ)
      _ = _ := by dsimp [A]; field_simp
  have H (j : Fin k) := (equalBlock_trace_integral D N k hN U (fun b => Real.sqrt (Δ b))
    (fun b => Real.sqrt_pos.2 (hpos b)) v hvb hv j).trans (add_le_add le_rfl (he j))
  have HS := Finset.sum_le_sum (s := Finset.univ) (fun (j : Fin k) _ =>
    mul_le_mul_of_nonneg_left (H j) (inv_nonneg.2 hK.le))
  change (∑ j : Fin k, K⁻¹*_) ≤ _
  apply HS.trans
  change (∑ j : Fin k, K⁻¹*(r j.succ-r j.castSucc+A*(1/((j.val+1 : ℕ) : ℝ)^2))) ≤ _
  rw [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  have ht : (∑ j : Fin k, (r j.succ-r j.castSucc)) = r (Fin.last k)-r 0 := by
    rw [Finset.sum_sub_distrib]
    have h1 := Fin.sum_univ_succ r
    have h2 := Fin.sum_univ_castSucc r
    linarith
  rw [ht]
  have hb := mul_le_mul_of_nonneg_left (sum_nat_reciprocal_squares k) hA
  have hl : r (Fin.last k)-r 0+A*(∑ j : Fin k, 1/((j.val+1 : ℕ) : ℝ)^2) ≤ 1+2*A := by linarith
  calc
    _ ≤ K⁻¹*(1+2*A) := mul_le_mul_of_nonneg_left hl (inv_nonneg.2 hK.le)
    _ = _ := by dsimp [A,K]; field_simp
end AverageTrace
end SK.Analytic

end
end

end

end OAI
