import OAI.Analysis.FreeEntropy.GeometricTail

namespace OAI

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type} [DecidableEq α] [Fintype α]

 theorem wick_degree_bound {R : Series α} {v : α → ℝ} {K u : ℝ}
    (hc : ∀ i, R [i] = 0) (hv : ∀ i j, R [i,j] = if j=i then (v i : ℂ) else 0)
    (_hK : 0 ≤ K) (hR : ∀ m, degreeNorm R m ≤ K^m) (hu : 0 ≤ u) (d : ℕ) :
    ∑ i : α, degreeNorm (wickCoefficients (residual R v i) u) d ^ 2 ≤
      geometricCumulantTail K u d := by
  rw [wickCoefficients_degree_sum hc hv u hu d, geometricCumulantTail]
  split_ifs
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc
      degreeNorm R (d+1)^2 ≤ (K^(d+1))^2 :=
        pow_le_pow_left₀ (degreeNorm_nonneg _ _) (hR _) _
      _ = _ := by rw [← pow_mul, Nat.mul_comm]
  · rfl
 theorem wickCoefficient_summable {R : Series α} {v : α → ℝ} {K u : ℝ}
    (hc : ∀ i, R [i] = 0) (hv : ∀ i j, R [i,j] = if j=i then (v i : ℂ) else 0)
    (hK : 0 ≤ K) (hR : ∀ m, degreeNorm R m ≤ K^m) (hu : 0 < u) (hKu : K^2 < u)
    (i : α) : Summable (fun js => ‖wickCoefficients (residual R v i) u js‖^2) := by
  apply (summable_norm_sq_iff _).mpr
  apply Summable.of_nonneg_of_le (fun d => sq_nonneg _) _ (geometricCumulantTail_summable hu hKu)
  intro d
  exact (single_le_sum (fun j _ => sq_nonneg (degreeNorm (wickCoefficients (residual R v j) u) d))
    (mem_univ i)).trans (wick_degree_bound hc hv hK hR hu.le d)
 theorem wickCoefficient_total_bound {R : Series α} {v : α → ℝ} {K u : ℝ}
    (hc : ∀ i, R [i] = 0) (hv : ∀ i j, R [i,j] = if j=i then (v i : ℂ) else 0)
    (hK : 0 ≤ K) (hR : ∀ m, degreeNorm R m ≤ K^m) (hu : 0 < u) (hKu : 2*K^2 ≤ u) :
    ∑ i : α, ∑' js, ‖wickCoefficients (residual R v i) u js‖^2 ≤ 2*K^6/u^2 := by
  have hKu' : K^2 < u := by nlinarith [sq_nonneg K]
  have hs (i : α) := wickCoefficient_summable hc hv hK hR hu hKu' i
  have hd (i : α) := (summable_norm_sq_iff _).mp (hs i)
  have hsum := hasSum_sum (s := (univ : Finset α)) (fun i _ => (hd i).hasSum)
  simp_rw [tsum_norm_sq_degree _ (hs _)]
  rw [← hsum.tsum_eq]
  exact (hsum.summable.tsum_le_tsum (fun d => wick_degree_bound hc hv hK hR hu.le d)
    (geometricCumulantTail_summable hu hKu')).trans (geometricCumulantTail_le hu hKu)
end FiniteEntropySeparation.FreeSeries

end

end OAI
