import OAI.Geometry.NodalSets.Charts.ChartNormComparison

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

def sourceEuclideanNorm (x : Coord) : ℝ := Real.sqrt (∑ i, (x i)^2)

lemma sourceEuclideanNorm_nonneg (x : Coord) : 0 ≤ sourceEuclideanNorm x := Real.sqrt_nonneg _

lemma sourceEuclideanNorm_le (x : Coord) : sourceEuclideanNorm x ≤ 2*‖x‖ := by
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  have hh (i : Fin 4) : (x i)^2 ≤ ‖x‖^2 := by
    have hi := norm_le_pi_norm x i
    change |x i| ≤ ‖x‖ at hi
    nlinarith [sq_abs (x i),norm_nonneg x,abs_nonneg (x i)]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) ↦ hh i)
  norm_num at hs
  nlinarith

lemma norm_le_sourceEuclideanNorm (x : Coord) : ‖x‖ ≤ sourceEuclideanNorm x := by
  apply (pi_norm_le_iff_of_nonneg (sourceEuclideanNorm_nonneg x)).mpr
  intro i
  have hi : (x i)^2 ≤ ∑ j : Fin 4, (x j)^2 :=
    Finset.single_le_sum (fun j _ ↦ sq_nonneg (x j)) (Finset.mem_univ i)
  have hs := Real.sq_sqrt (Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) ↦ sq_nonneg (x j)))
  change |x i| ≤ sourceEuclideanNorm x
  have hpos := sourceEuclideanNorm_nonneg x
  dsimp [sourceEuclideanNorm] at *
  nlinarith [sq_abs (x i)]

lemma gaussian_source_euclidean (x : Coord) (c N s : ℝ) (hc : 0 ≤ c) (hN : 0 ≤ N) :
    Real.exp (N*s-c*N*‖x‖^2) ≤ Real.exp (N*s-(c/4)*N*(sourceEuclideanNorm x)^2) := by
  have h := gaussian_chart_norm_bound c N 2 ‖x‖ (sourceEuclideanNorm x) hc hN (by norm_num)
    (norm_nonneg _) (sourceEuclideanNorm_nonneg x) (sourceEuclideanNorm_le x)
  apply Real.exp_le_exp.mpr
  norm_num at h
  linarith

lemma coordinate_partials_le_iterated_norm (u : Coord → ℂ) (k : ℕ) (x : Coord)
    (a : Fin k → Fin 4) :
    ‖iteratedFDeriv ℝ k u x (fun j ↦ Pi.single (a j) 1)‖ ≤ ‖iteratedFDeriv ℝ k u x‖ := by
  have h := (iteratedFDeriv ℝ k u x).le_opNorm (fun j ↦ Pi.single (a j) 1)
  have hn (j : Fin k) : ‖(Pi.single (a j) (1:ℝ) : Coord)‖ = 1 := by simp [Pi.norm_single]
  simpa only [hn,Finset.prod_const_one,mul_one] using h

end
end Yau.Geometry

end OAI
