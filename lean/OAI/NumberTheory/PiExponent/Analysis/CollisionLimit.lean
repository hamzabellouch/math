import Mathlib
import OAI.NumberTheory.PiExponent.Analysis.FiniteDeterminantCollision

namespace OAI

open scoped BigOperators Topology
open Filter

namespace PiExponent.Collision

theorem norm_det_le_of_entrywise_limit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℕ → Matrix ι ι ℂ) (T : Matrix ι ι ℂ) {B : ℝ}
    (hlim : ∀ i j, Tendsto (fun N => A N i j) atTop (𝓝 (T i j)))
    (hbound : ∀ N, ‖(A N).det‖ ≤ B) : ‖T.det‖ ≤ B := by
  have hmatrix : Tendsto A atTop (𝓝 T) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact tendsto_pi_nhds.mpr (hlim i)
  have hdet : Tendsto (fun N => (A N).det) atTop (𝓝 T.det) :=
    (continuous_id.matrix_det.tendsto T).comp hmatrix
  exact le_of_tendsto' hdet.norm hbound

theorem norm_det_le_of_entrywise_hasSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ι → ℕ → ι → ℂ) (T : Matrix ι ι ℂ) {B : ℝ}
    (hsum : ∀ i j, HasSum (fun d => C i d j) (T i j))
    (hbound : ∀ N, ‖Matrix.det (fun i j => ∑ d ∈ Finset.range N, C i d j)‖ ≤ B) :
    ‖T.det‖ ≤ B := by
  exact norm_det_le_of_entrywise_limit
    (fun N i j => ∑ d ∈ Finset.range N, C i d j) T
    (fun i j => (hsum i j).tendsto_sum_nat) hbound

theorem norm_det_le_of_tested_series_hasSum
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (group : ι → κ) (coeff : κ → ℕ → ι → ℂ) (test : ι → ℕ → ℂ)
    (T : Matrix ι ι ℂ) {B : ℝ}
    (hsum : ∀ i j, HasSum (fun d => test i d * coeff (group i) d j) (T i j))
    (hbound : ∀ N,
      ‖Matrix.det (fun i j => ∑ d ∈ Finset.range N, test i d * coeff (group i) d j)‖ ≤ B) :
    ‖T.det‖ ≤ B := by
  exact norm_det_le_of_entrywise_hasSum
    (fun i d j => test i d * coeff (group i) d j) T hsum hbound

theorem infinite_collision_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (B : ι → ℕ → ℂ) (C : κ → ℕ → ι → ℂ)
    (D s : ℝ) (L : ι → ℝ) (hD : 0 ≤ D) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hL : ∀ i, 0 ≤ L i)
    (hC : ∀ a d j, ‖C a d j‖ ≤ D)
    (hB : ∀ i d, ‖B i d‖ ≤ L i * (s * s) ^ d)
    (T : Matrix ι ι ℂ)
    (hsum : ∀ i j, HasSum (fun d => B i d * C (group i) d j) (T i j)) :
    ‖T.det‖ ≤
      ((Fintype.card ι).factorial * D ^ Fintype.card ι * (∏ i, L i)) *
        s ^ (∑ a, (multiplicity Finset.univ group a).choose 2) *
          ((1 - s)⁻¹) ^ Fintype.card ι := by
  apply norm_det_le_of_tested_series_hasSum group C B T hsum
  intro N
  have hmatrix : (fun i j => ∑ d ∈ Finset.range N, B i d * C (group i) d j) =
      (fun i j => ∑ d : Fin N, B i d * C (group i) d j) := by
    funext i j
    exact (Fin.sum_univ_eq_sum_range (fun d : ℕ => B i d * C (group i) d j) N).symm
  rw [hmatrix]
  exact FiniteDeterminantCollision.finite_collision_bound group B C D s L hD hs0 hs1
    hL hC hB N

end PiExponent.Collision

end OAI
