import Mathlib
import OAI.Probability.CriticalPercolation.LinearGroups.ClusterMatrix
import OAI.Probability.CriticalPercolation.GraphGeometry.ColumnHitOthersOffdiag

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical Matrix

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

omit [Fintype V] in
lemma last_inverse_diagonal {n : ℕ} (w : E → Prop → ℝ)
    (hpos : ∀ e b, 0 ≤ w e b) (hclosed : ∀ e, 0 < w e False)
    (x : Fin (n+1) → V) (hx : Function.Injective x) :
    G.avoidedAverage w (earlier x (Fin.last n)) (x (Fin.last n)) (fun _ => 1) *
      (G.clusterMatrix w x)⁻¹ (Fin.last n) (Fin.last n) = 1 := by
  have hu : IsUnit (G.clusterMatrix w x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (G.clusterMatrix_det_pos w hpos hclosed x hx))
  have h := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ =>
    M (Fin.last n) (Fin.last n)) (Matrix.nonsing_inv_mul (G.clusterMatrix w x) hu)
  simp only [Matrix.mul_apply, Matrix.one_apply_eq, Fin.sum_univ_castSucc,
    clusterMatrix, column_zero_of_lt _ _ _ (Fin.castSucc_lt_last _), mul_zero,
    Finset.sum_const_zero, zero_add, column_diag] at h
  simpa only [mul_comm] using h

lemma finite_cluster_relay {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (x : Fin (n+1) → V) (hx : Function.Injective x)
    {F : Set V → ℝ} (hF : Monotone F) (hF0 : ∀ U, 0 ≤ F U)
    (a : ℝ) (ha : ∀ j : Fin n, a ≤ expect w
      (fun ω => F (component (G.openGraph ω) (x j.castSucc)))) :
    (1 - G.avoidedAverage w (earlier x (Fin.last n)) (x (Fin.last n)) (fun _ => 1)) * a ≤
      expect w (fun ω => F (component (G.openGraph ω) (x (Fin.last n)))) := by
  let N := (G.clusterMatrix w x)⁻¹
  let y : Fin (n+1) → ℝ := fun j => expect w (fun ω => F (component (G.openGraph ω) (x j)))
  let d := G.avoidedAverage w (earlier x (Fin.last n)) (x (Fin.last n)) (fun _ => 1)
  have hd : 0 < d := G.avoidance_pos w hpos hclosed _ _ (root_not_mem_earlier hx _)
  have hdiag : d * N (Fin.last n) (Fin.last n) = 1 := G.last_inverse_diagonal w hpos hclosed x hx
  have hmass := congrFun (G.inverseMatrix_row_mass w hw hpos hclosed x hx) (Fin.last n)
  change ∑ j, N (Fin.last n) j * 1 = 1 at hmass
  simp only [mul_one, Fin.sum_univ_castSucc] at hmass
  have hzero := G.inverse_clusterFunction_nonneg w hw hpos hclosed x hx hF hF0 (Fin.last n)
  change 0 ≤ ∑ j, N (Fin.last n) j * y j at hzero
  rw [Fin.sum_univ_castSucc] at hzero
  have hs : (∑ j : Fin n, N (Fin.last n) j.castSucc * y j.castSucc) ≤
      (∑ j : Fin n, N (Fin.last n) j.castSucc) * a := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonpos_left (ha j)
      (G.inverseMatrix_offdiag_nonpos w hw hpos hclosed x hx j.castSucc (Fin.last n)
        (ne_of_gt (Fin.castSucc_lt_last j)))
  have hb : (N (Fin.last n) (Fin.last n) - 1) * a ≤
      N (Fin.last n) (Fin.last n) * y (Fin.last n) := by
    have hm : (∑ j : Fin n, N (Fin.last n) j.castSucc) =
        1 - N (Fin.last n) (Fin.last n) := by linarith only [hmass]
    rw [hm] at hs
    linarith only [hzero, hs]
  change (1-d)*a ≤ y (Fin.last n)
  calc
    (1-d)*a = (d * N (Fin.last n) (Fin.last n) - d) * a := by rw [hdiag]
    _ = d * ((N (Fin.last n) (Fin.last n) - 1) * a) := by ring
    _ ≤ d * (N (Fin.last n) (Fin.last n) * y (Fin.last n)) :=
      mul_le_mul_of_nonneg_left hb hd.le
    _ = y (Fin.last n) := by rw [← mul_assoc, hdiag, one_mul]

end CriticalPercolation.BondGraph

end
end

end OAI
