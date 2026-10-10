import Mathlib
import OAI.Probability.CriticalPercolation.Clusters.DeleteBot
import OAI.Probability.CriticalPercolation.ProductMeasure.DensityMulExpect
import OAI.Probability.CriticalPercolation.GraphGeometry.Column
import OAI.Probability.CriticalPercolation.Clusters.HitOthers
import OAI.Probability.CriticalPercolation.LinearGroups.ClusterMatrix

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
lemma column_hitOthers_offdiag {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
    (k i : Fin n) (hik : i ≠ k) :
    G.column w x k (hitOthers x k) i = G.column w x k (fun _ => 1) i := by
  unfold column
  congr 1
  funext ω
  by_cases hc : first (G.openGraph ω) x k ∧ x i ∈ component (G.openGraph ω) (x k)
  · have hh : ∃ j, j ≠ k ∧ x j ∈ component (G.openGraph ω) (x k) := ⟨i, hik, hc.2⟩
    simp [select, hitOthers, hc, hh]
  · simp [select, hc]

omit [Fintype V] in
lemma column_hitOthers_gap_pos {n : ℕ} (w : E → Prop → ℝ)
    (hpos : ∀ e b, 0 ≤ w e b) (hclosed : ∀ e, 0 < w e False)
    (x : Fin n → V) (hx : Function.Injective x) (k : Fin n) :
    0 < G.column w x k (fun _ => 1) k - G.column w x k (hitOthers x k) k := by
  have he : G.column w x k (fun _ => 1) k - G.column w x k (hitOthers x k) k =
      expect w (fun ω => select (G.openGraph ω) x k k *
        (1 - hitOthers x k (component (G.openGraph ω) (x k)))) := by
    unfold column
    erw [← expect_sub]
    congr 1
    funext ω
    ring
  rw [he]
  have hf (ω : E → Prop) : 0 ≤ select (G.openGraph ω) x k k *
      (1 - hitOthers x k (component (G.openGraph ω) (x k))) :=
    mul_nonneg (select_nonneg _ _ _ _) (sub_nonneg.mpr (hitOthers_le_one _ _ _))
  have hd := density_mul_le_expect hpos hf (fun _ => False)
  have hs : first (⊥ : SimpleGraph V) x k := by
    simpa only [first, roots_bot] using root_not_mem_earlier hx k
  simp only [show (fun _ : E => False) = (∅ : Set E) from rfl,
    G.openGraph_empty, component_bot, hitOthers_singleton x hx, sub_zero,
    select_diag, hs, ite_true, mul_one] at hd
  have hp : 0 < density w (∅ : Set E) := Finset.prod_pos (fun e _ => hclosed e)
  simpa only [select_diag] using hp.trans_le hd

lemma inverseMatrix_offdiag_nonpos {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (x : Fin n → V) (hx : Function.Injective x)
    (k i : Fin n) (hik : i ≠ k) : (G.clusterMatrix w x)⁻¹ i k ≤ 0 := by
  let a := G.column w x k (fun _ => 1) k - G.column w x k (hitOthers x k) k
  have ha : 0 < a := G.column_hitOthers_gap_pos w hpos hclosed x hx k
  have he : G.column w x k (fun _ => 1) =
      G.column w x k (hitOthers x k) + a • Pi.single k 1 := by
    ext j
    by_cases hj : j = k
    · subst j
      simp [a]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hj, mul_zero,
        add_zero]
      exact (G.column_hitOthers_offdiag w x k j hj).symm
  have he' := congrArg (fun v => (G.clusterMatrix w x)⁻¹ *ᵥ v) he
  change G.inverseColumn w x k (fun _ => 1) = _ at he'
  rw [G.inverseColumn_const w hpos hclosed x hx, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_single_one] at he'
  have he'' := congrFun he' i
  simp only [Pi.single_eq_of_ne hik, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.col_apply] at he''
  have hp := G.inverseColumn_nonneg w hw hpos hclosed x hx k
    (hitOthers_monotone x k) (hitOthers_nonneg x k) i
  change 0 ≤ ((G.clusterMatrix w x)⁻¹ *ᵥ G.column w x k (hitOthers x k)) i at hp
  nlinarith only [he'', hp, ha]

omit [Fintype V] in
lemma clusterMatrix_row_mass {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (x : Fin n → V) :
    G.clusterMatrix w x *ᵥ (fun _ => 1) = fun _ => 1 := by
  ext i
  change (∑ k, G.column w x k (fun _ => 1) i * 1) = 1
  simp only [mul_one, column]
  erw [← expect_sum]
  simpa only [mul_one, select_mass] using expect_const w hw 1

omit [Fintype V] in
lemma inverseMatrix_row_mass {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (x : Fin n → V) (hx : Function.Injective x) :
    (G.clusterMatrix w x)⁻¹ *ᵥ (fun _ => 1) = fun _ => 1 := by
  have h := congrArg (fun v => (G.clusterMatrix w x)⁻¹ *ᵥ v)
    (G.clusterMatrix_row_mass w hw x)
  have hu : IsUnit (G.clusterMatrix w x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (G.clusterMatrix_det_pos w hpos hclosed x hx))
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec] at h
  exact h.symm

omit [Fintype V] in
lemma clusterFunction_sum_columns {n : ℕ} (w : E → Prop → ℝ)
    (x : Fin n → V) (F : Set V → ℝ) :
    (fun i => expect w (fun ω => F (component (G.openGraph ω) (x i)))) =
      ∑ k, G.column w x k F := by
  ext i
  simp only [Finset.sum_apply, column]
  erw [← expect_sum]
  congr 1
  funext ω
  exact cluster_partition (G.openGraph ω) x F i

lemma inverse_clusterFunction_nonneg {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (x : Fin n → V) (hx : Function.Injective x)
    {F : Set V → ℝ} (hF : Monotone F) (hF0 : ∀ U, 0 ≤ F U) (i : Fin n) :
    0 ≤ ((G.clusterMatrix w x)⁻¹ *ᵥ
      (fun j => expect w (fun ω => F (component (G.openGraph ω) (x j))))) i := by
  rw [G.clusterFunction_sum_columns, Matrix.mulVec_sum, Finset.sum_apply]
  exact Finset.sum_nonneg (fun k _ => G.inverseColumn_nonneg w hw hpos hclosed x hx k hF hF0 i)

end CriticalPercolation.BondGraph

end
end

end OAI
