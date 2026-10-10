import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.Column
import OAI.Probability.CriticalPercolation.GraphGeometry.UpdateKernel

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

noncomputable def clusterMatrix {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V) :
    Matrix (Fin n) (Fin n) ℝ := fun i k => G.column w x k (fun _ => 1) i

omit [Fintype V] in
lemma column_zero_of_lt {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
    {k i : Fin n} (hik : i < k) (F : Set V → ℝ) : G.column w x k F i = 0 := by
  unfold column
  simp only [select_zero_of_lt _ _ hik, zero_mul, expect_zero]

omit [Fintype V] in
lemma column_diag {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
    (k : Fin n) (F : Set V → ℝ) :
    G.column w x k F k = G.avoidedAverage w (earlier x k) (x k) F := by
  unfold column avoidedAverage
  simp only [select_diag, first]
  congr 1
  funext ω
  split_ifs <;> simp_all

omit [Fintype V] in
lemma clusterMatrix_lower {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V) :
    (G.clusterMatrix w x).IsLowerTriangular := by
  intro i k hik
  exact G.column_zero_of_lt w x hik _

omit [Fintype V] in
lemma clusterMatrix_det_pos {n : ℕ} (w : E → Prop → ℝ)
    (hpos : ∀ e b, 0 ≤ w e b) (hclosed : ∀ e, 0 < w e False)
    (x : Fin n → V) (hx : Function.Injective x) : 0 < (G.clusterMatrix w x).det := by
  rw [Matrix.det_of_isLowerTriangular _ (G.clusterMatrix_lower w x)]
  apply Finset.prod_pos
  intro k _
  change 0 < G.column w x k (fun _ => 1) k
  rw [G.column_diag]
  exact G.avoidance_pos w hpos hclosed _ _ (root_not_mem_earlier hx k)

noncomputable def inverseColumn {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
    (k : Fin n) (F : Set V → ℝ) : Fin n → ℝ :=
  (G.clusterMatrix w x)⁻¹ *ᵥ G.column w x k F

omit [Fintype V] in
lemma inverseColumn_const {n : ℕ} (w : E → Prop → ℝ)
    (hpos : ∀ e b, 0 ≤ w e b) (hclosed : ∀ e, 0 < w e False)
    (x : Fin n → V) (hx : Function.Injective x) (k : Fin n) (c : ℝ) :
    G.inverseColumn w x k (fun _ => c) = c • Pi.single k 1 := by
  have hc : G.column w x k (fun _ => c) = c • G.column w x k (fun _ => 1) := by
    funext i
    change expect w _ = c * expect w _
    rw [← expect_const_mul]
    congr 1
    funext ω
    ring
  have hunit : IsUnit (G.clusterMatrix w x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (G.clusterMatrix_det_pos w hpos hclosed x hx))
  unfold inverseColumn
  rw [hc, Matrix.mulVec_smul]
  congr 1
  have hcol : G.column w x k (fun _ => 1) = G.clusterMatrix w x *ᵥ Pi.single k 1 := by
    ext i
    simp [Matrix.mulVec_single, clusterMatrix]
  rw [hcol, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]

lemma inverseColumn_decomposition {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (x : Fin n → V) (k : Fin n) (F : Set V → ℝ) :
    G.inverseColumn w x k F =
      G.inverseColumn w x k (G.clusterUpdate w (earlier x k) (x k) F) +
        ∑ l, if k < l then G.inverseColumn w x l
          (G.expectedResidual w (earlier x k) (x k) F) else 0 := by
  have hc : G.column w x k F =
      G.column w x k (G.clusterUpdate w (earlier x k) (x k) F) +
        ∑ l, if k < l then G.column w x l
          (G.expectedResidual w (earlier x k) (x k) F) else 0 := by
    ext i
    simpa only [Pi.add_apply, Finset.sum_apply, ite_apply, Pi.zero_apply] using
      G.column_decomposition w hw x k F i
  unfold inverseColumn
  rw [hc, Matrix.mulVec_add, Matrix.mulVec_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  split_ifs <;> simp

omit [Fintype V] in
lemma continuous_inverseColumn {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
    (k i : Fin n) : Continuous (fun F : Set V → ℝ => G.inverseColumn w x k F i) := by
  unfold inverseColumn Matrix.mulVec dotProduct column expect
  fun_prop

lemma inverseColumn_nonneg {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (x : Fin n → V) (hx : Function.Injective x)
    (k : Fin n) {F : Set V → ℝ} (hF : Monotone F) (hF0 : ∀ U, 0 ≤ F U) :
    ∀ i, 0 ≤ G.inverseColumn w x k F i := by
  induction k using WellFoundedGT.induction generalizing F with
  | ind k ih =>
    have hstep (f : Set V → ℝ) (hf : Monotone f) (i : Fin n) :
        G.inverseColumn w x k (G.clusterUpdate w (earlier x k) (x k) f) i ≤
          G.inverseColumn w x k f i := by
      have hd := congrFun (G.inverseColumn_decomposition w hw x k f) i
      simp only [Pi.add_apply, Finset.sum_apply, ite_apply, Pi.zero_apply] at hd
      have hr : 0 ≤ ∑ l, if k < l then G.inverseColumn w x l
          (G.expectedResidual w (earlier x k) (x k) f) i else 0 := by
        apply Finset.sum_nonneg
        intro l _
        split_ifs with hkl
        · exact ih l hkl (G.expectedResidual_monotone w hw hpos _ _ hf)
            (G.expectedResidual_nonneg w hw hpos _ _ hf) i
        · exact le_rfl
      linarith only [hd, hr]
    have hmono (j : ℕ) : Monotone ((G.clusterUpdate w (earlier x k) (x k))^[j] F) := by
      induction j with
      | zero => exact hF
      | succ j hj =>
        rw [Function.iterate_succ_apply']
        exact G.clusterUpdate_monotone w hpos _ _ hj
    have hbound (j : ℕ) (i : Fin n) :
        G.inverseColumn w x k ((G.clusterUpdate w (earlier x k) (x k))^[j] F) i ≤
          G.inverseColumn w x k F i := by
      induction j with
      | zero => exact le_rfl
      | succ j hj =>
        rw [Function.iterate_succ_apply']
        exact (hstep _ (hmono j) i).trans hj
    let m := G.avoidedAverage w (earlier x k) (x k) F /
      G.avoidedAverage w (earlier x k) (x k) (fun _ => 1)
    have hm : 0 ≤ m := by
      apply div_nonneg
      · unfold avoidedAverage
        apply expect_nonneg hpos
        intro ω
        split_ifs
        · exact le_rfl
        · exact hF0 _
      · exact le_of_lt (G.avoidance_pos w hpos hclosed _ _ (root_not_mem_earlier hx k))
    have hlim : Filter.Tendsto
        (fun j => (G.clusterUpdate w (earlier x k) (x k))^[j] F) Filter.atTop
        (nhds (fun _ => m)) :=
      tendsto_pi_nhds.mpr (fun U => G.tendsto_clusterUpdate w hw hpos hclosed _ _
        (root_not_mem_earlier hx k) F U)
    intro i
    have hi := (G.continuous_inverseColumn w x k i).tendsto (fun _ => m) |>.comp hlim
    have hb := le_of_tendsto hi (Filter.Eventually.of_forall (fun j => hbound j i))
    rw [G.inverseColumn_const w hpos hclosed x hx] at hb
    apply le_trans _ hb
    change 0 ≤ m * (Pi.single (M := fun _ : Fin n => ℝ) k 1 i)
    apply mul_nonneg hm
    by_cases hki : k = i <;> simp [hki]

end CriticalPercolation.BondGraph

end
end

end OAI
