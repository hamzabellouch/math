import Mathlib
import OAI.Probability.SKValue.GroundState.RandomColumn

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]

noncomputable def adaptiveResidual (w : ι → EuclideanSpace ℝ κ)
    (v : (j : ℕ) → ColumnHistory κ j → EuclideanSpace ℝ κ) :
    (j : ℕ) → ColumnHistory κ j → ι → EuclideanSpace ℝ κ
  | 0, _, i => w i
  | j+1,h,i => columnResidual (v j (historyInit κ h))
      (adaptiveResidual w v j (historyInit κ h) i)

noncomputable def adaptiveOffset (w : ι → EuclideanSpace ℝ κ)
    (v : (j : ℕ) → ColumnHistory κ j → EuclideanSpace ℝ κ) :
    (j : ℕ) → ColumnHistory κ j → ι → ℝ
  | 0, _, _ => 0
  | j+1,h,i => adaptiveOffset w v j (historyInit κ h) i+
      linearProcess (fun i k ↦ columnVector (v j (historyInit κ h))
        (adaptiveResidual w v j (historyInit κ h) i) k) (h (Fin.last j)) i

variable (w : ι → EuclideanSpace ℝ κ)
  (v : (j : ℕ) → ColumnHistory κ j → EuclideanSpace ℝ κ)
  (hv : ∀ j,Measurable (v j)) (hu : ∀ j h,v j h=0 ∨ ⟪v j h,v j h⟫=1)

include hv in
omit [Fintype ι] [Nonempty ι] in
lemma adaptiveResidual_measurable [Fintype ι] [Nonempty ι] (j : ℕ) (i : ι) :
    Measurable (fun h ↦ adaptiveResidual w v j h i) := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    exact measurable_columnResidual ((hv j).comp (historyInit_measurable κ j))
      (ih.comp (historyInit_measurable κ j))

include hu in
omit [Fintype ι] [Nonempty ι] in
lemma adaptiveResidual_bound [Fintype ι] [Nonempty ι] (R : ℝ) (hR : ∀ i,‖w i‖≤R) (j : ℕ)
    (h : ColumnHistory κ j) (i : ι) : ‖adaptiveResidual w v j h i‖≤R := by
  induction j with
  | zero => exact hR i
  | succ j ih =>
    exact (columnResidual_norm_le (hu j _) _).trans (ih _)

include hv in
lemma adaptiveOffset_measurable (j : ℕ) (i : ι) :
    Measurable (fun h ↦ adaptiveOffset w v j h i) := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    unfold adaptiveOffset
    apply (ih.comp (historyInit_measurable κ j)).add
    unfold linearProcess
    apply Finset.measurable_sum
    intro k _
    apply Measurable.mul _ (by fun_prop)
    exact (PiLp.continuous_apply 2 (fun _ : κ ↦ ℝ) k).measurable.comp
      (measurable_columnVector ((hv j).comp (historyInit_measurable κ j))
        ((adaptiveResidual_measurable w v hv j i).comp (historyInit_measurable κ j)))

include hv hu in
lemma adaptiveOffset_integrable (R : ℝ) (hR : ∀ i,‖w i‖≤R) (j : ℕ) (i : ι) :
    Integrable (fun h ↦ adaptiveOffset w v j h i) (columnHistoryLaw κ j) := by
  induction j with
  | zero => exact integrable_const 0
  | succ j ih =>
    change Integrable (fun h ↦ adaptiveOffset w v j (historyInit κ h) i+
      linearProcess (fun i k ↦ columnVector (v j (historyInit κ h))
        (adaptiveResidual w v j (historyInit κ h) i) k) (h (Fin.last j)) i) _
    exact history_integrable_succ κ j (f:=fun p ↦ adaptiveOffset w v j p.1 i+
      linearProcess (fun i k ↦ columnVector (v j p.1) (adaptiveResidual w v j p.1 i) k) p.2 i) (by
    apply (ih.comp_fst _).add
    apply random_linear_integrable (fun h i k ↦ columnVector (v j h) (adaptiveResidual w v j h i) k)
      _ (R^2) _ i
    · intro i k
      exact (PiLp.continuous_apply 2 (fun _ : κ ↦ ℝ) k).measurable.comp
        (measurable_columnVector (hv j) (adaptiveResidual_measurable w v hv j i))
    · intro h i k
      exact (columnVector_coord_bound (hu j h) _ k).trans
        ((sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans
          (adaptiveResidual_bound w v hu R hR j h i))).mpr
            (adaptiveResidual_bound w v hu R hR j h i)))

include hv hu in

theorem adaptive_value_identity (R : ℝ) (hR : ∀ i,‖w i‖≤R) (K : ℕ) :
    quadraticValue w (fun _ ↦ 0)=
      ∫ h,quadraticValue (adaptiveResidual w v K h) (adaptiveOffset w v K h)
        ∂columnHistoryLaw κ K := by
  induction K with
  | zero => simp [adaptiveResidual,adaptiveOffset]
  | succ K ih =>
    rw [ih]
    change _ = ∫ h,quadraticValue
      (fun i ↦ columnResidual (v K (historyInit κ h))
        (adaptiveResidual w v K (historyInit κ h) i))
      (fun i ↦ adaptiveOffset w v K (historyInit κ h) i+
        linearProcess (fun i k ↦ columnVector (v K (historyInit κ h))
          (adaptiveResidual w v K (historyInit κ h) i) k) (h (Fin.last K)) i)
      ∂columnHistoryLaw κ (K+1)
    rw [history_integral_succ κ K (fun p ↦ quadraticValue
      (fun i ↦ columnResidual (v K p.1) (adaptiveResidual w v K p.1 i))
      (fun i ↦ adaptiveOffset w v K p.1 i+
        linearProcess (fun i k ↦ columnVector (v K p.1)
          (adaptiveResidual w v K p.1 i) k) p.2 i))]
    exact random_column_identity _ _ _ (adaptiveResidual_measurable w v hv K)
      (adaptiveOffset_measurable w v hv K) (adaptiveOffset_integrable w v hv hu R hR K)
      (hv K) (hu K) R (adaptiveResidual_bound w v hu R hR K)

include hv hu in

theorem adaptive_spin_lower (R : ℝ) (hR : ∀ i,‖w i‖≤R) (K : ℕ)
    (s : ColumnHistory κ K → ι)
    (hs : Measurable (fun h ↦ adaptiveOffset w v K h (s h))) :
    (∫ h,adaptiveOffset w v K h (s h) ∂columnHistoryLaw κ K)≤
      quadraticValue w (fun _ ↦ 0) := by
  have hd := adaptiveOffset_integrable w v hv hu R hR K
  have hi : Integrable (fun h ↦ adaptiveOffset w v K h (s h)) (columnHistoryLaw κ K) := by
    apply (integrable_finsetSum Finset.univ (fun i _ ↦ (hd i).abs)).mono' hs.aestronglyMeasurable
    exact Eventually.of_forall (fun h ↦ by
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (fun i _ ↦ abs_nonneg (adaptiveOffset w v K h i)) (Finset.mem_univ (s h)))
  rw [adaptive_value_identity w v hv hu R hR K]
  apply integral_mono hi
    (random_quadratic_integrable _ _ (adaptiveResidual_measurable w v hv K) hd R
      (adaptiveResidual_bound w v hu R hR K))
  intro h
  exact quadraticValue_ge_offset _ _ (s h)

end SKValueG

end

end OAI
