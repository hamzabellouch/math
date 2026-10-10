import OAI.Analysis.LipschitzEquivalence.RotatingStages

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal

namespace LipschitzCounterexample.SeparatingStages
open scoped ENNReal NNReal InnerProductSpace
open HilbertSlots RadialBudget SlowAngles RotatingStages

def stage (n : ℕ) : ℕ → M → Block n
  | 0 => fun _ => Wzero n
  | k+1 => if h : k < n+1 then W n ⟨k,h⟩ else fun _ => 0

def bounds : ℕ → ℝ
  | 0 => 0
  | k+1 => stageBound (k+1)

theorem bounds_nonneg (k : ℕ) : 0 ≤ bounds k := by
  cases k with
  | zero => exact le_refl _
  | succ k => exact stageBound_nonneg _

theorem stage_contDiff (n k : ℕ) : ContDiff ℝ 1 (stage n k) := by
  cases k with
  | zero => exact contDiff_const
  | succ k => simp only [stage]; split_ifs <;> [exact W_contDiff n _; exact contDiff_const]

theorem stage_fderiv_bound (n k : ℕ) (x : M) : ‖fderiv ℝ (stage n k) x‖ ≤ bounds k := by
  cases k with
  | zero => simp [stage,bounds]
  | succ k =>
    simp only [stage]
    split_ifs
    · exact W_fderiv_bound n _ x
    · simpa only [fderiv_const_apply,ContinuousLinearMap.opNorm_zero] using bounds_nonneg (k+1)

theorem norm_stage (n k : ℕ) (hk : k ≤ n+1) (x : M) : ‖stage n k x‖ = 1 := by
  cases k with
  | zero => exact norm_Wzero n
  | succ k => simpa only [stage,dite_eq_left (by omega : k<n+1)] using norm_W n ⟨k,by omega⟩ x

theorem inner_stage (n j k : ℕ) (hj : j < k) (hk : k ≤ n+1) (x y : M) :
    ⟪stage n j x,stage n k y⟫_ℝ = 0 := by
  cases k with
  | zero => omega
  | succ k =>
    rw [stage, dite_eq_left (by omega : k<n+1)]
    cases j with
    | zero => exact inner_Wzero_W n ⟨k,by omega⟩ y
    | succ j =>
      rw [stage,dite_eq_left (by omega : j<n+1)]
      apply inner_W_W
      intro he
      have hv := congrArg Fin.val he
      simp only at hv
      omega

def slot (n : ℕ) : M → Block n :=
  path (stage n) (fun k x => theta bounds bounds_nonneg k (radius n x)) (n+1)

theorem norm_slot (n : ℕ) (x : M) : ‖slot n x‖ = 1 :=
  norm_path (stage n) _ (n+1) x (fun j hj => norm_stage n j hj x)
    (fun j k hj hk => inner_stage n j k hj hk x x)

theorem slot_contDiff (n : ℕ) : ContDiff ℝ 1 (slot n) := by
  apply path_contDiff
  · exact stage_contDiff n
  · intro k
    exact pulledAngle_contDiff bounds bounds_nonneg (radius n) (radius_nonneg n)
      (radius_lipschitz n).continuous (radius_contDiffAt n) k

theorem slot_derivative_budget (n : ℕ) (x : M) (hr : 0 < radius n x) :
    ‖fderiv ℝ (slot n) x‖ ≤ gamma (radius n x) :=
  path_derivative_budget (stage n) bounds bounds_nonneg rfl (radius n)
    (radius_lipschitz n).continuous (radius_contDiffAt n) (radius_lipschitz n)
    (stage_contDiff n) (stage_fderiv_bound n) (n+1) x hr
    (fun j hj => norm_stage n j hj x) (fun j k hj hk => inner_stage n j k hj hk x x)

end LipschitzCounterexample.SeparatingStages

namespace LipschitzCounterexample.SeparatingStages
open scoped ENNReal NNReal InnerProductSpace Topology
open HilbertSlots RadialBudget SlowAngles RotatingStages Filter

def h : M ≃ U := Equiv.ofBijective (movingSlotsMap slot norm_slot)
  (movingSlotsMap_bijective slot norm_slot Wzero norm_Wzero slot_contDiff slot_derivative_budget)

theorem h_bounds (x y : M) :
    (24/25 : ℝ)*‖x-y‖ ≤ ‖h x-h y‖ ∧ ‖h x-h y‖ ≤ (26/25 : ℝ)*‖x-y‖ :=
  movingSlotsMap_bounds slot norm_slot Wzero norm_Wzero slot_contDiff slot_derivative_budget x y

@[simp] theorem norm_h (x : M) : ‖h x‖ = ‖x‖ := norm_movingSlotsMap slot norm_slot x

@[simp] theorem h_zero : h 0 = 0 := norm_eq_zero.mp (by rw [norm_h,norm_zero])

theorem h_lipschitz : LipschitzWith (26/25) h :=
  lipschitzWith_iff_norm_sub_le.mpr (fun x y => (h_bounds x y).2)

theorem h_symm_lipschitz : LipschitzWith (25/24) h.symm := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro x y
  have hb := (h_bounds (h.symm x) (h.symm y)).1
  rw [h.apply_symm_apply,h.apply_symm_apply] at hb
  norm_num only [NNReal.coe_div,NNReal.coe_ofNat]
  linarith

def D (x : M) : U := h x-x.fst

@[simp] theorem D_zero : D 0 = 0 := by simp [D]

theorem fst_lipschitz : LipschitzWith 1 (fun x : M => x.fst) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro x y
  simpa only [NNReal.coe_one,one_mul, WithLp.sub_fst] using WithLp.norm_fst_le U (x-y)

theorem D_lipschitz : LipschitzWith (51/25) D := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro x y
  have hf := (lipschitzWith_iff_norm_sub_le.mp fst_lipschitz x y)
  have hh := (h_bounds x y).2
  have hi : D x-D y = (h x-h y) - (x.fst-y.fst) := by dsimp [D]; abel
  rw [hi]
  calc
    ‖(h x-h y) - (x.fst-y.fst)‖ ≤ ‖h x-h y‖ + ‖x.fst-y.fst‖ := norm_sub_le _ _
    _ ≤ (51/25 : ℝ≥0) * ‖x-y‖ := by norm_num at hf ⊢; linarith

theorem D_coord (x : M) (n : ℕ) :
    D x n = (scalarSlot slot x n - ⟪slot n x,x.fst n⟫_ℝ) • slot n x := by
  change movingSlotsMap slot norm_slot x n - x.fst n = _
  rw [movingSlotsMap_apply,slotCoord]
  abel

instance : TopologicalSpace.SeparableSpace U := by
  let S : Set U := ⋃ i : ℕ, Set.range (lp.single (E := Block) 2 i)
  have hs : TopologicalSpace.IsSeparable S :=
    TopologicalSpace.IsSeparable.iUnion (fun i =>
      TopologicalSpace.isSeparable_range (lp.isometry_single i).continuous)
  have hd : Dense (Submodule.span ℝ S : Set U) := by
    intro s
    apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by simp) s).tendsto_sum_nat
    apply Eventually.of_forall
    intro n
    apply subset_closure
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.subset_span
    exact Set.mem_iUnion.2 ⟨i,⟨s i,rfl⟩⟩
  exact hd.isSeparable_iff.mp hs.span

def q : FreeSpace.Space M →L[ℝ] U := FreeSpace.linearize D

@[simp] theorem q_point (x : M) : q (FreeSpace.point x) = D x :=
  FreeSpace.linearize_point D D_lipschitz D_zero x

theorem q_norm : ‖q‖ ≤ (51/25 : ℝ) :=
  FreeSpace.norm_linearize_le D D_lipschitz D_zero

end LipschitzCounterexample.SeparatingStages

end

end OAI
