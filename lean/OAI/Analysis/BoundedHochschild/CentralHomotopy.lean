import Mathlib
import OAI.Analysis.BoundedHochschild.Cochains
import OAI.Analysis.BoundedHochschild.CollisionBounds

namespace OAI

/-! The Hochschild differential and homotopies for central idempotents. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open Filter Topology
namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

 
def centralCut {n : ℕ} (z : M) (f : Cochain M n) : Cochain M n :=
  f.compContinuousLinearMap (fun _ => ContinuousLinearMap.mul ℂ M z)

@[simp] lemma centralCut_apply {n : ℕ} (z : M) (f : Cochain M n) (v : Fin n → M) :
    centralCut z f v = f (fun i => z*v i) := rfl

lemma norm_centralCut_le {n : ℕ} (z : M) (hz : ‖z‖ ≤ 1) (f : Cochain M n) :
    ‖centralCut z f‖ ≤ ‖f‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro v
  apply (f.le_opNorm _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro i _
  exact (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (v i)])

lemma central_mul_assoc (z : M) (hz : ∀ a, z*a=a*z) (a b : M) :
    a*(z*b) = z*(a*b) := by rw [← mul_assoc, ← hz, mul_assoc]

lemma central_idempotent_mul (z : M) (hi : z*z=z) (hz : ∀ a, z*a=a*z) (a b : M) :
    (z*a)*(z*b) = z*(a*b) := by
  rw [mul_assoc, central_mul_assoc z hz, ← mul_assoc z z, hi]

lemma mergeInputs_central (z : M) (hi : z*z=z) (hz : ∀ a, z*a=a*z)
    {n : ℕ} (v : Fin (n+1) → M) (j : Fin n) :
    mergeInputs (fun i => z*v i) j = fun i => z*mergeInputs v j i := by
  funext i
  simp only [mergeInputs]
  split_ifs <;> first | rfl | exact central_idempotent_mul z hi hz _ _

 

theorem differential_centralCut {n : ℕ} (z : M) (hi : z*z=z) (hz : ∀ a, z*a=a*z)
    (f : Cochain M n) (hr : ∀ v, z*f v=f v) (v : Fin (n+1) → M) :
    differentialValue (centralCut z f) v = differentialValue f (fun i => z*v i) := by
  simp only [differentialValue, centralCut_apply, mergeInputs_central z hi hz]
  congr 2
  · rw [mul_assoc, ← central_mul_assoc z hz, hr]
  · rw [← mul_assoc, ← hz, hr]

lemma centralCut_cocycle {n : ℕ} (z : M) (hi : z*z=z) (hz : ∀ a, z*a=a*z)
    (f : Cochain M n) (hr : ∀ v, z*f v=f v)
    (hf : ∀ v, differentialValue f v = 0) :
    ∀ v, differentialValue (centralCut z f) v = 0 := by
  intro v
  rw [differential_centralCut z hi hz f hr]
  exact hf _

end BoundedHochschild

 

namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

def leftCoboundary {n : ℕ} (f : Cochain M n) : Cochain M (n+1) :=
  (((ContinuousLinearMap.compContinuousMultilinearMapL ℂ (fun _ : Fin n => M) M M).flip f).comp
    (ContinuousLinearMap.mul ℂ M)).uncurryLeft

@[simp] lemma leftCoboundary_apply {n : ℕ} (f : Cochain M n) (v : Fin (n+1) → M) :
    leftCoboundary f v = v 0 * f (fun i => v i.succ) := rfl

def rightCoboundary {n : ℕ} (f : Cochain M n) : Cochain M (n+1) :=
  ((ContinuousLinearMap.mul ℂ M).compContinuousMultilinearMap f).uncurryRight

@[simp] lemma rightCoboundary_apply {n : ℕ} (f : Cochain M n) (v : Fin (n+1) → M) :
    rightCoboundary f v = f (fun i => v i.castSucc) * v (Fin.last n) := rfl

def middleCoboundary {n : ℕ} (f : Cochain M (n+1)) (j : Fin (n+1)) : Cochain M (n+2) :=
  (((ContinuousMultilinearMap.curryMidEquiv ℂ (fun _ : Fin (n+1) => M) M j).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((ContinuousLinearMap.compL ℂ M M (Cochain M n) (f.curryMid j)).comp
      (ContinuousLinearMap.mul ℂ M))).uncurryMid j.castSucc

@[simp] lemma middleCoboundary_apply {n : ℕ} (f : Cochain M (n+1)) (j : Fin (n+1))
    (v : Fin (n+2) → M) : middleCoboundary f j v = f (mergeInputs v j) := by
  change f (j.insertNth (v j.castSucc * v (j.castSucc.succAbove j))
    (fun i => v (j.castSucc.succAbove (j.succAbove i)))) = _
  congr 1
  apply (Fin.insertNth_eq_iff).mpr
  constructor
  · simp [mergeInputs, Fin.succAbove_of_le_castSucc]
  · funext i
    change v (j.castSucc.succAbove (j.succAbove i)) = mergeInputs v j (j.succAbove i)
    by_cases h : i.castSucc < j
    · rw [Fin.succAbove_of_castSucc_lt _ _ h]
      have h' : i.castSucc.castSucc < j.castSucc := by simpa using h
      rw [Fin.succAbove_of_castSucc_lt _ _ h']
      simp [mergeInputs, h]
    · have hj : j ≤ i.castSucc := le_of_not_gt h
      rw [Fin.succAbove_of_le_castSucc _ _ hj]
      have h' : j.castSucc ≤ i.succ.castSucc := by
        simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ] at *
        omega
      rw [Fin.succAbove_of_le_castSucc _ _ h']
      have hh : ¬i.succ < j := by
        simp only [Fin.lt_def, Fin.val_succ, Fin.le_def, Fin.val_castSucc] at *
        omega
      have hn : i.succ ≠ j := by
        intro he; have he' := congrArg Fin.val he
        simp only [Fin.val_succ] at he'
        have := j.isLt
        simp only [Fin.le_def, Fin.val_castSucc] at hj
        omega
      simp [mergeInputs, hh, hn]

def differential : {n : ℕ} → Cochain M n → Cochain M (n+1)
  | 0, f => leftCoboundary f - rightCoboundary f
  | n+1, f => leftCoboundary f + ∑ j : Fin (n+1), ((-1:ℂ)^(j.val+1)) • middleCoboundary f j +
      ((-1:ℂ)^(n+1+1)) • rightCoboundary f

@[simp] theorem differential_apply {n : ℕ} (f : Cochain M n) (v : Fin (n+1) → M) :
    differential f v = differentialValue f v := by
  cases n with
  | zero => simp [differential, differentialValue, sub_eq_add_neg]
  | succ n => simp only [differential, differentialValue, add_apply, sum_apply, smul_apply,
      leftCoboundary_apply, rightCoboundary_apply, middleCoboundary_apply]

end BoundedHochschild

 

namespace BoundedHochschild
variable {M : Type*}

def tupleInsert {n : ℕ} (p : Fin (n+1)) (a : M) (v : Fin n → M) (i : Fin (n+1)) : M :=
  if h : i.val < p.val then v ⟨i.val, by omega⟩
  else if h : i = p then a else v ⟨i.val-1, by have := i.isLt; have := p.isLt; omega⟩

lemma tupleInsert_eq {n : ℕ} (p : Fin (n+1)) (a : M) (v : Fin n → M) :
    tupleInsert p a v = p.insertNth a v := by
  apply (Fin.eq_insertNth_iff).mpr
  constructor
  · simp [tupleInsert]
  · funext i
    change tupleInsert p a v (p.succAbove i) = v i
    by_cases h : i.castSucc < p
    · rw [Fin.succAbove_of_castSucc_lt _ _ h]
      dsimp [tupleInsert]
      rw [dite_eq_left (show i.val < p.val from h)]
    · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt h)]
      dsimp [tupleInsert]
      rw [dite_eq_right (by change ¬i.val < p.val at h; omega),
        ite_eq_right (by intro he; have hv := congrArg Fin.val he; dsimp at hv; change ¬i.val < p.val at h; omega)]

lemma tupleInsert_lt {n : ℕ} (p : Fin (n+1)) (a : M) (v : Fin n → M)
    (i : Fin (n+1)) (h : i.val < p.val) :
    Fin.insertNth (α := fun _ => M) p a v i = v ⟨i.val, by omega⟩ := by
  rw [← tupleInsert_eq]
  simp only [tupleInsert, dite_eq_left h]

lemma tupleInsert_gt {n : ℕ} (p : Fin (n+1)) (a : M) (v : Fin n → M)
    (i : Fin (n+1)) (h : p.val < i.val) :
    Fin.insertNth (α := fun _ => M) p a v i = v ⟨i.val-1, by have := i.isLt; omega⟩ := by
  rw [← tupleInsert_eq]
  simp only [tupleInsert, dite_eq_right (by omega : ¬i.val < p.val),
    dite_eq_right (by intro he; have := congrArg Fin.val he; omega : i ≠ p)]

lemma merge_insert_same [Mul M] {n : ℕ} (v : Fin (n+1) → M) (r : Fin (n+1)) (q : M)
    (hq : q*v r=v r) : mergeInputs (r.castSucc.insertNth q v) r = v := by
  funext i
  simp only [mergeInputs]
  split_ifs with h h
  · rw [tupleInsert_lt _ _ _ _ (by simpa only [Fin.val_castSucc, Fin.lt_def] using h)]
    rfl
  · subst i
    rw [Fin.insertNth_apply_same, tupleInsert_gt _ _ _ _ (by simp)]
    simpa using hq
  · rw [tupleInsert_gt _ _ _ _ (by simpa only [Fin.val_castSucc,Fin.val_succ] using
        (show r.val < i.val+1 by omega))]
    rfl

lemma merge_insert_before [Mul M] {n : ℕ} (v : Fin (n+1) → M) (r : Fin (n+1))
    (q : M) (j : Fin n) (hjr : j.val+1 < r.val) :
    mergeInputs (r.castSucc.insertNth q v) (r.succAbove j) =
      (⟨r.val-1, by omega⟩ : Fin (n+1)).insertNth q (mergeInputs v j) := by
  have hs : r.succAbove j=j.castSucc := by
    exact Fin.succAbove_of_castSucc_lt _ _ (by simpa only [Fin.lt_def, Fin.val_castSucc] using (show j.val < r.val by omega))
  rw [hs]
  funext i
  simp only [mergeInputs, ← tupleInsert_eq, tupleInsert, Fin.lt_def, Fin.val_castSucc,
    Fin.val_succ, Fin.ext_iff]
  split_ifs <;> try omega
  all_goals first | rfl | congr 1
  all_goals exact Fin.ext (by dsimp; omega)

lemma merge_insert_after [Mul M] {n : ℕ} (v : Fin (n+1) → M) (r : Fin (n+1))
    (q : M) (j : Fin n) (hjr : r.val ≤ j.val) :
    mergeInputs (r.castSucc.insertNth q v) (r.succAbove j) =
      (⟨r.val, by omega⟩ : Fin (n+1)).insertNth q (mergeInputs v j) := by
  have hs : r.succAbove j=j.succ := by
    exact Fin.succAbove_of_le_castSucc _ _ (by simpa only [Fin.le_def, Fin.val_castSucc] using hjr)
  rw [hs]
  funext i
  simp only [mergeInputs, ← tupleInsert_eq, tupleInsert, Fin.lt_def, Fin.val_castSucc,
    Fin.val_succ, Fin.ext_iff]
  split_ifs <;> try omega
  all_goals first | rfl | congr 1
  all_goals first | rfl | (apply Fin.ext; dsimp; omega) |
    (apply congrArg v; apply Fin.ext; dsimp; omega)

lemma tail_insert {n : ℕ} (v : Fin (n+1) → M) (r : Fin (n+1)) (q : M)
    (hr : 0 < r.val) :
    (fun i : Fin (n+1) => (r.castSucc.insertNth (α := fun _ => M) q v) i.succ) =
    (⟨r.val-1, by omega⟩ : Fin (n+1)).insertNth (α := fun _ => M) q (fun i => v i.succ) := by
  funext i
  simp only [← tupleInsert_eq, tupleInsert, Fin.val_succ, Fin.val_castSucc, Fin.ext_iff]
  split_ifs <;> try omega
  all_goals first | rfl | congr 1
  all_goals exact Fin.ext (by dsimp; omega)

lemma init_insert {n : ℕ} (v : Fin (n+1) → M) (r : Fin (n+1)) (q : M) :
    (fun i : Fin (n+1) => (r.castSucc.insertNth (α := fun _ => M) q v) i.castSucc) =
    r.insertNth (α := fun _ => M) q (fun i => v i.castSucc) := by
  funext i
  simp only [← tupleInsert_eq, tupleInsert, Fin.val_castSucc, Fin.ext_iff]
  split_ifs <;> rfl

lemma last_insert {n : ℕ} (v : Fin (n+1) → M) (r : Fin (n+1)) (q : M) :
    (r.castSucc.insertNth (α := fun _ => M) q v) (Fin.last (n+1)) = v (Fin.last n) := by
  rw [tupleInsert_gt _ _ _ _ (by simp only [Fin.val_castSucc,Fin.val_last]; omega)]
  rfl

end BoundedHochschild

 

open Filter Topology
namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

 
def centralJTerm {n : ℕ} (z q : M) (f : Cochain M (n+1)) (i : Fin n) : Cochain M n :=
  (f.curryMid i.castSucc q).compContinuousLinearMap (fun j =>
    if j < i then ContinuousLinearMap.mul ℂ M z
    else if j = i then ContinuousLinearMap.mul ℂ M q
    else ContinuousLinearMap.id ℂ M)

@[simp] lemma centralJTerm_apply {n : ℕ} (z q : M) (f : Cochain M (n+1))
    (i : Fin n) (v : Fin n → M) :
    centralJTerm z q f i v = f (i.castSucc.insertNth q (fun j =>
      if j < i then z*v j else if j = i then q*v j else v j)) := by
  change f (i.castSucc.insertNth q (fun j => (if j < i then ContinuousLinearMap.mul ℂ M z
    else if j = i then ContinuousLinearMap.mul ℂ M q else ContinuousLinearMap.id ℂ M) (v j))) = _
  apply congrArg (fun w => f (i.castSucc.insertNth q w))
  funext j
  split_ifs <;> rfl

def centralJ {n : ℕ} (z q : M) (f : Cochain M (n+1)) : Cochain M n :=
  ∑ i : Fin n, ((-1:ℂ)^(i.val+1)) • centralJTerm z q f i

lemma norm_centralJTerm_le {n : ℕ} (z q : M) (hz : ‖z‖ ≤ 1) (hq : ‖q‖ ≤ 1)
    (f : Cochain M (n+1)) (i : Fin n) : ‖centralJTerm z q f i‖ ≤ ‖f‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro v
  rw [centralJTerm_apply]
  apply (f.norm_map_insertNth_le _ _).trans
  calc
    ‖f‖ * ‖q‖ * (∏ j, ‖if j < i then z*v j else if j = i then q*v j else v j‖) ≤
        ‖f‖ * 1 * (∏ j, ‖v j‖) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hq (norm_nonneg _)
      · apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro j _
        split_ifs
        · exact (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (v j)])
        · exact (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (v j)])
        · rfl
      · positivity
      · positivity
    _ = _ := by ring

lemma norm_centralJ_le {n : ℕ} (z q : M) (hz : ‖z‖ ≤ 1) (hq : ‖q‖ ≤ 1)
    (f : Cochain M (n+1)) : ‖centralJ z q f‖ ≤ n*‖f‖ := by
  apply (norm_sum_le _ _).trans
  calc
    ∑ i : Fin n, ‖((-1:ℂ)^(i.val+1)) • centralJTerm z q f i‖ ≤
        ∑ _ : Fin n, ‖f‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        using norm_centralJTerm_le z q hz hq f i
    _ = _ := by simp

lemma centralJ_range {n : ℕ} (z q : M) (f : Cochain M (n+1))
    (hr : ∀ v, z*f v=f v) (v : Fin n → M) : z*centralJ z q f v=centralJ z q f v := by
  simp only [centralJ, sum_apply, smul_apply, centralJTerm_apply, Finset.mul_sum,
    mul_smul_comm, hr]

lemma centralJTerm_eq_zero_lt {n : ℕ} (z q : M) (hzq : q*z=0)
    (f : Cochain M (n+1)) (i r : Fin n) (hir : i < r) (v : Fin n → M)
    (hv : ∀ j, j < r → z*v j=v j) : centralJTerm z q f i v=0 := by
  have hqi : q*v i=0 := by rw [← hv i hir, ← mul_assoc, hzq, zero_mul]
  rw [centralJTerm_apply]
  apply f.map_coord_zero ((i.castSucc).succAbove i)
  simp only [Fin.insertNth_apply_succAbove, lt_self_iff_false, ite_false, ite_true, hqi]

lemma centralJTerm_eq_zero_gt {n : ℕ} (z q : M) (hzq : z*q=0)
    (f : Cochain M (n+1)) (i r : Fin n) (hri : r < i) (v : Fin n → M)
    (hv : q*v r=v r) : centralJTerm z q f i v=0 := by
  have hzr : z*v r=0 := by rw [← hv, ← mul_assoc, hzq, zero_mul]
  rw [centralJTerm_apply]
  apply f.map_coord_zero ((i.castSucc).succAbove r)
  simp only [Fin.insertNth_apply_succAbove, hri, ite_true, hzr]

 

lemma centralJ_first_q {n : ℕ} (z q : M) (hzq : z*q=0) (hqz : q*z=0)
    (f : Cochain M (n+1)) (r : Fin n) (v : Fin n → M)
    (hv : ∀ j, j < r → z*v j=v j) (hvr : q*v r=v r) :
    centralJ z q f v = ((-1:ℂ)^(r.val+1)) • f (r.castSucc.insertNth q v) := by
  classical
  rw [centralJ, sum_apply, Finset.sum_eq_single r]
  · simp only [smul_apply, centralJTerm_apply]
    apply congrArg (fun w => ((-1:ℂ)^(r.val+1)) • f (r.castSucc.insertNth q w))
    funext j
    split_ifs with h h
    · exact hv j h
    · subst j; exact hvr
    · rfl
  · intro i _ hir
    rw [smul_apply]
    have hi : centralJTerm z q f i v=0 := by
      rcases lt_or_gt_of_ne hir with h | h
      · exact centralJTerm_eq_zero_lt z q hqz f i r h v hv
      · exact centralJTerm_eq_zero_gt z q hzq f i r h v hvr
    rw [hi, smul_zero]
  · simp

lemma centralJ_all_z {n : ℕ} (z q : M) (hqz : q*z=0)
    (f : Cochain M (n+1)) (v : Fin n → M) (hv : ∀ j, z*v j=v j) :
    centralJ z q f v=0 := by
  rw [centralJ, sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  simp only [smul_apply]
  have hi : centralJTerm z q f i v=0 := by
    have hqi : q*v i=0 := by rw [← hv i, ← mul_assoc, hqz, zero_mul]
    rw [centralJTerm_apply]
    apply f.map_coord_zero ((i.castSucc).succAbove i)
    simp only [Fin.insertNth_apply_succAbove, lt_self_iff_false, ite_false, ite_true, hqi]
  rw [hi, smul_zero]

end BoundedHochschild

 

namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

lemma centralJ_merge_before {n : ℕ} (z q : M) (hzq : z*q=0) (hqz : q*z=0)
    (f : Cochain M (n+1)) (v : Fin (n+1) → M) (r : Fin (n+1))
    (hv : ∀ i, i < r → z*v i=v i) (hvr : q*v r=v r) (j : Fin n)
    (hjr : j.val+1 < r.val) :
    centralJ z q f (mergeInputs v j) = ((-1:ℂ)^r.val) •
      f (mergeInputs (r.castSucc.insertNth (α := fun _ => M) q v) (r.succAbove j)) := by
  rw [merge_insert_before v r q j hjr]
  let r' : Fin n := ⟨r.val-1, by omega⟩
  have hh : ∀ i, i < r' → z*mergeInputs v j i=mergeInputs v j i := by
    intro i hi
    simp only [mergeInputs]
    split_ifs with h h
    · exact hv i.castSucc (by simp only [Fin.lt_def, Fin.val_castSucc] at *; omega)
    · subst i
      rw [← mul_assoc, hv j.castSucc (by simp only [Fin.lt_def, Fin.val_castSucc]; omega)]
    · exact hv i.succ (by simp only [r', Fin.lt_def,Fin.val_succ] at *; omega)
  have hq : q*mergeInputs v j r'=mergeInputs v j r' := by
    have hlo : ¬r' < j := by simp only [r', Fin.lt_def]; omega
    have hne : r' ≠ j := by intro h; have hh := congrArg Fin.val h; dsimp [r'] at hh; omega
    have he : r'.succ=r := Fin.ext (by dsimp [r']; omega)
    simp only [mergeInputs, hlo, hne, ite_false, he]
    exact hvr
  rw [centralJ_first_q z q hzq hqz f r' _ hh hq]
  have he : r'.val+1=r.val := by dsimp [r']; omega
  rw [he]
  rfl

lemma centralJ_merge_after {n : ℕ} (z q : M) (hzq : z*q=0) (hqz : q*z=0)
    (f : Cochain M (n+1)) (v : Fin (n+1) → M) (r : Fin (n+1))
    (hv : ∀ i, i < r → z*v i=v i) (hvr : q*v r=v r) (j : Fin n)
    (hjr : r.val ≤ j.val) :
    centralJ z q f (mergeInputs v j) = ((-1:ℂ)^(r.val+1)) •
      f (mergeInputs (r.castSucc.insertNth (α := fun _ => M) q v) (r.succAbove j)) := by
  rw [merge_insert_after v r q j hjr]
  let r' : Fin n := ⟨r.val, by omega⟩
  have hh : ∀ i, i < r' → z*mergeInputs v j i=mergeInputs v j i := by
    intro i hi
    have hh : i<j := by simp only [r', Fin.lt_def] at *; omega
    simp only [mergeInputs, hh, ite_true]
    exact hv i.castSucc (by simpa only [r', Fin.lt_def,Fin.val_castSucc] using hi)
  have hq : q*mergeInputs v j r'=mergeInputs v j r' := by
    have he : r'.castSucc=r := rfl
    simp only [mergeInputs]
    split_ifs with hlt heq
    · simpa only [he] using hvr
    · rw [he, ← mul_assoc, hvr]
    · exfalso
      apply heq
      apply Fin.ext
      change r.val = j.val
      change ¬r.val < j.val at hlt
      omega
  exact centralJ_first_q z q hzq hqz f r' _ hh hq

lemma centralJ_merge_boundary {n : ℕ} (z q : M) (hzq : z*q=0) (hz : ∀ a, z*a=a*z)
    (f : Cochain M (n+1)) (v : Fin (n+1) → M) (r : Fin (n+1))
    (hv : ∀ i, i < r → z*v i=v i) (hvr : q*v r=v r) (j : Fin n)
    (hjr : j.val+1 = r.val) :
    centralJ z q f (mergeInputs v j)=0 ∧
      f (mergeInputs (r.castSucc.insertNth (α := fun _ => M) q v) (r.succAbove j))=0 := by
  have hjr' : j.succ=r := Fin.ext hjr
  have hlt : j.castSucc<r := by simp only [Fin.lt_def, Fin.val_castSucc]; omega
  have hvj : v j.castSucc*q=0 := by
    rw [← hv _ hlt, mul_assoc, ← central_mul_assoc z hz, hzq, mul_zero]
  constructor
  · apply (centralJ z q f).map_coord_zero j
    simp only [mergeInputs, lt_self_iff_false, ite_false, ite_true, hjr']
    rw [← hvr, ← mul_assoc, hvj, zero_mul]
  · apply f.map_coord_zero j.castSucc
    have hes : r.succAbove j=j.castSucc := Fin.succAbove_of_castSucc_lt _ _ hlt
    rw [hes]
    simp only [mergeInputs, lt_self_iff_false, ite_false, ite_true]
    rw [tupleInsert_lt _ _ _ _ (by simpa only [Fin.val_castSucc] using (show j.val<r.val by omega))]
    have he : j.castSucc.succ=r.castSucc := Fin.ext (by simp only [Fin.val_succ,Fin.val_castSucc]; omega)
    rw [he, Fin.insertNth_apply_same]
    exact hvj

lemma centralJ_inner_cancellation {n : ℕ} (z q : M) (hzq : z*q=0) (hqz : q*z=0)
    (hz : ∀ a, z*a=a*z) (f : Cochain M (n+1)) (v : Fin (n+1) → M) (r : Fin (n+1))
    (hv : ∀ i, i < r → z*v i=v i) (hvr : q*v r=v r) (j : Fin n) :
    ((-1:ℂ)^(r.val+1)) • (((-1:ℂ)^((r.succAbove j).val+1)) •
      f (mergeInputs (r.castSucc.insertNth (α := fun _ => M) q v) (r.succAbove j))) =
        - (((-1:ℂ)^(j.val+1)) • centralJ z q f (mergeInputs v j)) := by
  rcases lt_trichotomy (j.val+1) r.val with h | h | h
  · rw [centralJ_merge_before z q hzq hqz f v r hv hvr j h]
    rw [Fin.succAbove_of_castSucc_lt _ _ (by simp only [Fin.lt_def,Fin.val_castSucc]; omega)]
    simp only [Fin.val_castSucc, smul_smul, ← neg_smul]
    congr 1
    rw [pow_succ]
    ring
  · obtain ⟨h₁,h₂⟩ := centralJ_merge_boundary z q hzq hz f v r hv hvr j h
    rw [h₁,h₂,smul_zero,smul_zero,smul_zero,neg_zero]
  · have hrj : r.val ≤ j.val := by omega
    rw [centralJ_merge_after z q hzq hqz f v r hv hvr j hrj]
    rw [Fin.succAbove_of_le_castSucc _ _ (by simpa only [Fin.le_def,Fin.val_castSucc] using hrj)]
    simp only [Fin.val_succ, smul_smul, ← neg_smul, pow_succ]
    congr 1
    ring

lemma centralJ_left_cancellation {n : ℕ} (z q : M) (hzq : z*q=0) (hqz : q*z=0)
    (hz : ∀ a, z*a=a*z) (f : Cochain M (n+1)) (hr : ∀ w, z*f w=f w)
    (v : Fin (n+1) → M) (r : Fin (n+1))
    (hv : ∀ i, i < r → z*v i=v i) (hvr : q*v r=v r) :
    ((-1:ℂ)^(r.val+1)) • ((r.castSucc.insertNth (α := fun _ => M) q v) 0 *
      f (fun i => (r.castSucc.insertNth (α := fun _ => M) q v) i.succ)) =
        -(v 0 * centralJ z q f (fun i => v i.succ)) := by
  by_cases hro : r.val=0
  · have hre : r=0 := Fin.ext hro
    subst r
    have hqf : ∀ w, q*f w=0 := by intro w; rw [← hr w, ← mul_assoc, hqz, zero_mul]
    have hvrz : v 0*z=0 := by
      rw [← hvr, mul_assoc, ← hz (v 0), ← mul_assoc, hqz, zero_mul]
    have hrj := centralJ_range z q f hr (fun i => v i.succ)
    have hh : v 0*centralJ z q f (fun i => v i.succ)=0 := by
      rw [← hrj, ← mul_assoc, hvrz, zero_mul]
    simp only [Fin.castSucc_zero, Fin.insertNth_apply_same, hqf, smul_zero, hh, neg_zero]
  · have hro : 0<r.val := by omega
    let r' : Fin n := ⟨r.val-1, by omega⟩
    have hv' : ∀ i, i<r' → z*v i.succ=v i.succ := by
      intro i hi
      exact hv _ (by simp only [r', Fin.lt_def,Fin.val_succ] at *; omega)
    have he : r'.succ=r := Fin.ext (by dsimp [r']; omega)
    have hq' : q*v r'.succ=v r'.succ := by simpa only [he] using hvr
    rw [centralJ_first_q z q hzq hqz f r' _ hv' hq', tail_insert v r q hro,
      tupleInsert_lt _ _ _ _ (by simpa only [Fin.val_zero,Fin.val_castSucc] using hro)]
    have he' : r'.val+1=r.val := by dsimp [r']; omega
    rw [he', mul_smul_comm, ← neg_smul, pow_succ]
    congr 1
    ring

lemma centralJ_right_cancellation {n : ℕ} (z q : M) (hzq : z*q=0) (hqz : q*z=0)
    (hz : ∀ a, z*a=a*z) (f : Cochain M (n+1)) (hr : ∀ w, z*f w=f w)
    (v : Fin (n+1) → M) (r : Fin (n+1))
    (hv : ∀ i, i < r → z*v i=v i) (hvr : q*v r=v r) :
    ((-1:ℂ)^(r.val+1)) • (((-1:ℂ)^(n+2)) •
      (f (fun i => (r.castSucc.insertNth (α := fun _ => M) q v) i.castSucc) *
        (r.castSucc.insertNth (α := fun _ => M) q v) (Fin.last (n+1)))) =
        - (((-1:ℂ)^(n+1)) • (centralJ z q f (fun i => v i.castSucc)*v (Fin.last n))) := by
  rw [init_insert, last_insert]
  by_cases hrl : r.val=n
  · have hre : r=Fin.last n := Fin.ext hrl
    subst r
    have hv' : ∀ i : Fin n, z*v i.castSucc=v i.castSucc := by
      intro i; exact hv _ (by simpa only [Fin.lt_def,Fin.val_last,Fin.val_castSucc] using i.isLt)
    rw [centralJ_all_z z q hqz f _ hv', zero_mul, smul_zero, neg_zero]
    have hh : z*v (Fin.last n)=0 := by rw [← hvr, ← mul_assoc, hzq, zero_mul]
    have he : f ((Fin.last n).insertNth q (fun i => v i.castSucc))*v (Fin.last n)=0 := by
      rw [← hr, hz, mul_assoc, hh, mul_zero]
    rw [he, smul_zero, smul_zero]
  · let r' : Fin n := ⟨r.val, by omega⟩
    have hv' : ∀ i, i<r' → z*v i.castSucc=v i.castSucc := by
      intro i hi; exact hv _ (by simpa only [r', Fin.lt_def,Fin.val_castSucc] using hi)
    have he : r'.castSucc=r := rfl
    have hq' : q*v r'.castSucc=v r'.castSucc := by simpa only [he] using hvr
    rw [centralJ_first_q z q hzq hqz f r' _ hv' hq', he]
    simp only [r', smul_mul_assoc, smul_smul, ← neg_smul, pow_succ]
    congr 1
    ring

 
lemma differential_centralJ_first_q {n : ℕ} (z q : M) (hzq : z*q=0) (hqz : q*z=0)
    (hz : ∀ a, z*a=a*z) (f : Cochain M (n+1)) (hr : ∀ w, z*f w=f w)
    (hf : ∀ w, differentialValue f w=0) (v : Fin (n+1) → M) (r : Fin (n+1))
    (hv : ∀ i, i<r → z*v i=v i) (hvr : q*v r=v r) :
    differentialValue (centralJ z q f) v=f v := by
  have h := congrArg (fun a => ((-1:ℂ)^(r.val+1)) • a)
    (hf (r.castSucc.insertNth (α := fun _ => M) q v))
  simp only [smul_zero, differentialValue, smul_add] at h
  rw [centralJ_left_cancellation z q hzq hqz hz f hr v r hv hvr,
    centralJ_right_cancellation z q hzq hqz hz f hr v r hv hvr,
    Fin.sum_univ_succAbove _ r, smul_add, merge_insert_same v r q hvr,
    smul_smul, ← mul_pow, neg_mul_neg, one_mul, one_pow, one_smul, Finset.smul_sum] at h
  have hi : ∑ j : Fin n, ((-1:ℂ)^(r.val+1)) •
      (((-1:ℂ)^((r.succAbove j).val+1)) •
        f (mergeInputs (r.castSucc.insertNth (α := fun _ => M) q v) (r.succAbove j))) =
      -(∑ j : Fin n, ((-1:ℂ)^(j.val+1)) • centralJ z q f (mergeInputs v j)) := by
    simp only [centralJ_inner_cancellation z q hzq hqz hz f v r hv hvr, Finset.sum_neg_distrib]
  rw [hi] at h
  have h' : f v - differentialValue (centralJ z q f) v = 0 := by
    convert h using 1
    simp only [differentialValue]
    abel
  exact (sub_eq_zero.mp h').symm

lemma differential_centralJ_all_z {n : ℕ} (z q : M) (hqz : q*z=0)
    (f : Cochain M (n+1)) (v : Fin (n+1) → M) (hv : ∀ i, z*v i=v i) :
    differentialValue (centralJ z q f) v=0 := by
  have hl : centralJ z q f (fun i : Fin n => v i.succ)=0 := centralJ_all_z z q hqz f _ (fun _ => hv _)
  have hr : centralJ z q f (fun i : Fin n => v i.castSucc)=0 := centralJ_all_z z q hqz f _ (fun _ => hv _)
  have hm (j : Fin n) : centralJ z q f (mergeInputs v j)=0 := by
    apply centralJ_all_z z q hqz f
    intro i
    simp only [mergeInputs]
    split_ifs
    · exact hv _
    · rw [← mul_assoc, hv]
    · exact hv _
  simp only [differentialValue, hl,hr,hm,mul_zero,zero_mul,smul_zero,Finset.sum_const_zero,add_zero]

 

theorem differential_centralJ {n : ℕ} (z : M) (hzz : z*z=z) (hz : ∀ a, z*a=a*z)
    (f : Cochain M (n+1)) (hr : ∀ w, z*f w=f w)
    (hf : ∀ w, differentialValue f w=0) (v : Fin (n+1) → M) :
    differentialValue (centralJ z (1-z) f) v = f v - centralCut z f v := by
  classical
  let q := 1-z
  have hzq : z*q=0 := by dsimp [q]; rw [mul_sub,mul_one,hzz,sub_self]
  have hqz : q*z=0 := by dsimp [q]; rw [sub_mul,one_mul,hzz,sub_self]
  have hqq : q*q=q := by dsimp [q]; rw [mul_sub,sub_mul,sub_mul,one_mul,mul_one,one_mul,hzz]; abel
  let D := differential (centralJ z q f) - f + centralCut z f
  have hall (w : Fin (n+1) → M) (hw : ∀ i, z*w i=w i ∨ q*w i=w i) : D w=0 := by
    by_cases hzall : ∀ i, z*w i=w i
    · have he : (fun i => z*w i)=w := funext hzall
      simp only [D,add_apply,sub_apply,differential_apply,
        differential_centralJ_all_z z q hqz f w hzall, centralCut_apply, he]
      abel
    · let bad : Finset (Fin (n+1)) := Finset.univ.filter (fun i => z*w i≠w i)
      have hb : bad.Nonempty := by
        push Not at hzall
        obtain ⟨i,hi⟩ := hzall
        exact ⟨i, by simp [bad,hi]⟩
      let r := bad.min' hb
      have hrb : r∈bad := Finset.min'_mem bad hb
      have hzr : z*w r≠w r := (Finset.mem_filter.mp hrb).2
      have hqr : q*w r=w r := (hw r).resolve_left hzr
      have hprefix : ∀ i, i<r → z*w i=w i := by
        intro i hi
        by_contra h
        have him : i∈bad := by simp [bad,h]
        have hil : r ≤ i := Finset.min'_le bad i him
        exact (not_le_of_gt hi) hil
      have hc : centralCut z f w=0 := by
        apply f.map_coord_zero r
        change z*w r=0
        rw [← hqr, ← mul_assoc, hzq, zero_mul]
      simp only [D,add_apply,sub_apply,differential_apply,
        differential_centralJ_first_q z q hzq hqz hz f hr hf w r hprefix hqr,
        hc,sub_self,add_zero]
  have hvsum : (fun i => z*v i) + (fun i => q*v i)=v := by
    funext i
    change z*v i+(1-z)*v i=v i
    rw [sub_mul,one_mul]
    abel
  have hd : D v=0 := by
    rw [← hvsum, D.map_add_univ]
    apply Finset.sum_eq_zero
    intro s _
    apply hall
    intro i
    by_cases his : i∈s
    · left
      simp only [Finset.piecewise,his,ite_true,← mul_assoc,hzz]
    · right
      simp only [Finset.piecewise,his,ite_false,← mul_assoc,hqq]
  change differentialValue (centralJ z q f) v = _
  simp only [D,add_apply,sub_apply,differential_apply] at hd
  apply eq_sub_iff_add_eq.mpr
  calc
    _ = (differentialValue (centralJ z q f) v - f v + centralCut z f v) + f v := by abel
    _ = f v := by rw [hd,zero_add]

 
theorem central_cocycle_correction {n : ℕ} (z : M) (hp : IsStarProjection z)
    (hz : ∀ a, z*a=a*z) (f : Cochain M (n+1)) (hr : ∀ w, z*f w=f w)
    (hf : ∀ w, differentialValue f w=0) :
    ∃ g : Cochain M n, ‖g‖ ≤ n*‖f‖ ∧ (∀ w, z*g w=g w) ∧
      ∀ w, differentialValue g w = f w-centralCut z f w := by
  have hq : IsStarProjection (1-z) := hp.one_sub
  exact ⟨centralJ z (1-z) f, norm_centralJ_le z (1-z) (IsStarProjection.norm_le z hp)
    (IsStarProjection.norm_le (1-z) hq) f, centralJ_range z (1-z) f hr,
    differential_centralJ z hp.isIdempotentElem.eq hz f hr hf⟩

end BoundedHochschild
end

end OAI
