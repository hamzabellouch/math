import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.FinPivotPSD
import OAI.Analysis.MatrixSigning.Machines.NestedSchur
import OAI.Analysis.MatrixSigning.Machines.SchurBounds

namespace OAI

namespace KS.W07

open Matrix

def appendIndexEquiv (k : ℕ) : Fin k ⊕ Unit ≃ Fin (k + 1) where
  toFun := Sum.elim Fin.castSucc (fun _ => Fin.last k)
  invFun := Fin.lastCases (Sum.inr ()) Sum.inl
  left_inv := by
    intro i
    cases i with
    | inl i => simp
    | inr i => cases i; simp
  right_inv := by
    intro i
    induction i using Fin.lastCases <;> simp

noncomputable def selectedSchur {N : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (M : Matrix (Fin N) (Fin N) ℚ) (p : ι → Fin N) (r : κ → Fin N) :
    Matrix κ κ ℚ :=
  M.submatrix r r - M.submatrix r p * (M.submatrix p p)⁻¹ * M.submatrix p r

theorem selectedSchur_reindex_selected {N : ℕ} {ι κ ρ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype ρ]
    (M : Matrix (Fin N) (Fin N) ℚ) (p : ι → Fin N) (r : ρ → Fin N)
    (e : κ ≃ ι) :
    selectedSchur M (p ∘ e) r = selectedSchur M p r := by
  change M.submatrix r r -
      (M.submatrix r p).submatrix id e * ((M.submatrix p p).submatrix e e)⁻¹ *
        (M.submatrix p r).submatrix e id = _
  simp only [Matrix.inv_submatrix_equiv, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_id_id, selectedSchur]

theorem selectedSchur_restrict {N k t u : ℕ}
    (M : Matrix (Fin N) (Fin N) ℚ) (p : Fin k → Fin N) (r : Fin t → Fin N)
    (f : Fin u → Fin t) :
    selectedSchur M p (r ∘ f) = (selectedSchur M p r).submatrix f f := by
  ext i j
  simp [selectedSchur, Matrix.mul_apply, Function.comp_def]

theorem originalBorder_reindex {N k : ℕ}
    (M : Matrix (Fin N) (Fin N) ℚ) (p : Fin k → Fin N) (i j : Fin N) :
    (M.submatrix (Fin.snoc p i) (Fin.snoc p j)).submatrix
        (appendIndexEquiv k) (appendIndexEquiv k) =
      Matrix.fromBlocks (M.submatrix p p)
        (fun x _ => M (p x) j : Matrix (Fin k) Unit ℚ)
        (fun _ y => M i (p y) : Matrix Unit (Fin k) ℚ)
        (fun _ _ => M i j : Matrix Unit Unit ℚ) := by
  ext x y
  cases x <;> cases y <;> simp [appendIndexEquiv, Matrix.submatrix] <;> rfl

theorem selectedSchur_entry_minor_ratio {N k t : ℕ}
    (M : Matrix (Fin N) (Fin N) ℚ) (p : Fin k → Fin N) (r : Fin t → Fin N)
    (hp : (M.submatrix p p).det ≠ 0) (i j : Fin t) :
    selectedSchur M p r i j =
      (M.submatrix (Fin.snoc p (r i)) (Fin.snoc p (r j))).det /
        (M.submatrix p p).det := by
  have h := KS.W30.schur_scalar_det_ratio (M.submatrix p p)
    (fun x _ => M (p x) (r j)) (fun _ y => M (r i) (p y))
    (fun _ _ => M (r i) (r j)) hp
  have hd := congrArg Matrix.det (originalBorder_reindex M p (r i) (r j))
  simp only [Matrix.det_submatrix_equiv_self] at hd
  rw [← hd] at h
  exact h

theorem selectedSchur_multiplier_minor_ratio {N k t : ℕ}
    (M : Matrix (Fin N) (Fin N) ℚ) (p : Fin k → Fin N)
    (r : Fin (t + 1) → Fin N) (hp : (M.submatrix p p).det ≠ 0)
    (ha : selectedSchur M p r 0 0 ≠ 0) (i : Fin (t + 1)) :
    selectedSchur M p r i 0 / selectedSchur M p r 0 0 =
      (M.submatrix (Fin.snoc p (r i)) (Fin.snoc p (r 0))).det /
        (M.submatrix (Fin.snoc p (r 0)) (Fin.snoc p (r 0))).det := by
  rw [selectedSchur_entry_minor_ratio M p r hp i 0,
    selectedSchur_entry_minor_ratio M p r hp 0 0]
  have hborder : (M.submatrix (Fin.snoc p (r 0)) (Fin.snoc p (r 0))).det ≠ 0 := by
    intro hz
    apply ha
    rw [selectedSchur_entry_minor_ratio M p r hp 0 0, hz, zero_div]
  field_simp [hp, hborder]

theorem selectedSchur_new_det_ne_zero {N k t : ℕ}
    (M : Matrix (Fin N) (Fin N) ℚ) (p : Fin k → Fin N)
    (r : Fin (t + 1) → Fin N) (hp : (M.submatrix p p).det ≠ 0)
    (ha : selectedSchur M p r 0 0 ≠ 0) :
    (M.submatrix (Fin.snoc p (r 0)) (Fin.snoc p (r 0))).det ≠ 0 := by
  intro hz
  apply ha
  rw [selectedSchur_entry_minor_ratio M p r hp 0 0, hz, zero_div]

theorem selectedSchur_append_step {N k t : ℕ}
    (M : Matrix (Fin N) (Fin N) ℚ) (p : Fin k → Fin N)
    (r : Fin (t + 1) → Fin N) (hp : (M.submatrix p p).det ≠ 0)
    (ha : selectedSchur M p r 0 0 ≠ 0) :
    selectedSchur M (Fin.snoc p (r 0)) (fun i => r i.succ) =
      KS.W17.schurTail (selectedSchur M p r) := by
  let A := M.submatrix p p
  let B : Matrix (Fin k) Unit ℚ := fun i _ => M (p i) (r 0)
  let C : Matrix Unit (Fin k) ℚ := fun _ j => M (r 0) (p j)
  let D := scalarPivot (M (r 0) (r 0))
  let F := M.submatrix p (fun i : Fin t => r i.succ)
  let G : Matrix Unit (Fin t) ℚ := fun _ j => M (r 0) (r j.succ)
  let H := M.submatrix (fun i : Fin t => r i.succ) p
  let I : Matrix (Fin t) Unit ℚ := fun i _ => M (r i.succ) (r 0)
  let J := M.submatrix (fun i : Fin t => r i.succ) (fun i : Fin t => r i.succ)
  let S := selectedSchur M p r
  have hhead : D - C * A⁻¹ * B = scalarPivot (S 0 0) := by
    ext i j
    cases i; cases j
    rfl
  have hrow : G - C * A⁻¹ * F = (fun _ j => S 0 j.succ : Matrix Unit (Fin t) ℚ) := by
    ext i j
    cases i
    rfl
  have hcol : I - H * A⁻¹ * B = (fun i _ => S i.succ 0 : Matrix (Fin t) Unit ℚ) := by
    ext i j
    cases j
    rfl
  have htail : J - H * A⁻¹ * F = KS.W17.trailingMatrix S := by
    ext i j
    rfl
  have hdet : (D - C * A⁻¹ * B).det ≠ 0 := by
    rw [hhead, Matrix.det_unique]
    exact ha
  have hmap : Fin.snoc p (r 0) ∘ appendIndexEquiv k =
      Sum.elim p (fun _ : Unit => r 0) := by
    funext i
    cases i <;> simp [appendIndexEquiv]
  rw [← selectedSchur_reindex_selected M (Fin.snoc p (r 0))
    (fun i : Fin t => r i.succ) (appendIndexEquiv k), hmap]
  have hfull : M.submatrix (Sum.elim p (fun _ : Unit => r 0))
      (Sum.elim p (fun _ : Unit => r 0)) = Matrix.fromBlocks A B C D := by
    ext i j
    cases i <;> cases j <;> rfl
  have hleft : M.submatrix (fun i : Fin t => r i.succ)
      (Sum.elim p (fun _ : Unit => r 0)) = Matrix.fromCols H I := by
    ext i j
    cases j <;> rfl
  have hright : M.submatrix (Sum.elim p (fun _ : Unit => r 0))
      (fun i : Fin t => r i.succ) = Matrix.fromRows F G := by
    ext i j
    cases i <;> rfl
  unfold selectedSchur
  rw [hfull, hleft, hright]
  change J - Matrix.fromCols H I * (Matrix.fromBlocks A B C D)⁻¹ * Matrix.fromRows F G = _
  rw [KS.W30.nested_schur A B C D F G H I J hp hdet,
    hhead, hrow, hcol, htail, scalarPivot_inv ha]
  ext i j
  change S i.succ j.succ -
      (∑ _ : Unit, (∑ _ : Unit, S i.succ 0 * (S 0 0)⁻¹) * S 0 j.succ) =
    S i.succ j.succ - S i.succ 0 * S 0 j.succ / S 0 0
  simp only [Finset.univ_unique, Finset.sum_singleton]
  ring

inductive PivotTrace {N : ℕ} (M : Matrix (Fin N) (Fin N) ℚ) :
    {k t : ℕ} → (Fin k → Fin N) → (Fin t → Fin N) →
      Matrix (Fin t) (Fin t) ℚ → Prop
  | initial : PivotTrace M (fun i : Fin 0 => Fin.elim0 i) id M
  | zero {k t : ℕ} {p : Fin k → Fin N} {r : Fin (t + 1) → Fin N}
      {S : Matrix (Fin (t + 1)) (Fin (t + 1)) ℚ}
      (previous : PivotTrace M p r S) (pivot_zero : S 0 0 = 0) :
      PivotTrace M p (fun i => r i.succ) (KS.W17.schurTail S)
  | positive {k t : ℕ} {p : Fin k → Fin N} {r : Fin (t + 1) → Fin N}
      {S : Matrix (Fin (t + 1)) (Fin (t + 1)) ℚ}
      (previous : PivotTrace M p r S) (pivot_positive : 0 < S 0 0) :
      PivotTrace M (Fin.snoc p (r 0)) (fun i => r i.succ) (KS.W17.schurTail S)

theorem PivotTrace.originalSchur {N k t : ℕ}
    {M : Matrix (Fin N) (Fin N) ℚ} {p : Fin k → Fin N} {r : Fin t → Fin N}
    {S : Matrix (Fin t) (Fin t) ℚ} (h : PivotTrace M p r S) :
    (M.submatrix p p).det ≠ 0 ∧ S = selectedSchur M p r := by
  induction h with
  | initial =>
    constructor
    · simp
    · ext i j
      simp [selectedSchur]
  | @zero k t p r S previous hz ih =>
    obtain ⟨hp, hs⟩ := ih
    refine ⟨hp, ?_⟩
    calc
      KS.W17.schurTail S = S.submatrix Fin.succ Fin.succ := by
        ext i j
        simp [KS.W17.schurTail, hz]
      _ = (selectedSchur M p r).submatrix Fin.succ Fin.succ := by rw [hs]
      _ = selectedSchur M p (fun i => r i.succ) :=
        (selectedSchur_restrict M p r Fin.succ).symm
  | @positive k t p r S previous hpos ih =>
    obtain ⟨hp, hs⟩ := ih
    have ha : selectedSchur M p r 0 0 ≠ 0 := by
      rw [← hs]
      exact ne_of_gt hpos
    refine ⟨selectedSchur_new_det_ne_zero M p r hp ha, ?_⟩
    rw [hs]
    exact (selectedSchur_append_step M p r hp ha).symm

theorem PivotTrace.size_bound {N k t : ℕ}
    {M : Matrix (Fin N) (Fin N) ℚ} {p : Fin k → Fin N} {r : Fin t → Fin N}
    {S : Matrix (Fin t) (Fin t) ℚ} (h : PivotTrace M p r S) : k + t ≤ N := by
  induction h <;> omega

theorem PivotTrace.state_posSemidef {N k t : ℕ}
    {M : Matrix (Fin N) (Fin N) ℚ} {p : Fin k → Fin N} {r : Fin t → Fin N}
    {S : Matrix (Fin t) (Fin t) ℚ} (h : PivotTrace M p r S)
    (hM : (M.map (fun q : ℚ => (q : ℝ))).PosSemidef) :
    (S.map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  induction h with
  | initial => exact hM
  | zero _ _ ih => exact fin_schurTail_posSemidef _ ih
  | positive _ _ ih => exact fin_schurTail_posSemidef _ ih

theorem PivotTrace.entry_minor_ratio {N k t : ℕ}
    {M : Matrix (Fin N) (Fin N) ℚ} {p : Fin k → Fin N} {r : Fin t → Fin N}
    {S : Matrix (Fin t) (Fin t) ℚ} (h : PivotTrace M p r S) (i j : Fin t) :
    S i j = (M.submatrix (Fin.snoc p (r i)) (Fin.snoc p (r j))).det /
      (M.submatrix p p).det := by
  obtain ⟨hp, hs⟩ := h.originalSchur
  rw [hs]
  exact selectedSchur_entry_minor_ratio M p r hp i j

theorem PivotTrace.multiplier_minor_ratio {N k t : ℕ}
    {M : Matrix (Fin N) (Fin N) ℚ} {p : Fin k → Fin N}
    {r : Fin (t + 1) → Fin N} {S : Matrix (Fin (t + 1)) (Fin (t + 1)) ℚ}
    (h : PivotTrace M p r S) (ha : S 0 0 ≠ 0) (i : Fin (t + 1)) :
    S i 0 / S 0 0 =
      (M.submatrix (Fin.snoc p (r i)) (Fin.snoc p (r 0))).det /
        (M.submatrix (Fin.snoc p (r 0)) (Fin.snoc p (r 0))).det := by
  obtain ⟨hp, hs⟩ := h.originalSchur
  rw [hs] at ha ⊢
  exact selectedSchur_multiplier_minor_ratio M p r hp ha i

end KS.W07

end OAI
