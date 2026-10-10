import OAI.Analysis.Kaplansky.BundleWords
import OAI.Analysis.Kaplansky.Polynomials
import OAI.Geometry.ComplexBundle.StageMaps

namespace OAI

noncomputable section

/-! Bundle matrix polynomial evaluation, Hilbert isometries, and polynomial action. -/

open Bundle Topology
open scoped BigOperators
namespace Kaplansky
open ComplexGrassmann

/-- One term of a rectangular star polynomial, with its actual word and
its degree bound. Zero coefficients and empty words are allowed. -/
structure BoundedMatrixTerm (m n R : ℕ) where
  row : Fin m
  col : Fin n
  coeff : ℂ
  word : List (Bool × Fin 24)
  degree_le : word.length ≤ R

variable {ι : Type*} {K : ι → ℕ}

/-- The finite direct sum of the retained stages, for each matrix row. -/
def towerRetainedStage (a : ℕ → LineStage K) (m R : ℕ) : LineStage K :=
  LineStage.sum (fun _ : Fin m => LineStage.sum (fun j : Fin (R+1) => a j.val))

/-- The bottom bundle repeated once per matrix column. -/
def towerInputStage (a : ℕ → LineStage K) (n : ℕ) : LineStage K :=
  LineStage.sum (fun _ : Fin n => a 0)

variable {a : ℕ → LineStage K} (X : ∀ j, (a j).Step (a (j+1)))

def bundleMatrixTerm {m n R : ℕ} (t : BoundedMatrixTerm m n R) :
    ContinuousStageMap (towerInputStage a n) (towerRetainedStage a m R) := by
  let W := bundleWordValue X t.word
  let j : Fin (R+1) := ⟨W.level,Nat.lt_succ_of_le ((bundleWordValue_level_le X t.word).trans t.degree_le)⟩
  let wordMap : ContinuousStageMap (a 0) (a j.val) := ⟨W.map,W.continuous_map⟩
  exact ((ContinuousStageMap.inj (fun _ : Fin m =>
    LineStage.sum (fun k : Fin (R+1) => a k.val)) t.row).comp
    ((ContinuousStageMap.inj (fun k : Fin (R+1) => a k.val) j).comp
      (wordMap.comp (ContinuousStageMap.proj (fun _ : Fin n => a 0) t.col)))).smul t.coeff

/-- The intrinsic finite matrix restriction. Its continuity is proved from
actual normalized bundle maps and adjoints, including the constant term. -/
def bundleMatrixPolynomial {m n R : ℕ} {T : Type*} (s : Finset T)
    (t : T → BoundedMatrixTerm m n R) :
    ContinuousStageMap (towerInputStage a n) (towerRetainedStage a m R) :=
  ContinuousStageMap.sum s (fun k => bundleMatrixTerm X (t k))

theorem bundleMatrixPolynomial_continuous {m n R : ℕ} {T : Type*} (s : Finset T)
    (t : T → BoundedMatrixTerm m n R) :
    Continuous (fun z : TotalSpace (towerInputStage a n).Model (towerInputStage a n).Fiber =>
      TotalSpace.mk' (towerRetainedStage a m R).Model z.proj
        ((bundleMatrixPolynomial X s t).map z.proj z.2)) :=
  (bundleMatrixPolynomial X s t).continuous_map

abbrev MatrixPolynomialTermIndex {m n : ℕ} (p : Fin m → Fin n → StarWordPolynomial 24) :=
  Σ row : Fin m, Σ col : Fin n, {w // w ∈ (p row col).support}

def matrixPolynomialDegree {m n : ℕ} (p : Fin m → Fin n → StarWordPolynomial 24) : ℕ :=
  1 + Finset.univ.sup (fun k : MatrixPolynomialTermIndex p => k.2.2.val.length)

theorem matrixPolynomialDegree_pos {m n : ℕ} (p : Fin m → Fin n → StarWordPolynomial 24) :
    0 < matrixPolynomialDegree p := Nat.add_pos_left Nat.zero_lt_one _

/-- The common positive degree bound and the actual terms of a finite
rectangular polynomial matrix are produced from its entries. -/
def matrixPolynomialTerm {m n : ℕ} (p : Fin m → Fin n → StarWordPolynomial 24)
    (k : MatrixPolynomialTermIndex p) : BoundedMatrixTerm m n (matrixPolynomialDegree p) where
  row := k.1
  col := k.2.1
  coeff := p k.1 k.2.1 k.2.2.val
  word := k.2.2.val
  degree_le := (Finset.le_sup (f := fun k : MatrixPolynomialTermIndex p => k.2.2.val.length)
    (Finset.mem_univ k)).trans (Nat.le_add_left _ _)

theorem matrixPolynomialTerm_sum {m n : ℕ} (p : Fin m → Fin n → StarWordPolynomial 24)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Bool × Fin 24 → Module.End ℂ V) (v : Fin n → V) (row : Fin m) :
    (∑ k : MatrixPolynomialTermIndex p,
      if (matrixPolynomialTerm p k).row=row then (matrixPolynomialTerm p k).coeff •
        applyWord T (matrixPolynomialTerm p k).word (v (matrixPolynomialTerm p k).col) else 0) =
    ∑ col : Fin n, ∑ w ∈ (p row col).support, p row col w • applyWord T w (v col) := by
  classical
  simp only [MatrixPolynomialTermIndex,Fintype.sum_sigma,matrixPolynomialTerm]
  rw [Finset.sum_eq_single row]
  · simp only [ite_true]
    apply Finset.sum_congr rfl
    intro col _
    exact Finset.sum_coe_sort (p row col).support (fun w => p row col w • applyWord T w (v col))
  · intro k _ hk
    apply Finset.sum_eq_zero
    intro col _
    apply Finset.sum_eq_zero
    intro w _
    exact ite_eq_right hk
  · simp

def retainedRowHilbert (a : ℕ → LineStage K) (m R : ℕ)
    (y : ProjectiveProduct K) (row : Fin m) :
    (towerRetainedStage a m R).Fiber y →ₗ[ℂ] lp (fun j => (a j).Fiber y) 2 :=
  (finiteTowerHilbert a R y).comp
    (LineStage.sumProj (fun _ : Fin m => LineStage.sum (fun j : Fin (R+1) => a j.val)) row y)

/-- A matrix monomial has exactly its claimed shift-operator action in
each output row. No unspecified representation or evaluation is used. -/
theorem bundleMatrixTerm_shift_eval {m n R : ℕ} (t : BoundedMatrixTerm m n R)
    (y : ProjectiveProduct K) (v : (towerInputStage a n).Fiber y) (row : Fin m) :
    retainedRowHilbert a m R y row ((bundleMatrixTerm X t).map y v) =
      if t.row=row then t.coeff •
        applyWord (shiftLetter (fun i j => towerOperator X i y j)
          (fun i j => towerOperator_norm X i y j)) t.word
            (lp.single 2 0 (LineStage.sumProj (fun _ : Fin n => a 0) t.col y v)) else 0 := by
  classical
  let W := bundleWordValue X t.word
  let j : Fin (R+1) := ⟨W.level,Nat.lt_succ_of_le ((bundleWordValue_level_le X t.word).trans t.degree_le)⟩
  change finiteTowerHilbert a R y
    (LineStage.sumProj (fun _ : Fin m => LineStage.sum (fun k : Fin (R+1) => a k.val)) row y
      (t.coeff • LineStage.sumInj (fun _ : Fin m => LineStage.sum (fun k : Fin (R+1) => a k.val)) t.row y
        (LineStage.sumInj (fun k : Fin (R+1) => a k.val) j y
          (W.map y (LineStage.sumProj (fun _ : Fin n => a 0) t.col y v))))) = _
  rw [map_smul,map_smul]
  by_cases h : t.row=row
  · subst row
    simp only [LineStage.sumProj_sumInj_same,finiteTowerHilbert_inj,ite_true]
    rw [bundleWordValue_shift_eval]
    rfl
  · simp [LineStage.sumProj_sumInj_ne _ (Ne.symm h),h]
    rfl

/-- Exact evaluation agreement for the entire rectangular polynomial,
including all coefficients, rows, columns, constants, and adjoints. -/
theorem bundleMatrixPolynomial_shift_eval {m n R : ℕ} {T : Type*}
    (s : Finset T) (t : T → BoundedMatrixTerm m n R) (y : ProjectiveProduct K)
    (v : (towerInputStage a n).Fiber y) (row : Fin m) :
    retainedRowHilbert a m R y row ((bundleMatrixPolynomial X s t).map y v) =
      ∑ k ∈ s, if (t k).row=row then (t k).coeff •
        applyWord (shiftLetter (fun i j => towerOperator X i y j)
          (fun i j => towerOperator_norm X i y j)) (t k).word
            (lp.single 2 0 (LineStage.sumProj (fun _ : Fin n => a 0) (t k).col y v)) else 0 := by
  simp only [bundleMatrixPolynomial,ContinuousStageMap.sum,LinearMap.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact bundleMatrixTerm_shift_eval X (t k) y v row

abbrev MatrixTowerHilbert (a : ℕ → LineStage K) (n : ℕ) (y : ProjectiveProduct K) :=
  PiLp 2 (fun _ : Fin n => lp (fun j => (a j).Fiber y) 2)

def retainedMatrixHilbertMap (a : ℕ → LineStage K) (m R : ℕ) (y : ProjectiveProduct K) :
    (towerRetainedStage a m R).Fiber y →ₗ[ℂ] MatrixTowerHilbert a m y where
  toFun v := WithLp.toLp 2 (fun row => retainedRowHilbert a m R y row v)
  map_add' v w := by
    apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin m => lp (fun j => (a j).Fiber y) 2)).injective
    funext row
    exact map_add (retainedRowHilbert a m R y row) v w
  map_smul' c v := by
    apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin m => lp (fun j => (a j).Fiber y) 2)).injective
    funext row
    exact map_smul (retainedRowHilbert a m R y row) c v

theorem retainedMatrixHilbert_inner (a : ℕ → LineStage K) (m R : ℕ) (y : ProjectiveProduct K)
    (v w : (towerRetainedStage a m R).Fiber y) :
    inner ℂ (retainedMatrixHilbertMap a m R y v) (retainedMatrixHilbertMap a m R y w)=inner ℂ v w := by
  change (∑ row : Fin m, inner ℂ (retainedRowHilbert a m R y row v)
    (retainedRowHilbert a m R y row w))=inner ℂ v w
  exact (Finset.sum_congr rfl (fun row _ => finiteTowerHilbert_inner a R y
    (LineStage.sumProj (fun _ : Fin m => LineStage.sum (fun j : Fin (R+1) => a j.val)) row y v)
    (LineStage.sumProj (fun _ : Fin m => LineStage.sum (fun j : Fin (R+1) => a j.val)) row y w))).trans
      (LineStage.sum_inner _ y v w).symm

def retainedMatrixHilbertIsometry (a : ℕ → LineStage K) (m R : ℕ) (y : ProjectiveProduct K) :
    (towerRetainedStage a m R).Fiber y →ₗᵢ[ℂ] MatrixTowerHilbert a m y where
  toLinearMap := retainedMatrixHilbertMap a m R y
  norm_map' := (LinearMap.norm_map_iff_inner_map_map _).mpr (retainedMatrixHilbert_inner a m R y)

def inputMatrixHilbertMap (a : ℕ → LineStage K) (n : ℕ) (y : ProjectiveProduct K) :
    (towerInputStage a n).Fiber y →ₗ[ℂ] MatrixTowerHilbert a n y where
  toFun v := WithLp.toLp 2 (fun col => lp.single 2 0
    (LineStage.sumProj (fun _ : Fin n => a 0) col y v))
  map_add' v w := by
    apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => lp (fun j => (a j).Fiber y) 2)).injective
    funext col
    exact (congrArg (lp.single (E := fun j => (a j).Fiber y) 2 0)
      (map_add (LineStage.sumProj (fun _ : Fin n => a 0) col y) v w)).trans
      (lp.single_add (E := fun j => (a j).Fiber y) 2 0 _ _)
  map_smul' c v := by
    apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => lp (fun j => (a j).Fiber y) 2)).injective
    funext col
    exact (congrArg (lp.single (E := fun j => (a j).Fiber y) 2 0)
      (map_smul (LineStage.sumProj (fun _ : Fin n => a 0) col y) c v)).trans
      (lp.single_smul (E := fun j => (a j).Fiber y) 2 0 c _)

theorem inputMatrixHilbert_inner (a : ℕ → LineStage K) (n : ℕ) (y : ProjectiveProduct K)
    (v w : (towerInputStage a n).Fiber y) :
    inner ℂ (inputMatrixHilbertMap a n y v) (inputMatrixHilbertMap a n y w)=inner ℂ v w := by
  change (∑ col : Fin n, inner ℂ
    (lp.single 2 0 (LineStage.sumProj (fun _ : Fin n => a 0) col y v) : lp (fun j => (a j).Fiber y) 2)
    (lp.single 2 0 (LineStage.sumProj (fun _ : Fin n => a 0) col y w) : lp (fun j => (a j).Fiber y) 2))=inner ℂ v w
  simp only [lp.inner_single_left,lp.single_apply_self]
  exact (LineStage.sum_inner _ y v w).symm

def inputMatrixHilbertIsometry (a : ℕ → LineStage K) (n : ℕ) (y : ProjectiveProduct K) :
    (towerInputStage a n).Fiber y →ₗᵢ[ℂ] MatrixTowerHilbert a n y where
  toLinearMap := inputMatrixHilbertMap a n y
  norm_map' := (LinearMap.norm_map_iff_inner_map_map _).mpr (inputMatrixHilbert_inner a n y)

/-- Direct evaluated matrix action on Hilbert vectors, with every term
placed in its specified row and applied to its specified input column. -/
def matrixPolynomialAction {m n R : ℕ} {T : Type*} (s : Finset T)
    (t : T → BoundedMatrixTerm m n R) (y : ProjectiveProduct K)
    (v : MatrixTowerHilbert a n y) : MatrixTowerHilbert a m y :=
  WithLp.toLp 2 (fun row => ∑ k ∈ s, if (t k).row=row then (t k).coeff •
    applyWord (shiftLetter (fun i j => towerOperator X i y j)
      (fun i j => towerOperator_norm X i y j)) (t k).word (v (t k).col) else 0)

/-- The entire intrinsic matrix restriction agrees exactly with evaluation
on bottom-level inputs, through norm-preserving Hilbert embeddings. -/
theorem bundleMatrixPolynomial_evaluation {m n R : ℕ} {T : Type*}
    (s : Finset T) (t : T → BoundedMatrixTerm m n R) (y : ProjectiveProduct K)
    (v : (towerInputStage a n).Fiber y) :
    retainedMatrixHilbertIsometry a m R y ((bundleMatrixPolynomial X s t).map y v) =
      matrixPolynomialAction X s t y (inputMatrixHilbertIsometry a n y v) := by
  apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin m => lp (fun j => (a j).Fiber y) 2)).injective
  funext row
  exact bundleMatrixPolynomial_shift_eval X s t y v row

/-- A lower bound for the evaluated operator passes to the actual finite
bundle map. The two Hilbert inclusions are proved isometries. -/
theorem bundleMatrixPolynomial_lower_bound {m n R : ℕ} {T : Type*}
    (s : Finset T) (t : T → BoundedMatrixTerm m n R) (y : ProjectiveProduct K) (c : ℝ)
    (h : ∀ v : MatrixTowerHilbert a n y, c*‖v‖ ≤ ‖matrixPolynomialAction X s t y v‖)
    (v : (towerInputStage a n).Fiber y) :
    c*‖v‖ ≤ ‖(bundleMatrixPolynomial X s t).map y v‖ := by
  have hb := h (inputMatrixHilbertIsometry a n y v)
  rw [← bundleMatrixPolynomial_evaluation,LinearIsometry.norm_map,LinearIsometry.norm_map] at hb
  exact hb

end Kaplansky

end

end OAI
