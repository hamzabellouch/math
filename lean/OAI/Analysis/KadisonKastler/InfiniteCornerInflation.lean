import OAI.Analysis.KadisonKastler.CornerUnitary
import Mathlib.Analysis.InnerProductSpace.l2Space

namespace OAI

/-! # Inflation through countably many matrix corners

The hypotheses are the algebraic matrix-unit relations and the strong sum
of their diagonal projections. They give an actual Hilbert direct-sum
decomposition. A corner operator is then applied on each summand; in
particular a corner unitary inflates with no loss in displacement.
-/

namespace KadisonKastler

open scoped BigOperators Topology
open Filter

noncomputable section

section Diagonal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

abbrev CountableHilbertSum (E : Type*) [NormedAddCommGroup E] := lp (fun _ : ℕ => E) 2

def l2DiagonalLinear (T : E →L[ℂ] E) :
    CountableHilbertSum E →ₗ[ℂ] CountableHilbertSum E where
  toFun x := ⟨fun i => T (x i),
    ((lp.memℓp x).norm.const_mul ‖T‖).mono (fun i => T.le_opNorm (x i))⟩
  map_add' x y := by ext i; exact map_add T (x i) (y i)
  map_smul' c x := by ext i; exact map_smul T c (x i)

theorem norm_l2DiagonalLinear_le (T : E →L[ℂ] E) (x : CountableHilbertSum E) :
    ‖l2DiagonalLinear T x‖ ≤ ‖T‖ * ‖x‖ := by
  have h : ‖l2DiagonalLinear T x‖ ≤ ‖(‖T‖ : ℝ) • x‖ :=
    lp.norm_mono (by norm_num) (fun i => by
      change ‖T (x i)‖ ≤ ‖(‖T‖ : ℝ) • x i‖
      simpa only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg T)] using T.le_opNorm (x i))
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg T)] using h

def l2Diagonal (T : E →L[ℂ] E) : CountableHilbertSum E →L[ℂ] CountableHilbertSum E :=
  (l2DiagonalLinear T).mkContinuous ‖T‖ (norm_l2DiagonalLinear_le T)

@[simp] theorem l2Diagonal_apply (T : E →L[ℂ] E) (x : CountableHilbertSum E) (i : ℕ) :
    l2Diagonal T x i = T (x i) := rfl

theorem norm_l2Diagonal_le (T : E →L[ℂ] E) : ‖l2Diagonal T‖ ≤ ‖T‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) (norm_l2DiagonalLinear_le T)

@[simp] theorem l2Diagonal_single (T : E →L[ℂ] E) (i : ℕ) (x : E) :
    l2Diagonal T (lp.single 2 i x) = lp.single 2 i (T x) := by
  ext j
  by_cases h : j = i <;> simp [l2Diagonal_apply, lp.single_apply, h]

variable [CompleteSpace E]

theorem l2Diagonal_star (T : E →L[ℂ] E) :
    l2Diagonal (star T) = star (l2Diagonal T) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    lp.inner_eq_tsum, l2Diagonal_apply]

def l2DiagonalHom : (E →L[ℂ] E) →⋆ₐ[ℂ]
    (CountableHilbertSum E →L[ℂ] CountableHilbertSum E) where
  toFun := l2Diagonal
  map_one' := by ext x i; rfl
  map_mul' T S := by ext x i; rfl
  map_zero' := by ext x i; rfl
  map_add' T S := by ext x i; rfl
  commutes' c := by ext x i; rfl
  map_star' := l2Diagonal_star

end Diagonal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : Submodule ℂ H) [CompleteSpace E]

/-- Actual countable matrix units with initial corner `E` and strong sum one. -/
structure FullMatrixCorner where
  entry : ℕ → ℕ → (H →L[ℂ] H)
  star_entry : ∀ i j, star (entry i j) = entry j i
  mul_entry : ∀ i j k l, entry i j * entry k l = if j = k then entry i l else 0
  zero_zero : entry 0 0 = E.starProjection
  total : ∀ x : H, HasSum (fun i => entry i i x) x

namespace FullMatrixCorner

variable {E} (F : FullMatrixCorner E)

def columnLinear (i : ℕ) : E →ₗ[ℂ] H := (F.entry i 0).toLinearMap.comp E.subtype

theorem inner_columns (i j : ℕ) (x y : E) :
    inner ℂ (F.entry i 0 x) (F.entry j 0 y) =
      if i = j then inner ℂ x y else 0 := by
  calc
    inner ℂ (F.entry i 0 x) (F.entry j 0 y) =
        inner ℂ (x : H) ((star (F.entry i 0) * F.entry j 0) (y : H)) := by
      rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_right]
    _ = if i = j then inner ℂ x y else 0 := by
      rw [F.star_entry, F.mul_entry]
      split_ifs with h
      · rw [F.zero_zero, Submodule.starProjection_mem_subspace_eq_self]
        rfl
      · simp

def column (i : ℕ) : E →ₗᵢ[ℂ] H where
  toLinearMap := F.columnLinear i
  norm_map' := (LinearMap.norm_map_iff_inner_map_map (F.columnLinear i)).mpr
    (fun x y => by simpa [columnLinear] using
      F.inner_columns i i x y)

@[simp] theorem column_apply (i : ℕ) (x : E) : F.column i x = F.entry i 0 x := rfl

theorem columns_orthogonal : OrthogonalFamily ℂ (fun _ : ℕ => E) F.column := by
  intro i j hij x y
  simpa only [column_apply, ite_eq_right hij] using F.inner_columns i j x y

theorem diagonal_apply (i : ℕ) (x : H) :
    F.entry i i x = F.column i (E.orthogonalProjectionOnto (F.entry 0 i x)) := by
  change F.entry i i x = (F.entry i 0 * E.starProjection * F.entry 0 i) x
  rw [← F.zero_zero, F.mul_entry, ite_eq_left rfl, F.mul_entry, ite_eq_left rfl]

theorem columns_total :
    ⊤ ≤ (⨆ i, LinearMap.range (F.column i).toLinearMap).topologicalClosure := by
  intro x _
  apply mem_closure_of_tendsto (F.total x)
  apply Eventually.of_forall
  intro s
  apply Submodule.sum_mem
  intro i _
  apply le_iSup (fun j => LinearMap.range (F.column j).toLinearMap) i
  exact ⟨E.orthogonalProjectionOnto (F.entry 0 i x), (F.diagonal_apply i x).symm⟩

theorem hilbertSum : IsHilbertSum ℂ (fun _ : ℕ => E) F.column :=
  IsHilbertSum.mk F.columns_orthogonal F.columns_total

/-- The coordinate equivalence obtained from the actual matrix units. -/
def coordinates : H ≃ₗᵢ[ℂ] CountableHilbertSum E := F.hilbertSum.linearIsometryEquiv

@[simp] theorem coordinates_symm_single (i : ℕ) (x : E) :
    F.coordinates.symm (lp.single 2 i x) = F.column i x :=
  F.hilbertSum.linearIsometryEquiv_symm_apply_single x

@[simp] theorem coordinates_column (i : ℕ) (x : E) :
    F.coordinates (F.column i x) = lp.single 2 i x := by
  rw [← F.coordinates_symm_single, F.coordinates.apply_symm_apply]

theorem column_adjoint_apply (i : ℕ) (x : H) :
    (F.column i).toContinuousLinearMap.adjoint x =
      E.orthogonalProjectionOnto (F.entry 0 i x) := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (F.entry i 0 y) x =
    inner ℂ y (E.orthogonalProjectionOnto (F.entry 0 i x))
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  rw [← F.star_entry i 0, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

theorem coordinates_apply (x : H) (i : ℕ) :
    F.coordinates x i = E.orthogonalProjectionOnto (F.entry 0 i x) := by
  rw [← F.column_adjoint_apply]
  apply ext_inner_left ℂ
  intro y
  calc
    inner ℂ y (F.coordinates x i) =
        inner ℂ (lp.single 2 i y) (F.coordinates x) :=
      (lp.inner_single_left (𝕜 := ℂ) i y (F.coordinates x)).symm
    _ = inner ℂ (F.coordinates.symm (lp.single 2 i y))
        (F.coordinates.symm (F.coordinates x)) :=
      (F.coordinates.symm.inner_map_map _ _).symm
    _ = inner ℂ (F.column i y) x := by
      rw [F.coordinates_symm_single, F.coordinates.symm_apply_apply]
    _ = inner ℂ y ((F.column i).toContinuousLinearMap.adjoint x) :=
      (ContinuousLinearMap.adjoint_inner_right (F.column i).toContinuousLinearMap y x).symm

/-- Inflate a corner operator by the same operator on every matrix summand. -/
def inflateHom : (E →L[ℂ] E) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  F.coordinates.symm.conjStarAlgEquiv.toStarAlgHom.comp l2DiagonalHom

theorem inflateHom_apply (T : E →L[ℂ] E) (x : H) :
    F.inflateHom T x = F.coordinates.symm (l2Diagonal T (F.coordinates x)) := rfl

theorem norm_inflateHom_le (T : E →L[ℂ] E) : ‖F.inflateHom T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  rw [F.inflateHom_apply, F.coordinates.symm.norm_map]
  exact (l2Diagonal T).le_opNorm (F.coordinates x) |>.trans
    (mul_le_mul_of_nonneg_right (norm_l2Diagonal_le T) (norm_nonneg _)) |>.trans_eq
      (by rw [F.coordinates.norm_map])

@[simp] theorem inflateHom_column (T : E →L[ℂ] E) (i : ℕ) (x : E) :
    F.inflateHom T (F.column i x) = F.column i (T x) := by
  rw [F.inflateHom_apply, F.coordinates_column, l2Diagonal_single,
    F.coordinates_symm_single]

/-- The constructed operator is the strong sum of its actual matrix-corner
copies, rather than an abstract operator with prescribed coefficients. -/
theorem hasSum_inflateHom (T : E →L[ℂ] E) (x : H) :
    HasSum (fun i => (F.entry i 0 * cornerExtension E T * F.entry 0 i) x)
      (F.inflateHom T x) := by
  have h := F.hilbertSum.hasSum_linearIsometryEquiv_symm (l2Diagonal T (F.coordinates x))
  change HasSum (fun i => F.column i (l2Diagonal T (F.coordinates x) i))
    (F.inflateHom T x) at h
  simpa only [l2Diagonal_apply, F.coordinates_apply, column_apply,
    mul_apply_eq_comp, cornerExtension_apply] using h

/-- The actual unitary on the whole Hilbert space obtained from a corner unitary. -/
def inflateUnitary (v : unitary (E →L[ℂ] E)) : unitary (H →L[ℂ] H) :=
  Unitary.map ({
    toFun := F.inflateHom
    map_one' := F.inflateHom.map_one'
    map_mul' := F.inflateHom.map_mul'
    map_star' := F.inflateHom.map_star' } : (E →L[ℂ] E) →⋆* (H →L[ℂ] H)) v

@[simp] theorem coe_inflateUnitary (v : unitary (E →L[ℂ] E)) :
    (F.inflateUnitary v : H →L[ℂ] H) = F.inflateHom (v : E →L[ℂ] E) := rfl

theorem norm_inflateUnitary_sub_one_le (v : unitary (E →L[ℂ] E)) :
    ‖(F.inflateUnitary v : H →L[ℂ] H) - 1‖ ≤ ‖(v : E →L[ℂ] E) - 1‖ := by
  have he : (F.inflateUnitary v : H →L[ℂ] H) - 1 =
      F.inflateHom ((v : E →L[ℂ] E) - 1) := by
    rw [map_sub, map_one]
    rfl
  rw [he]
  exact F.norm_inflateHom_le _

def matrixEntry (T : H →L[ℂ] H) (i j : ℕ) : E →L[ℂ] E :=
  (F.column i).toContinuousLinearMap.adjoint.comp
    (T.comp (F.column j).toContinuousLinearMap)

theorem matrixEntry_apply (T : H →L[ℂ] H) (i j : ℕ) (x : E) :
    F.matrixEntry T i j x =
      E.orthogonalProjectionOnto (F.entry 0 i (T (F.entry j 0 x))) := by
  exact F.column_adjoint_apply i _

/-- Matrix coefficients of the inflated unitary conjugation are the original
corner conjugation, with no change of representation or norm. -/
theorem matrixEntry_unitaryConj (v : unitary (E →L[ℂ] E))
    (T : H →L[ℂ] H) (i j : ℕ) :
    F.matrixEntry (unitaryConj (F.inflateUnitary v) T) i j =
      unitaryConj v (F.matrixEntry T i j) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  have hs (k : ℕ) (z : E) :
      star (F.inflateUnitary v : H →L[ℂ] H) (F.column k z) =
        F.column k (star (v : E →L[ℂ] E) z) := by
    rw [coe_inflateUnitary, ← map_star]
    exact F.inflateHom_column _ k z
  change inner ℂ y ((F.column i).toContinuousLinearMap.adjoint
      ((F.inflateUnitary v : H →L[ℂ] H)
        (T (star (F.inflateUnitary v : H →L[ℂ] H) (F.column j x))))) =
    inner ℂ y ((v : E →L[ℂ] E)
      ((F.column i).toContinuousLinearMap.adjoint
        (T (F.column j (star (v : E →L[ℂ] E) x)))))
  rw [ContinuousLinearMap.adjoint_inner_right]
  rw [← ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ (star (F.inflateUnitary v : H →L[ℂ] H) (F.column i y))
      (T (star (F.inflateUnitary v : H →L[ℂ] H) (F.column j x))) = _
  rw [hs, hs]
  rw [← ContinuousLinearMap.adjoint_inner_left (v : E →L[ℂ] E)
    ((F.column i).toContinuousLinearMap.adjoint
      (T (F.column j (star (v : E →L[ℂ] E) x)))) y]
  rw [ContinuousLinearMap.adjoint_inner_right]
  rfl

end FullMatrixCorner

end

end KadisonKastler

end OAI
