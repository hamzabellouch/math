import OAI.Geometry.HeilbronnTriangle.LatticeSplit

namespace OAI


noncomputable section
namespace Problem355.LatticeSplit
open Module
open scoped Matrix

def twoPlusOneEquiv : (Fin 2 ⊕ Unit) ≃ Fin 3 where
  toFun x := match x with
    | .inl i => i.castSucc
    | .inr _ => 2
  invFun i := if h : i.val < 2 then .inl ⟨i.val, h⟩ else .inr ()
  left_inv x := by
    cases x with
    | inl i => simp; omega
    | inr u => cases u; rfl
  right_inv i := by fin_cases i <;> rfl

@[simp] theorem twoPlusOneEquiv_symm_zero : twoPlusOneEquiv.symm 0 = .inl 0 := rfl
@[simp] theorem twoPlusOneEquiv_symm_one : twoPlusOneEquiv.symm 1 = .inl 1 := rfl
@[simp] theorem twoPlusOneEquiv_symm_two : twoPlusOneEquiv.symm 2 = .inr () := rfl

variable {A : Type*} [AddCommGroup A]

def extendIntegerKernelBasis3 (f : A →ₗ[ℤ] ℤ) (g : ℤ) (hg : g ≠ 0)
    (hdiv : ∀ x, g ∣ f x) (u : A) (hu : f u = g)
    (b : Basis (Fin 2) ℤ (LinearMap.ker f)) : Basis (Fin 3) ℤ A :=
  (extendIntegerKernelBasis f g hg hdiv u hu b).reindex twoPlusOneEquiv

@[simp] theorem extendIntegerKernelBasis3_zero
    (f : A →ₗ[ℤ] ℤ) (g : ℤ) (hg : g ≠ 0) (hdiv : ∀ x, g ∣ f x)
    (u : A) (hu : f u = g) (b : Basis (Fin 2) ℤ (LinearMap.ker f)) :
    extendIntegerKernelBasis3 f g hg hdiv u hu b 0 = (b 0 : A) := by
  simp [extendIntegerKernelBasis3]

@[simp] theorem extendIntegerKernelBasis3_one
    (f : A →ₗ[ℤ] ℤ) (g : ℤ) (hg : g ≠ 0) (hdiv : ∀ x, g ∣ f x)
    (u : A) (hu : f u = g) (b : Basis (Fin 2) ℤ (LinearMap.ker f)) :
    extendIntegerKernelBasis3 f g hg hdiv u hu b 1 = (b 1 : A) := by
  simp [extendIntegerKernelBasis3]

@[simp] theorem extendIntegerKernelBasis3_two
    (f : A →ₗ[ℤ] ℤ) (g : ℤ) (hg : g ≠ 0) (hdiv : ∀ x, g ∣ f x)
    (u : A) (hu : f u = g) (b : Basis (Fin 2) ℤ (LinearMap.ker f)) :
    extendIntegerKernelBasis3 f g hg hdiv u hu b 2 = u := by
  simp [extendIntegerKernelBasis3]

theorem index_eq_natAbs_det_basis (L : Submodule ℤ (Fin 3 → ℤ))
    (b : Basis (Fin 3) ℤ L) :
    L.toAddSubgroup.index = (Matrix.det (Matrix.of (fun i j => (b i : Fin 3 → ℤ) j))).natAbs := by
  have h := AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin 3)) L.toAddSubgroup b
  rw [Pi.basisFun_det_apply] at h
  convert h using 2

theorem abs_det_real_basis_eq_index (L : Submodule ℤ (Fin 3 → ℤ))
    (b : Basis (Fin 3) ℤ L) :
    |Matrix.det (Matrix.of (fun i j => ((b i : Fin 3 → ℤ) j : ℝ)))| = (L.toAddSubgroup.index : ℝ) := by
  rw [index_eq_natAbs_det_basis L b, Nat.cast_natAbs, Int.cast_abs, Int.cast_det]
  rfl

theorem abs_det_kernel_height_eq_index (L : Submodule ℤ (Fin 3 → ℤ))
    (f : L →ₗ[ℤ] ℤ) (g : ℤ) (hg : g ≠ 0) (hdiv : ∀ x, g ∣ f x)
    (u : L) (hu : f u = g) (b : Basis (Fin 2) ℤ (LinearMap.ker f)) :
    |Matrix.det ![fun j => (((b 0 : L) : Fin 3 → ℤ) j : ℝ),
      fun j => (((b 1 : L) : Fin 3 → ℤ) j : ℝ),
      fun j => ((u : Fin 3 → ℤ) j : ℝ)]| = (L.toAddSubgroup.index : ℝ) := by
  have h := abs_det_real_basis_eq_index L (extendIntegerKernelBasis3 f g hg hdiv u hu b)
  convert h using 2
  congr 1
  ext i j
  fin_cases i <;> simp

theorem abs_det_real_full_basis_eq_one (b : Basis (Fin 3) ℤ (Fin 3 → ℤ)) :
    |Matrix.det (Matrix.of (fun i j => (b i j : ℝ)))| = 1 := by
  have h := Int.isUnit_iff_abs_eq.mp ((Pi.basisFun ℤ (Fin 3)).isUnit_det b)
  rw [Pi.basisFun_det_apply] at h
  have hi : |Matrix.det (Matrix.of (fun i j => b i j))| = 1 := by
    convert h using 2
  have hd : Matrix.det (Matrix.of (fun i j => (b i j : ℝ))) =
      (Matrix.det (Matrix.of (fun i j => b i j)) : ℤ) := by
    rw [Int.cast_det]
    rfl
  rw [hd, ← Int.cast_abs, hi, Int.cast_one]

theorem abs_det_primitive_kernel_height_eq_one
    (f : (Fin 3 → ℤ) →ₗ[ℤ] ℤ) (u : Fin 3 → ℤ) (hu : f u = 1)
    (b : Basis (Fin 2) ℤ (LinearMap.ker f)) :
    |Matrix.det ![fun j => ((b 0 : Fin 3 → ℤ) j : ℝ),
      fun j => ((b 1 : Fin 3 → ℤ) j : ℝ), fun j => (u j : ℝ)]| = 1 := by
  have h := abs_det_real_full_basis_eq_one
    (extendIntegerKernelBasis3 f 1 one_ne_zero (fun _ => one_dvd _) u hu b)
  convert h using 2
  congr 1
  ext i j
  fin_cases i <;> simp

end Problem355.LatticeSplit

end

end OAI
