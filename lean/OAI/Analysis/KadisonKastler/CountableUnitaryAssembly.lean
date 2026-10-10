import OAI.Analysis.KadisonKastler.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

/-! # Assembling the dimension strata by a Hilbert direct sum -/

namespace KadisonKastler

noncomputable section

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace ℂ (E n)] [∀ n, CompleteSpace (E n)]

def l2FiberUnitaryApply (U : ∀ n, unitary (E n →L[ℂ] E n)) (f : lp E 2) : lp E 2 :=
  ⟨fun n => (U n : E n →L[ℂ] E n) (f n),
    (lp.memℓp f).mono' (fun n => (Unitary.norm_map (U n) (f n)).le)⟩

@[simp] theorem l2FiberUnitaryApply_apply (U : ∀ n, unitary (E n →L[ℂ] E n))
    (f : lp E 2) (n : ℕ) :
    l2FiberUnitaryApply U f n = (U n : E n →L[ℂ] E n) (f n) := rfl

theorem norm_l2FiberUnitaryApply (U : ∀ n, unitary (E n →L[ℂ] E n)) (f : lp E 2) :
    ‖l2FiberUnitaryApply U f‖ = ‖f‖ := by
  apply le_antisymm
  · exact lp.norm_mono (by norm_num) fun n => (Unitary.norm_map (U n) (f n)).le
  · exact lp.norm_mono (by norm_num) fun n => (Unitary.norm_map (U n) (f n)).ge

def l2FiberUnitaryEquiv (U : ∀ n, unitary (E n →L[ℂ] E n)) : lp E 2 ≃ₗᵢ[ℂ] lp E 2 where
  toFun := l2FiberUnitaryApply U
  invFun := l2FiberUnitaryApply (fun n => star (U n))
  map_add' f g := by
    apply lp.ext
    funext n
    simp only [l2FiberUnitaryApply_apply, lp.coeFn_add, Pi.add_apply, map_add]
  map_smul' c f := by
    apply lp.ext
    funext n
    simp only [l2FiberUnitaryApply_apply, lp.coeFn_smul, Pi.smul_apply, map_smul,
      RingHom.id_apply]
  norm_map' := norm_l2FiberUnitaryApply U
  left_inv f := by
    apply lp.ext
    funext n
    exact congrArg (fun T : E n →L[ℂ] E n => T (f n)) (U n).property.1
  right_inv f := by
    apply lp.ext
    funext n
    exact congrArg (fun T : E n →L[ℂ] E n => T (f n)) (U n).property.2

def l2FiberUnitary (U : ∀ n, unitary (E n →L[ℂ] E n)) : unitary (lp E 2 →L[ℂ] lp E 2) :=
  Unitary.linearIsometryEquiv.symm (l2FiberUnitaryEquiv U)

@[simp] theorem l2FiberUnitary_apply (U : ∀ n, unitary (E n →L[ℂ] E n))
    (f : lp E 2) (n : ℕ) :
    ((l2FiberUnitary U : lp E 2 →L[ℂ] lp E 2) f) n = (U n : E n →L[ℂ] E n) (f n) := rfl

theorem norm_l2FiberUnitary_sub_one_le (U : ∀ n, unitary (E n →L[ℂ] E n))
    {a : ℝ} (ha : 0 ≤ a) (hU : ∀ n, ‖(U n : E n →L[ℂ] E n) - 1‖ ≤ a) :
    ‖(l2FiberUnitary U : lp E 2 →L[ℂ] lp E 2) - 1‖ ≤ a := by
  apply ContinuousLinearMap.opNorm_le_bound _ ha
  intro f
  calc
    ‖((l2FiberUnitary U : lp E 2 →L[ℂ] lp E 2) - 1) f‖ ≤ ‖(a : ℂ) • f‖ := by
      apply lp.norm_mono (by norm_num)
      intro n
      have h := (((U n : E n →L[ℂ] E n) - 1).le_opNorm (f n)).trans
        (mul_le_mul_of_nonneg_right (hU n) (norm_nonneg _))
      simpa only [sub_apply, one_apply_eq_self, lp.coeFn_sub, Pi.sub_apply,
        l2FiberUnitary_apply, lp.coeFn_smul, Pi.smul_apply, norm_smul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha] using h
    _ = a * ‖f‖ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]

end

end KadisonKastler

end OAI
