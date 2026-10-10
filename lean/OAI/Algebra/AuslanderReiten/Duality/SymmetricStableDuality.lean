import OAI.Algebra.AuslanderReiten.Modules.CoinducedEmbedding
import OAI.Algebra.AuslanderReiten.Stable.StableHom
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Pi

namespace OAI

namespace ArExplicit.FrobeniusTrace

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
variable {M N : Type u} [AddCommGroup M] [Module R M] [Module k M]
variable [IsScalarTower k R M] [AddCommGroup N] [Module R N] [Module k N]
variable [IsScalarTower k R N]

noncomputable def regularFromDual (φ : Module.Dual k M) : M →ₗ[R] R :=
  τ.leftEquiv.symm.toLinearMap.comp (Coinduced.adjoint φ)

def dualFromRegular (f : M →ₗ[R] R) : Module.Dual k M :=
  τ.trace.comp (f.restrictScalars k)

theorem trace_leftEquiv_symm (v : Coinduced k R) :
    τ.trace (τ.leftEquiv.symm v) = v.functional 1 := by
  have h := τ.leftEquiv_apply (τ.leftEquiv.symm v) 1
  simpa using h.symm

@[simp]
theorem dualFromRegular_regularFromDual (φ : Module.Dual k M) :
    τ.dualFromRegular (τ.regularFromDual φ) = φ := by
  ext x
  exact (τ.trace_leftEquiv_symm (Coinduced.adjoint φ x)).trans
    (Coinduced.adjoint_eval_one φ x)

@[simp]
theorem regularFromDual_dualFromRegular (f : M →ₗ[R] R) :
    τ.regularFromDual (τ.dualFromRegular f) = f := by
  ext x
  apply τ.leftEquiv.injective
  change τ.leftEquiv (τ.leftEquiv.symm (Coinduced.adjoint (τ.dualFromRegular f) x)) =
    τ.leftEquiv (f x)
  rw [τ.leftEquiv.apply_symm_apply]
  ext r
  change τ.trace (f (r • x)) = (τ.leftEquiv (f x)).functional r
  rw [map_smul, τ.leftEquiv_apply]
  rfl

noncomputable def dualModuleHomEquiv : Module.Dual k M ≃ₗ[k] (M →ₗ[R] R) where
  toFun := τ.regularFromDual
  invFun := τ.dualFromRegular
  left_inv := τ.dualFromRegular_regularFromDual
  right_inv := τ.regularFromDual_dualFromRegular
  map_add' φ ψ := by
    ext x
    apply τ.leftEquiv.injective
    simp only [regularFromDual, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearMap.add_apply, map_add]
    ext r
    rfl
  map_smul' c φ := by
    ext x
    apply τ.leftEquiv.injective
    change τ.leftEquiv (τ.leftEquiv.symm (Coinduced.adjoint (c • φ) x)) =
      τ.leftEquiv (c • τ.leftEquiv.symm (Coinduced.adjoint φ x))
    rw [τ.leftEquiv.apply_symm_apply]
    have hs := (τ.leftEquiv.restrictScalars k).map_smul c
      (τ.leftEquiv.symm (Coinduced.adjoint (R := R) φ x))
    change τ.leftEquiv (c • τ.leftEquiv.symm (Coinduced.adjoint (R := R) φ x)) =
      c • τ.leftEquiv (τ.leftEquiv.symm (Coinduced.adjoint (R := R) φ x)) at hs
    rw [τ.leftEquiv.apply_symm_apply] at hs
    rw [hs]
    ext r
    rfl

theorem dualModuleHomEquiv_precomp (φ : Module.Dual k N) (f : M →ₗ[R] N) :
    τ.dualModuleHomEquiv (φ.comp (f.restrictScalars k)) =
      (τ.dualModuleHomEquiv φ).comp f := by
  ext x
  apply τ.leftEquiv.injective
  change τ.leftEquiv (τ.leftEquiv.symm (Coinduced.adjoint (φ.comp (f.restrictScalars k)) x)) =
    τ.leftEquiv (τ.leftEquiv.symm (Coinduced.adjoint (R := R) φ (f x)))
  rw [τ.leftEquiv.apply_symm_apply, τ.leftEquiv.apply_symm_apply]
  ext r
  change φ (f (r • x)) = φ (r • f x)
  rw [map_smul]

variable [SMulCommClass R k M]

noncomputable def freeHomDualEquiv (r : ℕ) :
    Module.Dual k ((Fin r → R) →ₗ[R] M) ≃ₗ[k] (M →ₗ[R] (Fin r → R)) :=
  (LinearEquiv.piRing R M (Fin r) k).symm.dualMap |>.trans
    ((LinearMap.lsum k (fun _ : Fin r => M) k).symm.trans
      ((LinearEquiv.piCongrRight (fun _ : Fin r => τ.dualModuleHomEquiv)).trans
        (LinearEquiv.linearMapPi k)))

theorem freeHomDualEquiv_symm_apply (r : ℕ) (g : M →ₗ[R] (Fin r → R))
    (f : (Fin r → R) →ₗ[R] M) :
    (τ.freeHomDualEquiv r).symm g f =
      ∑ i : Fin r, τ.trace (g (f (Pi.single i 1)) i) := by
  simp [freeHomDualEquiv, LinearMap.lsum_apply, LinearEquiv.piRing_apply,
    dualModuleHomEquiv, dualFromRegular]

theorem free_map_apply (r : ℕ) (f : (Fin r → R) →ₗ[R] M) (v : Fin r → R) :
    f v = ∑ i : Fin r, v i • f (Pi.single i 1) := by
  have hv : v = ∑ i : Fin r, v i • Pi.single i (1 : R) := by
    ext j
    simp [Pi.single_apply]
  calc
    f v = f (∑ i : Fin r, v i • Pi.single i (1 : R)) := congrArg f hv
    _ = _ := by simp

def freeTrace (r : ℕ) (f : (Fin r → R) →ₗ[R] (Fin r → R)) : k :=
  ∑ i : Fin r, τ.trace (f (Pi.single i 1) i)

omit [Module.Finite k R] in
theorem trace_map_coordinate {r s : ℕ} (f : (Fin r → R) →ₗ[R] (Fin s → R))
    (v : Fin r → R) (i : Fin s) :
    τ.trace (f v i) = ∑ j : Fin r, τ.trace (v j * f (Pi.single j 1) i) := by
  rw [free_map_apply r f v]
  simp

omit [Module.Finite k R] in

theorem freeTrace_cyclic (hs : ∀ a b : R, τ.trace (a * b) = τ.trace (b * a))
    {r s : ℕ} (a : (Fin r → R) →ₗ[R] (Fin s → R))
    (b : (Fin s → R) →ₗ[R] (Fin r → R)) :
    τ.freeTrace r (b.comp a) = τ.freeTrace s (a.comp b) := by
  simp only [freeTrace, LinearMap.comp_apply]
  simp_rw [τ.trace_map_coordinate]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact hs _ _

theorem freeHomDual_naturality_source
    (hs : ∀ a b : R, τ.trace (a * b) = τ.trace (b * a))
    {r s : ℕ} (a : (Fin r → R) →ₗ[R] (Fin s → R))
    (f : (Fin s → R) →ₗ[R] M) (g : M →ₗ[R] (Fin r → R)) :
    (τ.freeHomDualEquiv r).symm g (f.comp a) =
      (τ.freeHomDualEquiv s).symm (a.comp g) f := by
  rw [freeHomDualEquiv_symm_apply, freeHomDualEquiv_symm_apply]
  exact τ.freeTrace_cyclic hs a (g.comp f)

theorem freeHomDual_naturality_target [SMulCommClass R k N]
    (r : ℕ) (u : M →ₗ[R] N) (f : (Fin r → R) →ₗ[R] M)
    (g : N →ₗ[R] (Fin r → R)) :
    (τ.freeHomDualEquiv r).symm g (u.comp f) =
      (τ.freeHomDualEquiv r).symm (g.comp u) f := by
  rw [freeHomDualEquiv_symm_apply, freeHomDualEquiv_symm_apply]
  rfl

end ArExplicit.FrobeniusTrace

end OAI
