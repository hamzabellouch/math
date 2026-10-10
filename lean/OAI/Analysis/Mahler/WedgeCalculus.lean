import OAI.Analysis.Mahler.WedgeAlgebra
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

namespace OAI

open scoped TensorProduct

namespace Mahler
variable {T : Type*} [AddCommGroup T] [Module ℝ T]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma wedge_summand_eval (a : T [⋀^ι]→ₗ[ℝ] ℂ) (b : T [⋀^κ]→ₗ[ℝ] ℂ)
    (σ : Equiv.Perm (ι ⊕ κ)) (v : ι ⊕ κ → T) :
    (LinearMap.mul' ℝ ℂ) (AlternatingMap.domCoprod.summand a b (Quotient.mk'' σ) v) =
      (((Equiv.Perm.sign σ : ℤ) : ℂ)) *
        (a (fun i => v (σ (Sum.inl i))) * b (fun i => v (σ (Sum.inr i)))) := by
  rw [AlternatingMap.domCoprod.summand_mk'']
  change (LinearMap.mul' ℝ ℂ) ((Equiv.Perm.sign σ : ℤ) •
    (a (fun index => v (σ (Sum.inl index))) ⊗ₜ[ℝ]
      b (fun index => v (σ (Sum.inr index))))) = _
  rw [map_zsmul, LinearMap.mul'_apply, zsmul_eq_mul]

/-- Differentiating the actual finite shuffle sum, at each vector tuple. -/
theorem hasDerivAt_wedge_eval {a : ℝ → T [⋀^ι]→ₗ[ℝ] ℂ}
    {b : ℝ → T [⋀^κ]→ₗ[ℝ] ℂ} {da : T [⋀^ι]→ₗ[ℝ] ℂ}
    {db : T [⋀^κ]→ₗ[ℝ] ℂ} {t : ℝ}
    (ha : ∀ v, HasDerivAt (fun s => a s v) (da v) t)
    (hb : ∀ v, HasDerivAt (fun s => b s v) (db v) t) (v : ι ⊕ κ → T) :
    HasDerivAt (fun s => wedge (a s) (b s) v)
      ((wedge da (b t) + wedge (a t) db) v) t := by
  have hterm (σ : Equiv.Perm.ModSumCongr ι κ) :
      HasDerivAt
        (fun s => (LinearMap.mul' ℝ ℂ) (AlternatingMap.domCoprod.summand (a s) (b s) σ v))
        ((LinearMap.mul' ℝ ℂ) (AlternatingMap.domCoprod.summand da (b t) σ v) +
         (LinearMap.mul' ℝ ℂ) (AlternatingMap.domCoprod.summand (a t) db σ v)) t := by
    induction σ using Quotient.inductionOn' with
    | h σ =>
      simp only [wedge_summand_eval]
      convert ((ha (fun i => v (σ (Sum.inl i)))).mul
        (hb (fun i => v (σ (Sum.inr i))))).const_mul (((Equiv.Perm.sign σ : ℤ) : ℂ)) using 1
      ring
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ => hterm σ)
  simpa only [wedge, LinearMap.compAlternatingMap_apply, AlternatingMap.domCoprod_apply,
    sum_apply, map_sum, AlternatingMap.add_apply, Finset.sum_add_distrib] using hs

/-- The exact variation of an iterated shuffle power, without suppressing any
terms by a formal commutativity or integration-by-parts assumption. -/
noncomputable def wedgePowerVariation (a da : T [⋀^Fin 2]→ₗ[ℝ] ℂ) :
    (k : ℕ) → T [⋀^WedgePowerSlots k]→ₗ[ℝ] ℂ
  | 0 => 0
  | k + 1 => wedge da (wedgePower a k) + wedge a (wedgePowerVariation a da k)

theorem hasDerivAt_wedgePower_eval {a : ℝ → T [⋀^Fin 2]→ₗ[ℝ] ℂ}
    {da : T [⋀^Fin 2]→ₗ[ℝ] ℂ} {t : ℝ}
    (ha : ∀ v, HasDerivAt (fun s => a s v) (da v) t) (k : ℕ)
    (v : WedgePowerSlots k → T) :
    HasDerivAt (fun s => wedgePower (a s) k v) (wedgePowerVariation (a t) da k v) t := by
  induction k with
  | zero => exact hasDerivAt_const t 1
  | succ k ih =>
    exact hasDerivAt_wedge_eval ha ih v

end Mahler

end OAI
