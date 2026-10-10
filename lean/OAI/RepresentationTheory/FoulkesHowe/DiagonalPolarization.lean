import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346

/-- A symmetric continuous multilinear form is determined by its diagonal. -/
theorem continuous_symmetric_multilinear_eq_zero_of_diagonal
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] {n : ℕ}
    (T : ContinuousMultilinearMap ℂ (fun _ : Fin n => W) ℂ)
    (hsym : ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → W),
      T (fun i => x (σ i)) = T x)
    (hdiag : ∀ x : W, T (fun _ => x) = 0) : T = 0 := by
  ext x
  have h := T.iteratedFDeriv_comp_diagonal (0 : W) x
  have hz : (fun x : W => T (fun _ => x)) = fun _ => 0 := funext hdiag
  rw [hz] at h
  simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, zero_apply] at h
  simp only [hsym, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (by exact_mod_cast Nat.factorial_ne_zero n)

/-- Algebraic polarization, without a topology on the source vector space. -/
theorem symmetric_multilinear_eq_zero_of_diagonal
    {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (T : MultilinearMap ℂ (fun _ : Fin n => W) ℂ)
    (hsym : ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → W),
      T (fun i => x (σ i)) = T x)
    (hdiag : ∀ x : W, T (fun _ => x) = 0) : T = 0 := by
  classical
  ext x
  let L : (Fin n → ℂ) →ₗ[ℂ] W :=
    ∑ i : Fin n, (LinearMap.proj i).smulRight (x i)
  let S := T.compLinearMap (fun _ => L)
  have hL (z : Fin n → ℂ) : L z = ∑ i, z i • x i := by simp [L]
  have hS (z : Fin n → Fin n → ℂ) :
      S z = ∑ r : Fin n → Fin n, (∏ i, z i (r i)) • T (fun i => x (r i)) := by
    simp only [S, MultilinearMap.compLinearMap_apply, hL]
    rw [T.map_sum]
    simp only [T.map_smul_univ]
  have hc : Continuous S := by
    have heq : (fun z => S z) = fun z =>
        ∑ r : Fin n → Fin n, (∏ i, z i (r i)) • T (fun i => x (r i)) := funext hS
    rw [show (S : (Fin n → Fin n → ℂ) → ℂ) = _ from heq]
    fun_prop
  let C : ContinuousMultilinearMap ℂ (fun _ : Fin n => Fin n → ℂ) ℂ := ⟨S, hc⟩
  have hC : C = 0 := continuous_symmetric_multilinear_eq_zero_of_diagonal C
    (by intro σ z; exact hsym σ (fun i => L (z i)))
    (by intro z; exact hdiag (L z))
  have hh := congrArg (fun f : ContinuousMultilinearMap ℂ
      (fun _ : Fin n => Fin n → ℂ) ℂ => f (fun i => Pi.single i 1)) hC
  change T (fun i => L (Pi.single i 1)) = 0 at hh
  simpa [hL] using hh

end Problem346

end

end OAI
