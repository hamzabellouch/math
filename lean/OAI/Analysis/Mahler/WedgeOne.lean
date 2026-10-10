import OAI.Analysis.Mahler.WedgeAssociativity
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

namespace OAI

open scoped BigOperators

namespace Mahler
variable {T J : Type*} [AddCommGroup T] [Module ℝ T] [Fintype J]

def prependFinEquiv (n : ℕ) : Fin 1 ⊕ Fin n ≃ Fin (n+1) :=
  { toFun := Sum.elim (fun _ => 0) Fin.succ
    invFun := Fin.cases (Sum.inl 0) Sum.inr
    left_inv := by
      intro s
      cases s with
      | inl i => exact congrArg Sum.inl (Subsingleton.elim _ _)
      | inr i => rfl
    right_inv := by
      intro i
      refine Fin.cases rfl (fun j => rfl) i }

lemma covectorVolume_cons_apply {n : ℕ} (a : T →ₗ[ℝ] ℂ)
    (l : Fin n → T →ₗ[ℝ] ℂ) (v : Fin (n+1) → T) :
    covectorVolume (Fin.cons a l) v =
      ∑ i : Fin (n+1), (-1 : ℂ)^i.val * a (v i) * covectorVolume l (i.removeNth v) := by
  rw [covectorVolume_apply]
  rw [Matrix.det_succ_column_zero]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [covectorVolume_apply]
  congr 2

lemma covectorVolume_prepend {n : ℕ} (a : T →ₗ[ℝ] ℂ)
    (l : Fin n → T →ₗ[ℝ] ℂ) :
    (covectorVolume (Sum.elim (fun _ : Fin 1 => a) l)).domDomCongr (prependFinEquiv n) =
      covectorVolume (Fin.cons a l) := by
  rw [covectorVolume_domDomCongr]
  congr 1
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [prependFinEquiv]
  · simp [prependFinEquiv]

lemma alternating_sum_eval {Q ι : Type*} (s : Finset Q)
    (f : Q → T [⋀^ι]→ₗ[ℝ] ℂ) (v : ι → T) :
    (∑ q ∈ s, f q) v = ∑ q ∈ s, f q v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AlternatingMap.zero_apply]
  | @insert q s hq ih =>
    simp only [Finset.sum_insert hq, AlternatingMap.add_apply, ih]

/-- One-form wedge evaluation in standard Fin order, with the unnormalized
exterior-derivative signs. -/
theorem wedge_one_eval (basis : Module.Basis J ℝ T) {n : ℕ}
    (a : T →ₗ[ℝ] ℂ) (B : T [⋀^Fin n]→ₗ[ℝ] ℂ) (v : Fin (n+1) → T) :
    (wedge (covectorVolume (fun _ : Fin 1 => a)) B).domDomCongr (prependFinEquiv n) v =
      ∑ i : Fin (n+1), (-1 : ℂ)^i.val * a (v i) * B (i.removeNth v) := by
  rw [alternating_basis_expansion_normalized basis B]
  simp only [wedge_sum_right, wedge_smul_right, domDomCongr_sum,
    AlternatingMap.domDomCongr_smul, wedge_covectorVolume, covectorVolume_prepend]
  simp only [alternating_sum_eval, AlternatingMap.smul_apply,
    covectorVolume_cons_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro q hq
  ring

end Mahler

end OAI
