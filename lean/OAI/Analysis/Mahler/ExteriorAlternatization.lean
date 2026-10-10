import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.Tactic.Ext

namespace OAI

open Equiv Fin
namespace Mahler
noncomputable section

/-- Insert the distinguished derivative slot at p, preserving the order of
all remaining slots before applying their permutation. -/
def orderedInsertPermutation {n : ℕ} (p : Fin (n+1)) (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n+1)) :=
  (Equiv.Perm.decomposeFin.symm (0, σ)).trans p.cycleRange.symm

@[simp] lemma orderedInsertPermutation_zero {n : ℕ} (p : Fin (n+1))
    (σ : Equiv.Perm (Fin n)) : orderedInsertPermutation p σ 0 = p := by
  simp [orderedInsertPermutation]

@[simp] lemma orderedInsertPermutation_succ {n : ℕ} (p : Fin (n+1))
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    orderedInsertPermutation p σ i.succ = p.succAbove (σ i) := by
  simp [orderedInsertPermutation, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fin.cycleRange_symm_succ]

lemma orderedInsertPermutation_sign {n : ℕ} (p : Fin (n+1))
    (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign (orderedInsertPermutation p σ) = (-1)^p.val * Equiv.Perm.sign σ := by
  simp [orderedInsertPermutation, Equiv.Perm.sign_trans, Equiv.Perm.decomposeFin.symm_sign,
    Fin.sign_cycleRange]

/-- An order-preserving decomposition of every permutation into its first
image and a permutation of the remaining slots. -/
def orderedPermutationEquiv (n : ℕ) :
    (Fin (n+1) × Equiv.Perm (Fin n)) ≃ Equiv.Perm (Fin (n+1)) where
  toFun q := orderedInsertPermutation q.1 q.2
  invFun σ := (σ 0, (Equiv.Perm.decomposeFin (σ.trans (σ 0).cycleRange)).2)
  left_inv := by
    rintro ⟨p,σ⟩
    simp only [orderedInsertPermutation_zero]
    have he : (orderedInsertPermutation p σ).trans p.cycleRange =
        Equiv.Perm.decomposeFin.symm (0,σ) := by
      ext i
      simp [orderedInsertPermutation]
    rw [he]
    simp
  right_inv := by
    intro σ
    have hz : (Equiv.Perm.decomposeFin (σ.trans (σ 0).cycleRange)).1 = 0 := by
      simp [Equiv.Perm.decomposeFin]
    have he : Equiv.Perm.decomposeFin (σ.trans (σ 0).cycleRange) =
        (0, (Equiv.Perm.decomposeFin (σ.trans (σ 0).cycleRange)).2) :=
      Prod.ext hz rfl
    have hi := congrArg Equiv.Perm.decomposeFin.symm he
    simp only [Equiv.symm_apply_apply] at hi
    dsimp only
    unfold orderedInsertPermutation
    rw [← hi]
    ext i
    simp

@[simp] lemma orderedPermutationEquiv_apply (n : ℕ)
    (p : Fin (n+1) × Equiv.Perm (Fin n)) :
    orderedPermutationEquiv n p = orderedInsertPermutation p.1 p.2 := rfl

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def rawUncurry {n : ℕ} (D : E →ₗ[ℝ] E [⋀^Fin n]→ₗ[ℝ] ℂ) :
    MultilinearMap ℝ (fun _ : Fin (n+1) => E) ℂ :=
  LinearMap.uncurryLeft
    { toFun := fun v => (D v).toMultilinearMap
      map_add' := fun _ _ => by ext w; simp
      map_smul' := fun _ _ => by ext w; simp }

@[simp] lemma rawUncurry_apply {n : ℕ} (D : E →ₗ[ℝ] E [⋀^Fin n]→ₗ[ℝ] ℂ)
    (v : Fin (n+1) → E) : rawUncurry D v = D (v 0) (fun i => v i.succ) := rfl

/-- Full alternatization of a distinguished derivative slot contains each
term of the usual exterior derivative exactly n! times. -/
theorem alternatization_rawUncurry {n : ℕ} (D : E →ₗ[ℝ] E [⋀^Fin n]→ₗ[ℝ] ℂ) :
    (rawUncurry D).alternatization = n.factorial • AlternatingMap.alternatizeUncurryFin D := by
  ext v
  rw [MultilinearMap.alternatization_apply]
  simp only [MultilinearMap.domDomCongr_apply, rawUncurry_apply]
  rw [← Equiv.sum_comp (orderedPermutationEquiv n), Fintype.sum_prod_type]
  simp only [orderedPermutationEquiv_apply, orderedInsertPermutation_zero,
    orderedInsertPermutation_succ, orderedInsertPermutation_sign]
  have hp (p : Fin (n+1)) (σ : Equiv.Perm (Fin n)) :
      ((-1 : ℤˣ)^p.val * Equiv.Perm.sign σ) •
        D (v p) (fun i => v (p.succAbove (σ i))) =
      (-1 : ℤ)^p.val • D (v p) (p.removeNth v) := by
    have he := (D (v p)).map_perm (p.removeNth v) σ
    change D (v p) (fun i => v (p.succAbove (σ i))) =
      Equiv.Perm.sign σ • D (v p) (p.removeNth v) at he
    rw [he, smul_smul, mul_assoc, Int.units_mul_self, mul_one]
    simp [Units.smul_def]
  simp_rw [hp]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    AlternatingMap.smul_apply, AlternatingMap.alternatizeUncurryFin_apply, Finset.smul_sum]

/-- General expansion: alternating all slots of an uncurried multilinear
map is the signed sum of the alternatizations in its trailing slots. -/
theorem alternatization_uncurryLeft_apply {n : ℕ}
    (D : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin n => E) ℂ) (v : Fin (n+1) → E) :
    D.uncurryLeft.alternatization v =
      ∑ p : Fin (n+1), (-1 : ℤ)^p.val • (D (v p)).alternatization (p.removeNth v) := by
  rw [MultilinearMap.alternatization_apply]
  simp only [MultilinearMap.domDomCongr_apply, LinearMap.uncurryLeft_apply]
  rw [← Equiv.sum_comp (orderedPermutationEquiv n), Fintype.sum_prod_type]
  simp only [orderedPermutationEquiv_apply, orderedInsertPermutation_zero,
    orderedInsertPermutation_sign, MultilinearMap.alternatization_apply, Finset.smul_sum,
    MultilinearMap.domDomCongr_apply]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro σ _
  change ((-1 : ℤˣ)^p.val * Equiv.Perm.sign σ) •
    D (v p) (fun i => v (orderedInsertPermutation p σ i.succ)) =
      (-1 : ℤ)^p.val • Equiv.Perm.sign σ • D (v p) (fun i => v (p.succAbove (σ i)))
  simp [Units.smul_def, mul_assoc]

end
end Mahler

end OAI
