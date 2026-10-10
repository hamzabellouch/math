import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem346

universe u v w z

/-- The normalized permanent of a pairing on two indexed families. -/
def permanentPairing {X : Type u} {Y : Type v} (n : ℕ)
    (B : X → Y → ℂ) (x : Fin n → X) (y : Fin n → Y) : ℂ :=
  (n.factorial : ℂ)⁻¹ * ∑ σ : Equiv.Perm (Fin n), ∏ i, B (x i) (y (σ i))

theorem permanentPairing_perm_right {X : Type u} {Y : Type v} (n : ℕ)
    (B : X → Y → ℂ) (x : Fin n → X) (y : Fin n → Y)
    (τ : Equiv.Perm (Fin n)) :
    permanentPairing n B x (fun i => y (τ i)) = permanentPairing n B x y := by
  classical
  unfold permanentPairing
  congr 1
  simpa only [Equiv.coe_mulLeft, Equiv.Perm.mul_apply] using
    (Equiv.sum_comp (Equiv.mulLeft τ)
      (fun σ : Equiv.Perm (Fin n) => ∏ i, B (x i) (y (σ i))))

theorem permanentPairing_perm_left {X : Type u} {Y : Type v} (n : ℕ)
    (B : X → Y → ℂ) (x : Fin n → X) (y : Fin n → Y)
    (τ : Equiv.Perm (Fin n)) :
    permanentPairing n B (fun i => x (τ i)) y = permanentPairing n B x y := by
  classical
  unfold permanentPairing
  congr 1
  calc
    (∑ σ : Equiv.Perm (Fin n), ∏ i, B (x (τ i)) (y (σ i))) =
        ∑ σ : Equiv.Perm (Fin n), ∏ i, B (x i) (y ((σ * τ⁻¹) i)) := by
      apply Finset.sum_congr rfl
      intro σ _
      simpa only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply] using
        (Equiv.prod_comp τ (fun i => B (x i) (y ((σ * τ⁻¹) i))))
    _ = ∑ σ : Equiv.Perm (Fin n), ∏ i, B (x i) (y (σ i)) := by
      simpa only [Equiv.coe_mulRight] using
        (Equiv.sum_comp (Equiv.mulRight τ⁻¹)
          (fun σ : Equiv.Perm (Fin n) => ∏ i, B (x i) (y (σ i))))

/-- Transposing the underlying pairing transposes the two families. -/
theorem permanentPairing_flip {X : Type u} {Y : Type v} (n : ℕ)
    (B : X → Y → ℂ) (x : Fin n → X) (y : Fin n → Y) :
    permanentPairing n (fun y x => B x y) y x = permanentPairing n B x y := by
  classical
  unfold permanentPairing
  congr 1
  calc
    (∑ σ : Equiv.Perm (Fin n), ∏ i, B (x (σ i)) (y i)) =
        ∑ σ : Equiv.Perm (Fin n), ∏ i, B (x i) (y (σ⁻¹ i)) := by
      apply Finset.sum_congr rfl
      intro σ _
      simpa only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] using
        (Equiv.prod_comp σ (fun i => B (x i) (y (σ⁻¹ i))))
    _ = ∑ σ : Equiv.Perm (Fin n), ∏ i, B (x i) (y (σ i)) := by
      exact Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n)))
        (fun σ : Equiv.Perm (Fin n) => ∏ i, B (x i) (y (σ i)))

@[simp] theorem permanentPairing_const_right {X : Type u} {Y : Type v} (n : ℕ)
    (B : X → Y → ℂ) (x : Fin n → X) (y : Y) :
    permanentPairing n B x (fun _ => y) = ∏ i, B (x i) y := by
  classical
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simp [permanentPairing, Fintype.card_perm, hn]

@[simp] theorem permanentPairing_const_left {X : Type u} {Y : Type v} (n : ℕ)
    (B : X → Y → ℂ) (x : X) (y : Fin n → Y) :
    permanentPairing n B (fun _ => x) y = ∏ i, B x (y i) := by
  rw [← permanentPairing_flip n B]
  exact permanentPairing_const_right n (fun y x => B x y) y x

/-- Moving a map across each scalar pairing moves it across the normalized permanent. -/
theorem permanentPairing_natural {X : Type u} {Y : Type v}
    {X' : Type w} {Y' : Type z} (n : ℕ)
    (B : X → Y → ℂ) (B' : X' → Y' → ℂ)
    (f : X → X') (g : Y' → Y)
    (h : ∀ x y, B' (f x) y = B x (g y))
    (x : Fin n → X) (y : Fin n → Y') :
    permanentPairing n B' (fun i => f (x i)) y =
      permanentPairing n B x (fun i => g (y i)) := by
  classical
  simp only [permanentPairing, h]

section Multilinear

variable {X : Type u} {Y : Type v}
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

/-- The permanent pairing as a multilinear map in its right family. -/
def permanentPairingRight (n : ℕ) (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (x : Fin n → X) : MultilinearMap ℂ (fun _ : Fin n => Y) ℂ :=
  (n.factorial : ℂ)⁻¹ •
    ∑ σ : Equiv.Perm (Fin n),
      ((MultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compLinearMap (fun i => B (x i))).domDomCongr σ

@[simp] theorem permanentPairingRight_apply (n : ℕ)
    (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (x : Fin n → X) (y : Fin n → Y) :
    permanentPairingRight n B x y = permanentPairing n (fun x y => B x y) x y := by
  classical
  simp [permanentPairingRight, permanentPairing]

/-- The permanent pairing as a multilinear map in its left family. -/
def permanentPairingLeft (n : ℕ) (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (y : Fin n → Y) : MultilinearMap ℂ (fun _ : Fin n => X) ℂ :=
  (n.factorial : ℂ)⁻¹ •
    ∑ σ : Equiv.Perm (Fin n),
      (MultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compLinearMap
        (fun i => B.flip (y (σ i)))

@[simp] theorem permanentPairingLeft_apply (n : ℕ)
    (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (x : Fin n → X) (y : Fin n → Y) :
    permanentPairingLeft n B y x = permanentPairing n (fun x y => B x y) x y := by
  classical
  simp [permanentPairingLeft, permanentPairing]

/-- Both families of the permanent pairing are multilinear. -/
def permanentPairingMultilinear (n : ℕ) (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) :
    MultilinearMap ℂ (fun _ : Fin n => X)
      (MultilinearMap ℂ (fun _ : Fin n => Y) ℂ) where
  toFun := permanentPairingRight n B
  map_update_add' x i a b := by
    ext y
    simpa only [add_apply, permanentPairingRight_apply,
      ← permanentPairingLeft_apply] using
      (permanentPairingLeft n B y).map_update_add x i a b
  map_update_smul' x i c a := by
    ext y
    simpa only [smul_apply, permanentPairingRight_apply,
      ← permanentPairingLeft_apply] using
      (permanentPairingLeft n B y).map_update_smul x i c a

@[simp] theorem permanentPairingMultilinear_apply (n : ℕ)
    (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (x : Fin n → X) (y : Fin n → Y) :
    permanentPairingMultilinear n B x y =
      permanentPairing n (fun x y => B x y) x y :=
  permanentPairingRight_apply n B x y

theorem permanentPairingMultilinear_perm_left (n : ℕ)
    (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (x : Fin n → X) (τ : Equiv.Perm (Fin n)) :
    permanentPairingMultilinear n B (fun i => x (τ i)) =
      permanentPairingMultilinear n B x := by
  ext y
  simpa only [permanentPairingMultilinear_apply] using
    permanentPairing_perm_left n (fun x y => B x y) x y τ

theorem permanentPairingMultilinear_perm_right (n : ℕ)
    (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (x : Fin n → X) (y : Fin n → Y)
    (τ : Equiv.Perm (Fin n)) :
    permanentPairingMultilinear n B x (fun i => y (τ i)) =
      permanentPairingMultilinear n B x y := by
  simpa only [permanentPairingMultilinear_apply] using
    permanentPairing_perm_right n (fun x y => B x y) x y τ

end Multilinear

end Problem346

end

end OAI
