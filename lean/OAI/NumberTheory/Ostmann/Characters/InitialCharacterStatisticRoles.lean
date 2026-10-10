import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters
open Construction Preliminaries

def initialRoleSplit {κ : Type*} (n c : ℕ) :
    (Fin (n+c) → κ) ≃ ((Fin n → κ) × (Fin c → κ)) where
  toFun w := (fun i => w (Fin.castAdd c i), fun j => w (Fin.natAdd n j))
  invFun w := Fin.append w.1 w.2
  left_inv w := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [Fin.append_left, Fin.append_right]
  right_inv w := by
    apply Prod.ext <;> funext i <;> simp only [Fin.append_left, Fin.append_right]

theorem masked_productPrior_split {κ : Type*} [Fintype κ] {n c : ℕ}
    (μ : Fin (n+c) → FinitePrior κ) (f : Fin (n+c) → κ → ℂ)
    (B : (Fin n → κ) → ℂ) :
    (productPrior μ).cmean (fun w => B (fun i => w (Fin.castAdd c i))*∏ i, f i (w i)) =
      (productPrior (fun i => μ (Fin.castAdd c i))).cmean
        (fun w => B w*∏ i, f (Fin.castAdd c i) (w i)) *
      ∏ j : Fin c, (μ (Fin.natAdd n j)).cmean (f (Fin.natAdd n j)) := by
  rw [← productPrior_cmean (fun j : Fin c => μ (Fin.natAdd n j))]
  let μ₁ := productPrior (fun i : Fin n => μ (Fin.castAdd c i))
  let μ₂ := productPrior (fun j : Fin c => μ (Fin.natAdd n j))
  let f₁ := fun w : Fin n → κ => B w*∏ i, f (Fin.castAdd c i) (w i)
  let f₂ := fun w : Fin c → κ => ∏ j, f (Fin.natAdd n j) (w j)
  have he : (productPrior μ).cmean (fun w => B (fun i => w (Fin.castAdd c i))*∏ i, f i (w i)) =
      ∑ y : (Fin n → κ) × (Fin c → κ),
        (μ₁.mass y.1 : ℂ)*(μ₂.mass y.2 : ℂ)*f₁ y.1*f₂ y.2 := by
    unfold FinitePrior.cmean
    rw [← (initialRoleSplit n c).sum_comp (fun y =>
      (μ₁.mass y.1 : ℂ)*(μ₂.mass y.2 : ℂ)*f₁ y.1*f₂ y.2)]
    apply Finset.sum_congr rfl
    intro w hw
    simp only [productPrior, Fin.prod_univ_add, Complex.ofReal_mul,
      μ₁, μ₂, f₁, f₂, initialRoleSplit, Equiv.coe_fn_mk]
    ring
  rw [he]
  change (∑ y : (Fin n → κ) × (Fin c → κ),
    (μ₁.mass y.1 : ℂ)*(μ₂.mass y.2 : ℂ)*f₁ y.1*f₂ y.2) = μ₁.cmean f₁*μ₂.cmean f₂
  simp only [Fintype.sum_prod_type, FinitePrior.cmean]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w hw
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

theorem initialCharacterMean_split {Q n c : ℕ}
    (E : Fin (n+c) → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i))
    (χ : Fin (n+c) → (q : ℕ) → MulChar (ZMod q) ℂ)
    (a : Fin (n+c) → (q : ℕ) → ZMod q) (z : Fin (n+c) → ℕ → ℂ)
    (B : (Fin n → PrimeUpTo Q) → ℝ) (x : ℤ) :
    initialCharacterMean E hE χ a z (fun w => B (fun i => w (Fin.castAdd c i))) x =
      initialCharacterMean (fun i => E (Fin.castAdd c i)) (fun i => hE (Fin.castAdd c i))
        (fun i => χ (Fin.castAdd c i)) (fun i => a (Fin.castAdd c i))
        (fun i => z (Fin.castAdd c i)) B x *
      ∏ j : Fin c, (primeShellPrior (E (Fin.natAdd n j)) (hE (Fin.natAdd n j))).cmean
        (fun p => phasedCharacter (χ (Fin.natAdd n j) p.val) (a (Fin.natAdd n j) p.val)
          (z (Fin.natAdd n j) p.val) (x : ZMod p.val)) := by
  exact masked_productPrior_split (fun i => primeShellPrior (E i) (hE i))
    (fun i p => phasedCharacter (χ i p.val) (a i p.val) (z i p.val) (x : ZMod p.val))
    (fun w => (B w : ℂ))

theorem initial_word_cells_norm_lower {c : ℕ} (G : ℂ) (R : Fin c → ℂ)
    {γ δ : ℝ} (_hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hG : γ ≤ ‖G‖)
    (hR : ∀ j, δ ≤ (R j).re) : γ*δ^c ≤ ‖G*∏ j, R j‖ := by
  rw [norm_mul, norm_prod]
  apply mul_le_mul hG _ (pow_nonneg hδ _) (norm_nonneg _)
  calc
    _ = ∏ _j : Fin c, δ := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hδ)
      (fun j _ => (hR j).trans (Complex.re_le_norm _))

end Ostmann.Characters

end

end OAI
