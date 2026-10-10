import OAI.NumberTheory.Ostmann.Tree.TruncatedModePairing

namespace OAI

/-! # Linear evaluation of the finite kernel against two fixed vectors -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def kernelPairingLinearMap {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℂ) (g : β → ℂ) : (α → β → ℂ) →ₗ[ℂ] ℂ where
  toFun M := ∑ x, conj (f x) * ∑ y, M x y * g y
  map_add' M N := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' c M := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring

theorem kernelPairing_polynomial {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℂ) (g : β → ℂ) (c : ℕ → ℕ → α → β → ℂ) (N : ℕ) (u v : ℂ) :
    kernelPairingLinearMap f g (finitePolynomial₂ c N u v) =
      finitePolynomial₂ (fun i j => kernelPairingLinearMap f g (c i j)) N u v := by
  simp only [finitePolynomial₂, finitePolynomial, map_sum, map_smul]

theorem kernelPairing_rectangular {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℂ) (g : β → ℂ) (c : ℕ → ℕ → α → β → ℂ) (N K : ℕ) :
    kernelPairingLinearMap f g (rectangularPolynomialSum c N K) =
      rectangularPolynomialSum (fun i j => kernelPairingLinearMap f g (c i j)) N K := by
  unfold rectangularPolynomialSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [map_zero]

end Ostmann

end OAI
