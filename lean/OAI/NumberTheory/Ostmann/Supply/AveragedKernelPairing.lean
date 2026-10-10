import OAI.NumberTheory.Ostmann.Supply.NonnegativeSparseWeight

namespace OAI

/-! # Averaging the actual tensor coordinates over summand elements -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def averagedCoordinates {ι α : Type*}
    (A : Finset ι) (V : ι → α → ℂ) (x : α) : ℂ :=
  (A.card : ℂ)⁻¹ * ∑ a ∈ A, V a x

theorem kernelPairing_sum_left {ι α β : Type*} [Fintype α] [Fintype β]
    (A : Finset ι) (V : ι → α → ℂ) (g : β → ℂ) (M : α → β → ℂ) :
    kernelPairingLinearMap (fun x => ∑ a ∈ A, V a x) g M =
      ∑ a ∈ A, kernelPairingLinearMap (V a) g M := by
  change (∑ x, conj (∑ a ∈ A, V a x) * ∑ y, M x y * g y) = _
  simp only [map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem kernelPairing_sum_right {ι α β : Type*} [Fintype α] [Fintype β]
    (A : Finset ι) (f : α → ℂ) (V : ι → β → ℂ) (M : α → β → ℂ) :
    kernelPairingLinearMap f (fun y => ∑ a ∈ A, V a y) M =
      ∑ a ∈ A, kernelPairingLinearMap f (V a) M := by
  change (∑ x, conj (f x) * ∑ y, M x y * ∑ a ∈ A, V a y) = _
  simp only [Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := A)]
  change _ = ∑ a ∈ A, ∑ x, conj (f x) * ∑ y, M x y * V a y
  simp only [Finset.mul_sum]

theorem kernelPairing_const_mul {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℂ) (g : β → ℂ) (M : α → β → ℂ) (c d : ℂ) :
    kernelPairingLinearMap (fun x => c * f x) (fun y => d * g y) M =
      conj c * d * kernelPairingLinearMap f g M := by
  change (∑ x, conj (c * f x) * ∑ y, M x y * (d * g y)) =
    conj c * d * ∑ x, conj (f x) * ∑ y, M x y * g y
  simp only [map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem kernelPairing_averages {ι κ α β : Type*} [Fintype α] [Fintype β]
    (A : Finset ι) (B : Finset κ) (V : ι → α → ℂ) (W : κ → β → ℂ)
    (M : α → β → ℂ) :
    kernelPairingLinearMap (averagedCoordinates A V) (averagedCoordinates B W) M =
      (A.card : ℂ)⁻¹ * (B.card : ℂ)⁻¹ *
        ∑ a ∈ A, ∑ b ∈ B, kernelPairingLinearMap (V a) (W b) M := by
  change kernelPairingLinearMap (fun x => (A.card : ℂ)⁻¹ * ∑ a ∈ A, V a x)
    (fun y => (B.card : ℂ)⁻¹ * ∑ b ∈ B, W b y) M = _
  rw [kernelPairing_const_mul]
  simp only [map_inv₀, map_natCast, kernelPairing_sum_left, kernelPairing_sum_right]
  rw [Finset.sum_comm]

end Ostmann

end OAI
