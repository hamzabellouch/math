import OAI.NumberTheory.Ostmann.Characters.MellinDiagonal
import OAI.NumberTheory.Ostmann.Characters.MixedFourier

namespace OAI

/-!
# The exact Parseval reduction for quartet averages

Two independent unit parameters are separated by Mellin Parseval.
The remaining difference convolution is diagonalized by additive Parseval.
All normalizations are the probability normalizations of Section 6.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance quartetParsevalFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable def additiveDifferenceConvolution {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) (y : ZMod p) : ℂ :=
  (p : ℂ)⁻¹ * ∑ d : ZMod p, f d * g (d - y)

theorem additiveFourier_reflection {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (fun x => f (-x)) a = additiveFourier f (-a) := by
  rw [additiveFourier_apply, additiveFourier_apply]
  congr 1
  calc
    _ = ∑ x : ZMod p, f (-(-x)) * ZMod.stdAddChar (-((-x) * a)) :=
      ((Equiv.neg (ZMod p)).bijective.sum_comp
        (fun x => f (-x) * ZMod.stdAddChar (-(x * a)))).symm
    _ = _ := by simp

theorem additiveFourier_differenceConvolution {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (additiveDifferenceConvolution f g) a =
      additiveFourier f a * additiveFourier g (-a) := by
  have heq : additiveDifferenceConvolution f g =
      additiveConvolution f (fun x => g (-x)) := by
    funext y
    simp only [additiveDifferenceConvolution, additiveConvolution, neg_sub]
  rw [heq, additiveFourier_convolution, additiveFourier_reflection]

theorem differenceConvolution_parseval {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) :
    (p : ℝ)⁻¹ * (∑ y : ZMod p, ‖additiveDifferenceConvolution f g y‖ ^ 2) =
      ∑ a : ZMod p, ‖additiveFourier f a‖ ^ 2 * ‖additiveFourier g (-a)‖ ^ 2 := by
  rw [← additiveFourier_parseval]
  simp only [additiveFourier_differenceConvolution, norm_mul, mul_pow]

/-- Parseval for coefficients given by an explicit Mellin synthesis. -/
theorem mellin_synthesis_parseval {p : ℕ} [Fact p.Prime]
    (c : MulChar (ZMod p) ℂ → ℂ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
      (∑ z : (ZMod p)ˣ, ‖∑ χ : MulChar (ZMod p) ℂ, c χ * χ z‖ ^ 2) =
        ∑ χ : MulChar (ZMod p) ℂ, ‖c χ‖ ^ 2 := by
  rw [← mellin_parseval]
  congr 1
  funext χ
  rw [mellinCoefficient_of_expansion c _ (fun _ => rfl)]

/-- Two independent held parameters separate both Mellin indices. -/
theorem mellin_product_synthesis_parseval {p : ℕ} [Fact p.Prime]
    (c : MulChar (ZMod p) ℂ → MulChar (ZMod p) ℂ → ℂ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
      (∑ z : (ZMod p)ˣ, (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
        ∑ t : (ZMod p)ˣ,
          ‖∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ,
            c χ ψ * χ z * ψ t‖ ^ 2) =
      ∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ, ‖c χ ψ‖ ^ 2 := by
  have hexp (z t : (ZMod p)ˣ) :
      (∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ, c χ ψ * χ z * ψ t) =
        ∑ ψ : MulChar (ZMod p) ℂ, (∑ χ : MulChar (ZMod p) ℂ, c χ ψ * χ z) * ψ t := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]
  simp_rw [hexp, mellin_synthesis_parseval]
  rw [Finset.sum_comm, Finset.mul_sum]
  simp_rw [mellin_synthesis_parseval]
  rw [Finset.sum_comm]

noncomputable def quartetSynthesis {p : ℕ} [Fact p.Prime]
    (f g : MulChar (ZMod p) ℂ → ZMod p → ℂ)
    (α β : MulChar (ZMod p) ℂ → MulChar (ZMod p) ℂ → MulChar (ZMod p) ℂ)
    (y : ZMod p) (z t : (ZMod p)ˣ) : ℂ :=
  ∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ,
    additiveDifferenceConvolution (fun d => f χ d * α χ ψ d)
      (fun e => g ψ e * β χ ψ e) y * χ z * ψ t

/-- Exact reduction to the Fourier sum used for all four quartet orientations. -/
theorem quartetSynthesis_parseval {p : ℕ} [Fact p.Prime]
    (f g : MulChar (ZMod p) ℂ → ZMod p → ℂ)
    (α β : MulChar (ZMod p) ℂ → MulChar (ZMod p) ℂ → MulChar (ZMod p) ℂ) :
    (p : ℝ)⁻¹ * (∑ y : ZMod p,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ z : (ZMod p)ˣ,
        (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
          ∑ t : (ZMod p)ˣ, ‖quartetSynthesis f g α β y z t‖ ^ 2)) =
      ∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
        ‖additiveFourier (fun d => f χ d * α χ ψ d) a‖ ^ 2 *
          ‖additiveFourier (fun e => g ψ e * β χ ψ e) (-a)‖ ^ 2 := by
  simp only [quartetSynthesis, mellin_product_synthesis_parseval]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ _
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ψ _
  exact differenceConvolution_parseval _ _

end Ostmann

end OAI
