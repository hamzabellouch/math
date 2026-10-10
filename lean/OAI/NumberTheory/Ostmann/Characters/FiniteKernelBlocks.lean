import OAI.NumberTheory.Ostmann.Supply.CenteredProjectionPairing
import OAI.NumberTheory.Ostmann.Supply.BalancedKernelBlocks
import OAI.NumberTheory.Ostmann.Construction.ResidueBlockEnergy

namespace OAI

/-! # Concrete side and lower blocks of the finite kernel matrix -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def residueKernelSide {p : ℕ} [NeZero p]
    (S T : Finset (ZMod p)) (k : ZMod p → ℂ) : ZMod p → ℂ :=
  centeredSupportProjection S (rawAdditiveKernelAction k (uniformResidueVector T))

noncomputable def residueKernelLower {p : ℕ} [NeZero p]
    (S T : Finset (ZMod p)) (k : ZMod p → ℂ) (f : ZMod p → ℂ) : ZMod p → ℂ :=
  centeredSupportProjection S (rawAdditiveKernelAction k (centeredSupportProjection T f))

theorem residueKernel_row_pairing {p : ℕ} [NeZero p]
    (S T : Finset (ZMod p)) (k : ZMod p → ℂ)
    (hk : ∀ a, conj ((p : ℂ) * additiveFourier k a) = (p : ℂ) * additiveFourier k a)
    (f : ZMod p → ℂ) :
    (∑ x, conj (uniformResidueVector S x) *
      rawAdditiveKernelAction k (centeredSupportProjection T f) x) =
      ∑ x, conj (residueKernelSide T S k x) * f x := by
  rw [rawAdditiveKernelAction_selfAdjoint k hk,
    centeredSupportProjection_pairing T]
  rfl

theorem residueKernelSide_sparse_norm {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (t : ℝ) :
    residueVectorNorm (residueKernelSide S T (sparseAdditiveKernel E t)) =
      |t| * residueVectorNorm (centeredSupportProjection S
        (finiteSpectralProjection E (uniformResidueVector T))) := by
  have he : rawAdditiveKernelAction (sparseAdditiveKernel E t) (uniformResidueVector T) =
      fun x => (t : ℂ) * finiteSpectralProjection E (uniformResidueVector T) x := by
    funext x
    exact sparseAdditiveKernel_action E t _ x
  rw [residueKernelSide, he, centeredSupportProjection_const_mul, residueVectorNorm_smul]
  simp only [Complex.norm_real, Real.norm_eq_abs]

theorem residueKernelSide_square_norm_le {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (t ε : ℝ) (hε : 0 ≤ ε) (hE : (E.card : ℝ) ≤ ε * p) :
    residueVectorNorm (residueKernelSide S T
      (fun x => sparseAdditiveKernel E t x * sparseAdditiveKernel E t x)) ≤
      (t ^ 2 * ε) * residueVectorNorm (uniformResidueVector T) := by
  apply (residueVectorNorm_centered_le _ _).trans
  exact residueVectorNorm_raw_le _ _ _ (mul_nonneg (sq_nonneg _) hε)
    (sparseAdditiveKernel_square_multiplier_le E t ε hE)

theorem sparseAdditiveKernel_multiplier_real {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (t : ℝ) (a : ZMod p) :
    conj ((p : ℂ) * additiveFourier (sparseAdditiveKernel E t) a) =
      (p : ℂ) * additiveFourier (sparseAdditiveKernel E t) a := by
  rw [sparseAdditiveKernel_fourier]
  simp only [map_mul, map_natCast, map_inv₀, Complex.conj_ofReal]
  by_cases ha : a ∈ E <;> simp [ha]

theorem sparseAdditiveKernel_square_multiplier_real {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (t : ℝ) (a : ZMod p) :
    conj ((p : ℂ) * additiveFourier
      (fun x => sparseAdditiveKernel E t x * sparseAdditiveKernel E t x) a) =
      (p : ℂ) * additiveFourier
        (fun x => sparseAdditiveKernel E t x * sparseAdditiveKernel E t x) a := by
  rw [sparseAdditiveKernel_square_fourier]
  simp only [map_mul, map_natCast, map_pow, map_inv₀, Complex.conj_ofReal]

end Ostmann

end OAI
