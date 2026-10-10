import OAI.NumberTheory.Ostmann.Characters.NormalizedResidueIndicator
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityFourierBounds

namespace OAI

/-! # The Fourier-phase giant and its real physical inverse -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def complexUnitPhase (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

@[simp] theorem complexUnitPhase_zero : complexUnitPhase 0 = 0 := by
  simp [complexUnitPhase]

theorem complexUnitPhase_norm_le (z : ℂ) : ‖complexUnitPhase z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz]
  · simp only [complexUnitPhase, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    rw [div_self (norm_ne_zero_iff.mpr hz)]

theorem complexUnitPhase_conj (z : ℂ) :
    complexUnitPhase (conj z) = conj (complexUnitPhase z) := by
  simp only [complexUnitPhase, Complex.norm_conj, map_div₀, Complex.conj_ofReal]

theorem complexUnitPhase_mul_conj (z : ℂ) :
    complexUnitPhase z * conj z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [hz]
  · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
    unfold complexUnitPhase
    rw [div_mul_eq_mul_div, Complex.mul_conj']
    field_simp

noncomputable def densityFourierInverse {p : ℕ} [NeZero p]
    (g : ZMod p → ℂ) (x : ZMod p) : ℂ := densityFourier g (-x)

noncomputable def phaseGiantPhysical {p : ℕ} [NeZero p]
    (g : ZMod p → ℂ) : ZMod p → ℂ :=
  densityFourierInverse (fun b => complexUnitPhase (g b))

theorem additiveFourier_reflect {p : ℕ} [NeZero p] (g : ZMod p → ℂ) (x : ZMod p) :
    additiveFourier (fun b => g (-b)) x = additiveFourier g (-x) := by
  simp only [additiveFourier_apply]
  congr 1
  apply Fintype.sum_equiv (Equiv.neg (ZMod p))
  intro b
  simp only [Equiv.neg_apply, neg_neg, neg_mul, mul_neg]

theorem densityFourierInverse_real {p : ℕ} [NeZero p]
    (g : ZMod p → ℂ) (hg : ∀ b, g (-b) = conj (g b)) (x : ZMod p) :
    (densityFourierInverse g x).im = 0 := by
  have hr : (fun b => conj (g b)) = fun b => g (-b) := funext fun b => (hg b).symm
  have he := additiveFourier_conj g x
  rw [hr, additiveFourier_reflect] at he
  have hc : conj (densityFourierInverse g x) = densityFourierInverse g x := by
    unfold densityFourierInverse densityFourier
    rw [map_mul, Complex.conj_ofReal, ← he]
  have hh := congrArg Complex.im hc
  simp only [Complex.conj_im] at hh
  linarith

theorem phaseGiantPhysical_real {p : ℕ} [NeZero p]
    (g : ZMod p → ℂ) (hg : ∀ b, g (-b) = conj (g b)) (x : ZMod p) :
    (phaseGiantPhysical g x).im = 0 := by
  apply densityFourierInverse_real
  intro b
  rw [hg, complexUnitPhase_conj]

theorem densityFourierInverse_energy {p : ℕ} [NeZero p] (g : ZMod p → ℂ) :
    (∑ x, ‖densityFourierInverse g x‖ ^ 2) = ∑ b, ‖g b‖ ^ 2 := by
  rw [← densityFourier_energy g]
  exact (Equiv.neg (ZMod p)).bijective.sum_comp (fun x => ‖densityFourier g x‖ ^ 2)

theorem phaseGiantPhysical_energy {p : ℕ} [NeZero p] (g : ZMod p → ℂ) :
    (∑ x, ‖phaseGiantPhysical g x‖ ^ 2) ≤ p := by
  rw [phaseGiantPhysical, densityFourierInverse_energy]
  calc
    _ ≤ ∑ _b : ZMod p, (1 : ℝ) := Finset.sum_le_sum fun b _ =>
      by simpa only [one_pow] using
        pow_le_pow_left₀ (norm_nonneg _) (complexUnitPhase_norm_le (g b)) 2
    _ = _ := by simp

theorem phaseGiantPhysical_bound {p : ℕ} [NeZero p] (g : ZMod p → ℂ) (x : ZMod p) :
    ‖phaseGiantPhysical g x‖ ≤ Real.sqrt p := by
  have hx : ‖phaseGiantPhysical g x‖ ^ 2 ≤ p :=
    (Finset.single_le_sum (fun b _ => sq_nonneg ‖phaseGiantPhysical g b‖)
      (Finset.mem_univ x)).trans (phaseGiantPhysical_energy g)
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg p), Real.sqrt_nonneg (p : ℝ),
    norm_nonneg (phaseGiantPhysical g x)]

/-- The unitary bilinear identity, with the inverse sign explicit. -/
theorem densityFourier_pairing {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) :
    (∑ x, f x * densityFourierInverse g x) =
      ∑ b, densityFourier f (-b) * g b := by
  simp only [densityFourierInverse, densityFourier, additiveFourier_apply,
    Finset.mul_sum, mul_neg, neg_neg, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro x _
  rw [mul_comm b x]
  ring

/-- Flattening preserves the exact positive Fourier pairing used in (7.2). -/
theorem phaseGiantPhysical_pairing {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ)
    (hf : ∀ b, densityFourier f (-b) = conj (densityFourier f b)) :
    (∑ x, f x * phaseGiantPhysical (densityFourier f) x) =
      ((∑ b, ‖densityFourier f b‖ : ℝ) : ℂ) := by
  rw [phaseGiantPhysical, densityFourier_pairing, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [hf, mul_comm, complexUnitPhase_mul_conj]

end Ostmann

end OAI
