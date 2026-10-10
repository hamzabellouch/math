import OAI.NumberTheory.Ostmann.Construction.PhaseGiantMean

namespace OAI

/-! # Concrete finite additive spectral projections for Section 5 -/

namespace Ostmann
open scoped Classical BigOperators

theorem densityFourier_sub {p : ℕ} [NeZero p] (f g : ZMod p → ℂ) (b : ZMod p) :
    densityFourier (fun x => f x - g x) b = densityFourier f b - densityFourier g b := by
  simp only [densityFourier, additiveFourier_sub, mul_sub]

theorem densityFourier_const_mul {p : ℕ} [NeZero p]
    (c : ℂ) (f : ZMod p → ℂ) (b : ZMod p) :
    densityFourier (fun x => c * f x) b = c * densityFourier f b := by
  simp only [densityFourier, additiveFourier_const_mul]
  ring

theorem densityFourierInverse_fourier {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (x : ZMod p) :
    densityFourierInverse (densityFourier f) x = f x := by
  change densityFourier (densityFourier f) (-x) = f x
  rw [densityFourier_twice, neg_neg]

noncomputable def finiteSpectralProjection {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (f : ZMod p → ℂ) : ZMod p → ℂ :=
  densityFourierInverse (fun b => if b ∈ E then densityFourier f b else 0)

theorem finiteSpectralProjection_fourier {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (f : ZMod p → ℂ) (b : ZMod p) :
    densityFourier (finiteSpectralProjection E f) b =
      if b ∈ E then densityFourier f b else 0 := densityFourier_inverse _ _

/-- The counting energy of the projection equals the selected Fourier energy. -/
theorem finiteSpectralProjection_energy {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (f : ZMod p → ℂ) :
    (∑ x, ‖finiteSpectralProjection E f x‖ ^ 2) =
      ∑ b ∈ E, ‖densityFourier f b‖ ^ 2 := by
  rw [finiteSpectralProjection, densityFourierInverse_energy]
  simp only [apply_ite, norm_zero, ite_pow, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_ite_mem, Finset.univ_inter]

theorem finiteSpectralProjection_energy_le {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (f : ZMod p → ℂ) :
    (∑ x, ‖finiteSpectralProjection E f x‖ ^ 2) ≤ ∑ x, ‖f x‖ ^ 2 := by
  rw [finiteSpectralProjection_energy, ← densityFourier_energy f]
  exact Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)

/-- The exact discarded energy, rather than a dimension-dependent bound. -/
theorem finiteSpectralProjection_residual_energy {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (f : ZMod p → ℂ) :
    (∑ x, ‖f x - finiteSpectralProjection E f x‖ ^ 2) =
      ∑ b ∈ Finset.univ \ E, ‖densityFourier f b‖ ^ 2 := by
  rw [← densityFourier_energy (fun x => f x - finiteSpectralProjection E f x)]
  simp_rw [densityFourier_sub, finiteSpectralProjection_fourier]
  have hE : Finset.univ \ E = Finset.univ.filter (fun b => b ∉ E) := by
    ext b
    simp
  rw [hE, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : b ∈ E <;> simp [hb]

/-- Every spectral projection minus half the identity has operator norm
one half, expressed in the counting energy needed for the block estimate. -/
theorem finiteSpectralProjection_half_energy {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (f : ZMod p → ℂ) :
    (∑ x, ‖finiteSpectralProjection E f x - (1 / 2 : ℂ) * f x‖ ^ 2) =
      (1 / 4 : ℝ) * ∑ x, ‖f x‖ ^ 2 := by
  rw [← densityFourier_energy (fun x => finiteSpectralProjection E f x - (1 / 2 : ℂ) * f x),
    ← densityFourier_energy f, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [densityFourier_sub, finiteSpectralProjection_fourier, densityFourier_const_mul]
  by_cases hb : b ∈ E
  · rw [ite_eq_left hb]
    have he : densityFourier f b - (1 / 2 : ℂ) * densityFourier f b =
        (1 / 2 : ℂ) * densityFourier f b := by ring
    rw [he, norm_mul, mul_pow]
    norm_num
  · rw [ite_eq_right hb, zero_sub, norm_neg, norm_mul, mul_pow]
    norm_num

/-- Zero outside the selected frequencies makes the projection idempotent. -/
theorem finiteSpectralProjection_idempotent {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (f : ZMod p → ℂ) :
    finiteSpectralProjection E (finiteSpectralProjection E f) = finiteSpectralProjection E f := by
  unfold finiteSpectralProjection
  congr 1
  funext b
  rw [densityFourier_inverse]
  by_cases hb : b ∈ E <;> simp [hb]

theorem finiteSpectralProjection_constant {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (hE : 0 ∉ E) (c : ℂ) (x : ZMod p) :
    finiteSpectralProjection E (fun _ => c) x = 0 := by
  have he : (fun b : ZMod p => if b ∈ E then densityFourier (fun _ => c) b else 0) =
      fun _ => 0 := by
    funext b
    simp only [densityFourier, additiveFourier_const]
    by_cases hb : b = 0
    · subst b
      simp only [ite_eq_right hE]
    · simp only [ite_eq_right hb, mul_zero, ite_self]
  rw [finiteSpectralProjection, he]
  simp only [densityFourierInverse, densityFourier, additiveFourier_apply, zero_mul,
    Finset.sum_const_zero, mul_zero]

end Ostmann

end OAI
