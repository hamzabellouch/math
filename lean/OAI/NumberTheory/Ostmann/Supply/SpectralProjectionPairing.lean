import OAI.NumberTheory.Ostmann.Supply.FiniteSpectralProjection

namespace OAI

/-! # The exact pairing of the local spectral projection -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem densityFourier_conj_reflect {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (b : ZMod p) :
    densityFourier (fun x => conj (f x)) b = conj (densityFourier f (-b)) := by
  simp only [densityFourier, additiveFourier_conj, map_mul, Complex.conj_ofReal]

theorem densityFourier_inner {p : ℕ} [NeZero p] (f g : ZMod p → ℂ) :
    (∑ x, conj (f x) * g x) = ∑ b, conj (densityFourier f b) * densityFourier g b := by
  have he := densityFourier_pairing (fun x => conj (f x)) (densityFourier g)
  simpa only [densityFourierInverse_fourier, densityFourier_conj_reflect, neg_neg] using he

theorem finiteSpectralProjection_pairing {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (f g : ZMod p → ℂ) :
    (∑ x, conj (f x) * finiteSpectralProjection E g x) =
      ∑ b ∈ E, conj (densityFourier f b) * densityFourier g b := by
  rw [densityFourier_inner]
  simp only [finiteSpectralProjection_fourier, mul_ite, mul_zero,
    Finset.sum_ite_mem, Finset.univ_inter]

theorem finiteSpectralProjection_selfAdjoint {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (f g : ZMod p → ℂ) :
    (∑ x, conj (f x) * finiteSpectralProjection E g x) =
      ∑ x, conj (finiteSpectralProjection E f x) * g x := by
  rw [finiteSpectralProjection_pairing, densityFourier_inner]
  simp only [finiteSpectralProjection_fourier, apply_ite, map_zero, ite_mul,
    zero_mul, Finset.sum_ite_mem, Finset.univ_inter]

theorem finiteSpectralProjection_self_pairing {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (f : ZMod p → ℂ) :
    (∑ x, conj (f x) * finiteSpectralProjection E f x) =
      ((∑ x, ‖finiteSpectralProjection E f x‖ ^ 2 : ℝ) : ℂ) := by
  rw [finiteSpectralProjection_pairing, finiteSpectralProjection_energy, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [mul_comm, Complex.mul_conj', Complex.ofReal_pow]

end Ostmann

end OAI
