import OAI.NumberTheory.Ostmann.Supply.CenteredResidueProjection
import OAI.NumberTheory.Ostmann.Supply.SpectralProjectionPairing
import OAI.NumberTheory.Ostmann.Characters.SparseKernelEnergy

namespace OAI

/-! # Self-adjointness of the finite centered and kernel blocks -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem centeredSupportProjection_pairing {α : Type*} [Fintype α]
    (S : Finset α) (f g : α → ℂ) :
    (∑ x, conj (f x) * centeredSupportProjection S g x) =
      ∑ x, conj (centeredSupportProjection S f x) * g x := by
  have hm : (∑ x ∈ S, conj (f x)) * finiteSupportMean S g =
      conj (finiteSupportMean S f) * ∑ x ∈ S, g x := by
    simp only [finiteSupportMean, map_mul, map_inv₀, map_natCast, map_sum]
    ring
  simp only [centeredSupportProjection, mul_zero, apply_ite, map_zero,
    ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
  simp only [mul_sub, map_sub, sub_mul, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum]
  rw [hm]

theorem rawAdditiveKernelAction_selfAdjoint {p : ℕ} [NeZero p]
    (k : ZMod p → ℂ) (hk : ∀ a, conj ((p : ℂ) * additiveFourier k a) =
      (p : ℂ) * additiveFourier k a) (f g : ZMod p → ℂ) :
    (∑ x, conj (f x) * rawAdditiveKernelAction k g x) =
      ∑ x, conj (rawAdditiveKernelAction k f x) * g x := by
  rw [densityFourier_inner f (rawAdditiveKernelAction k g),
    densityFourier_inner (rawAdditiveKernelAction k f) g]
  simp_rw [rawAdditiveKernelAction_fourier]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_mul, hk]
  ring

end Ostmann

end OAI
