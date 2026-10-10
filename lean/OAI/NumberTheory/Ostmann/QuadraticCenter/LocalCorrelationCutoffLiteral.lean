import OAI.NumberTheory.Ostmann.QuadraticCenter.LocalCorrelationCutoffSum

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators ComplexConjugate

def quadraticCutoffWeight (R : ℝ) (d e v w w' : ℕ) (s : ℝ) : ℂ :=
  cutoffFourier (s * v * (w : ℝ)^2 / (R * d)) *
    conj (cutoffFourier (s * v * (w' : ℝ)^2 / (R * e)))

theorem quadraticCutoffWeight_eq (R : ℝ) (d e v w w' : ℕ) (s : ℝ) :
    quadraticCutoffWeight R d e v w w' s =
      correlationCutoffWeight ((v : ℝ) * w^2 / (R*d)) ((v : ℝ) * w'^2 / (R*e)) s := by
  unfold quadraticCutoffWeight correlationCutoffWeight
  have hd : s * v * (w : ℝ)^2 / (R*d) = ((v:ℝ)*w^2/(R*d))*s := by ring
  have he : s * v * (w' : ℝ)^2 / (R*e) = ((v:ℝ)*w'^2/(R*e))*s := by ring
  rw [hd, he]

theorem periodic_interval_quadratic_cutoff_bound {q : ℕ} [NeZero q]
    (F : ZMod q → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hcoeff : ∀ h, ‖normalizedCoefficient F h‖ ≤ A)
    (α : ℝ) (a : ℤ) (N : ℕ) {R S : ℝ} (hR : 0 < R)
    (d e v w w' : ℕ) (hd : 0 < d) (he : 0 < e)
    (hN : (N : ℝ) ≤ S) (ha : S ≤ (a : ℝ)) :
    ‖∑ n ∈ Finset.range N,
      (F ((a + (n : ℤ) : ℤ) : ZMod q) * weylPhase (((a : ℝ) + n) * α)) *
        quadraticCutoffWeight R d e v w w' ((a : ℝ) + n)‖ ≤
      2 * cutoffFourierBound ^ 2 * A * (2 * N + 2 * q * (harmonic q : ℝ)) := by
  simp_rw [quadraticCutoffWeight_eq]
  apply periodic_interval_cutoff_bound_of_support F hA hcoeff α a N
    (by positivity) (by positivity) hN ha

end Ostmann.QuadraticCenter

end

end OAI
