import OAI.NumberTheory.CubicMoment.Estimates.DivisorCubeTerm
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCubeRoughness

namespace OAI

/-! Small square divisors act on the actual nonzero stopped rows. Zero
coefficients impose no artificial coprimality condition on the ambient support. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma divisorCubePoissonContribution_eq_of_active {d : Eisenstein} (hd : primary d)
    (hs : Squarefree d) (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (hS : ∀ a ∈ S, primary a)
    (hactive : ∀ a ∈ S, β a ≠ 0 → IsCoprime a d)
    (u : ℝ) (W : ℝ → ℂ) {A : ℝ} (hA : 0 ≤ A) :
    divisorCubePoissonContribution d S β u W A =
      (1/(norm d)^2:ℝ)*cubePoissonContribution S β u W A := by
  unfold divisorCubePoissonContribution cubePoissonContribution
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab]
    by_cases ha0 : β a = 0
    · simp only [ha0,zero_mul,mul_zero]
    by_cases hb0 : β b = 0
    · simp only [hb0,zero_mul,star_zero,mul_zero]
    rw [divisor_cube_series_effective (hS a ha) (hS b hb) hd hs
      (hactive a ha ha0) (hactive b hb hb0) W hA]
    simp only [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_one]
    ring
  · simp only [ite_eq_right hab,mul_zero]

lemma rough_coprime_small {a d : Eisenstein} {R : ℝ}
    (ha : primary a) (has : Squarefree a) (hd : d ≠ 0) (hsmall : norm d < R)
    (hrough : ∀ p ∈ primaryPrimeFactors a, R ≤ norm p) : IsCoprime a d := by
  by_contra hc
  obtain ⟨p,hp,hpd⟩ := not_coprime_prime_cover ha has hc
  exact (not_le_of_gt ((norm_le_of_dvd hd hpd).trans_lt hsmall)) (hrough p hp)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stopped_active_coprime_small {X ξ δ l b : ℝ}
    (hX : 1 ≤ X) (hξz : ξ ≤ 2/5) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (W : ι → ℝ → ℂ) (j k h : ℕ) (Z Q : ℝ) (early : Bool) (hj : j ≤ h)
    (e d : Eisenstein) (hd : d ≠ 0)
    (hsmall : norm d < min (X^ξ) (geometricBinLower (1+δ) X h))
    {a : Eisenstein} (ha : a ∈ stoppedIntervalSupport ι X l b e)
    (ha0 : stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
      (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
        j k h Z Q early) a ≠ 0) : IsCoprime a d := by
  have ha' := stoppedIntervalSupport_spec X l b e ha
  apply rough_coprime_small ha'.1 ha'.2.1 hd hsmall
  intro p hp
  exact stoppedRowCoefficient_early_roughness X (X^ξ) (X^(2/5:ℝ)) 0
    (1+δ) Z Q W (Real.rpow_pos_of_pos (zero_lt_one.trans_le hX) _)
    (Real.rpow_le_rpow_of_exponent_le hX hξz) (by linarith) (by linarith)
    j k h early hj ha0 (primaryPrimeFactor_spec ha'.1 hp).1
    (primaryPrimeFactor_spec ha'.1 hp).2

lemma stopped_divisor_cube_eq {X ξ δ l b : ℝ}
    (hX : 1 ≤ X) (hξz : ξ ≤ 2/5) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (W : ι → ℝ → ℂ) (j k h : ℕ) (Z Q : ℝ) (early : Bool) (hj : j ≤ h)
    (e d : Eisenstein) (hd : primary d) (hds : Squarefree d)
    (hsmall : norm d < min (X^ξ) (geometricBinLower (1+δ) X h))
    (u : ℝ) (Φ : ℝ → ℂ) {A : ℝ} (hA : 0 ≤ A) :
    let S := stoppedIntervalSupport ι X l b e
    let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
      (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
        j k h Z Q early)
    divisorCubePoissonContribution d S β u Φ A =
      (1/(norm d)^2:ℝ)*cubePoissonContribution S β u Φ A := by
  apply divisorCubePoissonContribution_eq_of_active hd hds
  · intro a ha
    exact (stoppedIntervalSupport_spec X l b e ha).1
  · intro a ha ha0
    exact stopped_active_coprime_small hX hξz hδ hδone W j k h Z Q early hj
      e d (primary_ne_zero hd) hsmall ha ha0
  · exact hA

end CubicFirstMoment

end

end OAI
