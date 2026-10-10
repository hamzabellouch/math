import OAI.NumberTheory.CubicMoment.Estimates.IdealDivisorPower
import OAI.NumberTheory.CubicMoment.Estimates.PolynomialMeanValue

namespace OAI

/-! Rational norm fibers of arbitrary primary elements. An element of norm
`n` divides the rational integer `n` in the Eisenstein ring. Thus the proved
ideal divisor bound supplies the small multiplicity loss required by the
ordinary Montgomery--Vaughan input, without any prime-factor restriction. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_dvd_of_normNat_eq {b : Eisenstein} {n : ℕ} (hn : normNat b = n) :
    b ∣ (n : Eisenstein) := by
  rw [←hn,normNat_cast_eq_mul_conjugate]
  exact dvd_mul_right _ _

private lemma norm_natCast_eisenstein (n : ℕ) : norm (n : Eisenstein) = (n:ℝ)^2 := by
  change Complex.normSq (n:ℂ) = _
  simpa only [Complex.ofReal_natCast,pow_two] using Complex.normSq_ofReal (n:ℝ)

/-- Uniform small-power bound for positive rational norm fibers. -/
theorem primary_norm_fiber_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Finset Eisenstein),
      (∀ b ∈ T, primary b) → ∀ n : ℕ, 0 < n →
      ((T.filter (fun b => normNat b = n)).card:ℝ) ≤ C*(n:ℝ)^ε := by
  obtain ⟨C,hC,hdiv⟩ := primary_divisor_card_small_power (half_pos hε)
  refine ⟨C,hC,?_⟩
  intro T hT n hn
  have hn0 : (n:Eisenstein) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hsub : T.filter (fun b => normNat b = n) ⊆ T.filter (fun b => b ∣ (n:Eisenstein)) := by
    intro b hb
    obtain ⟨hbT,hbn⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_filter.mpr ⟨hbT,primary_dvd_of_normNat_eq hbn⟩
  have hpower : norm (n:Eisenstein)^(ε/2) = (n:ℝ)^ε := by
    rw [norm_natCast_eisenstein,←Real.rpow_natCast_mul (Nat.cast_nonneg n)]
    congr 1
    ring
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    ((hdiv T hT (n:Eisenstein) hn0).trans_eq (by rw [hpower]))

lemma primary_norm_fiber_length_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Finset Eisenstein),
      (∀ b ∈ T, primary b) → ∀ Z n : ℕ, n ∈ Finset.Icc 1 Z →
      ((T.filter (fun b => normNat b = n)).card:ℝ) ≤ C*(Z:ℝ)^ε := by
  obtain ⟨C,hC,hfiber⟩ := primary_norm_fiber_small_power hε
  refine ⟨C,hC,?_⟩
  intro T hT Z n hn
  obtain ⟨hn1,hnZ⟩ := Finset.mem_Icc.mp hn
  exact (hfiber T hT n (by omega)).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnZ) hε.le) hC.le)

/-- The actual primary angular polynomial satisfies the ordinary height
mean with only an arbitrarily small norm-length loss. -/
theorem primary_angular_meanSquare {ε C : ℝ} (hε : 0 < ε)
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 < D ∧ ∀ (T : Finset Eisenstein), (∀ b ∈ T, primary b) →
      ∀ (v : Eisenstein → ℂ) (Z : ℕ),
      (∀ b ∈ T, normNat b ∈ Finset.Icc 1 Z) → ∀ (ℓ : ℤ) (u a b : ℝ), a ≤ b →
      (∫ t in a..b, ‖∑ c ∈ T, v c*theta ℓ c*mellinPhase (t+u) (norm c)‖^2) ≤
        C*(b-a+Z)*(D*(Z:ℝ)^ε)*(∑ c ∈ T, ‖v c‖^2) := by
  obtain ⟨D,hD,hfiber⟩ := primary_norm_fiber_length_bound hε
  refine ⟨D,hD,?_⟩
  intro T hT v Z hZ ℓ u a b hab
  exact fixedAngular_translated_meanSquare hMV hC T v Z (D*(Z:ℝ)^ε) hZ
    (fun c hc => primary_ne_zero (hT c hc)) (hfiber T hT Z) ℓ u hab

end CubicFirstMoment

end

end OAI
