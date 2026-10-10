import OAI.NumberTheory.TwoPoint.Fourier.MinorArcLogLog

namespace OAI

/-! Verifying every dyadic hypothesis from the actual prime range. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma minor_arc_prime_range_dyadics (P : Finset ℕ) (H R₀ : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hlogH : 1 ≤ Real.log (H : ℝ))
    (hrange : ∀ p ∈ P, 2 * R₀ ≤ p ∧
      2 * (Real.log (H : ℝ)) ^ 5 ≤ (p : ℝ) ∧
      (p : ℝ) ≤ (H : ℝ) / (Real.log (H : ℝ)) ^ 5) :
    let J := P.image (Nat.log 2)
    J ⊆ Icc 1 (Nat.log 2 H) ∧
      (∀ p ∈ P, Nat.log 2 p ∈ J) ∧
      (∀ j ∈ J, R₀ ≤ 2 ^ j ∧ 2 ^ j ≤ H) ∧
      (∀ j ∈ J, (Real.log (H : ℝ)) ^ 5 ≤ (2 : ℝ) ^ j ∧
        (2 : ℝ) ^ j ≤ (H : ℝ) / (Real.log (H : ℝ)) ^ 5) := by
  dsimp only
  have hW : 1 ≤ (Real.log (H : ℝ)) ^ 5 := one_le_pow₀ hlogH
  have hpH (p : ℕ) (hp : p ∈ P) : p ≤ H := by
    have hh := (hrange p hp).2.2
    have hb : (p : ℝ) ≤ H := hh.trans (div_le_self (Nat.cast_nonneg H) hW)
    exact_mod_cast hb
  refine ⟨?_, fun p hp => mem_image.mpr ⟨p, hp, rfl⟩, ?_, ?_⟩
  · intro j hj
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hj
    exact mem_Icc.mpr ⟨minor_arc_dyadic_index_pos (hP p hp).two_le,
      Nat.log_mono_right (hpH p hp)⟩
  · intro j hj
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hj
    have hd := minor_arc_dyadic_prime_bounds (hP p hp).pos rfl
    constructor
    · nlinarith [(hrange p hp).1, hd.2]
    · exact hd.1.trans (hpH p hp)
  · intro j hj
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hj
    have hd := minor_arc_dyadic_prime_bounds (hP p hp).pos rfl
    have hlo : (2 : ℝ) * (2 : ℝ) ^ Nat.log 2 p ≥ p := by exact_mod_cast hd.2
    have hhi : (2 : ℝ) ^ Nat.log 2 p ≤ p := by exact_mod_cast hd.1
    exact ⟨by linarith [(hrange p hp).2.1], hhi.trans (hrange p hp).2.2⟩

theorem minor_arc_typical_prime_range_saving :
    ∃ C : ℝ, 0 < C ∧ ∃ R₀ : ℕ,
      ∀ {ι : Type*} (I : Finset ι) (P : ι → Finset ℕ),
      (∀ i ∈ I, ∀ p ∈ P i, p.Prime) → Set.PairwiseDisjoint (I : Set ι) P →
      ∀ i ∈ I, ∀ (X H : ℕ), 2 ≤ H → H ≤ X →
      1 ≤ Real.log (H : ℝ) → 1 ≤ Real.log (Real.log (H : ℝ)) →
      (∀ p ∈ P i, p ≠ 2 ∧ 2 * R₀ ≤ p ∧
        2 * (Real.log (H : ℝ)) ^ 5 ≤ (p : ℝ) ∧
        (p : ℝ) ≤ (H : ℝ) / (Real.log (H : ℝ)) ^ 5) →
      ∀ (F : ℕ → ℂ), Multiplicative F → OneBounded F →
      ∀ (r : ℤ) (q : ℕ), 2 ≤ q →
      (Real.log (H : ℝ)) ^ 5 ≤ (q : ℝ) →
      (q : ℝ) ≤ (H : ℝ) / (Real.log (H : ℝ)) ^ 5 →
      ∀ α : ℝ, IsCoprime (q : ℤ) r →
      |α - (r : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 →
      shortExponentialIntegral (mrtTypicalCoefficient I P F) X H α ≤
        C * (X : ℝ) * H * Real.log (Real.log (H : ℝ)) / Real.log (H : ℝ) +
          3 * (H : ℝ) * (X + H) * ∑ p ∈ P i, 1 / (p : ℝ) ^ 2 := by
  obtain ⟨C, hC, R₀, hbound⟩ := minor_arc_typical_log_saving
  refine ⟨3 * C, by positivity, R₀, ?_⟩
  intro ι I P hP hdis i hi X H hH hHX hlogH hloglog hrange F hF hFb
    r q hq hWq hqH α hcop happ
  obtain ⟨hJ, hPJ, hR, hgeom⟩ := minor_arc_prime_range_dyadics (P i) H R₀ (hP i hi)
    hlogH (fun p hp => (hrange p hp).2)
  have hbound' := hbound I P hP hdis i hi ((P i).image (Nat.log 2)) X H (Nat.log 2 H)
    (by omega) hHX hlogH hJ hPJ (fun p hp => (hrange p hp).1)
    (fun j hj => ⟨(hR j hj).1, (hR j hj).2.trans hHX⟩) hgeom
    F hF hFb r q hq hWq hqH α hcop happ
  apply hbound'.trans
  apply add_le_add _ le_rfl
  have hh := mul_le_mul_of_nonneg_left (minor_arc_dyadic_log_log_bound H hH hlogH hloglog)
    (by positivity : 0 ≤ C * (X : ℝ) * H)
  have hh' := div_le_div_of_nonneg_right hh (by linarith : 0 ≤ Real.log (H : ℝ))
  convert hh' using 1
  ring

end TwoPointCorrelations

end OAI
