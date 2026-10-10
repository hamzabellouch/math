import OAI.NumberTheory.TwoPoint.Bounds.CutoffDivisorTransfer
import OAI.NumberTheory.TwoPoint.Walks.RetainedDivisorMass
import OAI.NumberTheory.TwoPoint.Bounds.PrimeCountDilation

namespace OAI

/-! The rough coefficient families obtained by selecting at least one
constant term in the center-band expansion. Their support and unit bound
are derived from the actual finite prime products. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def nonrawRoughSupport (T : Finset ℕ) (H τ : ℝ) (u : ℕ) : Finset ℕ :=
  (retainedPrimeDivisors T).filter (fun w =>
    1 < w ∧ H < ((u * w : ℕ) : ℝ) ∧ ((u * w : ℕ) : ℝ) ≤ τ * H ∧ u.Coprime w)

noncomputable def nonrawRoughData (T : Finset ℕ) (H τ : ℝ)
    (a : ℕ → ℂ) (θ : ℂ) (u : ℕ) : RoughCoefficients where
  support := nonrawRoughSupport T H τ u
  coefficient w := a (u * w) * (-θ) ^ w.primeFactors.card

noncomputable def activeNonrawDivisors (S T : Finset ℕ) (H τ : ℝ) : Finset ℕ :=
  (retainedPrimeDivisors S).filter (fun u => (nonrawRoughSupport T H τ u).Nonempty)

lemma nonraw_support_primeFactors {T : Finset ℕ} (hT : ∀ p ∈ T, Nat.Prime p)
    {H τ : ℝ} {u w : ℕ} (hw : w ∈ nonrawRoughSupport T H τ u) :
    w.primeFactors ⊆ T :=
  retainedPrimeDivisor_factors T hT (mem_filter.mp hw).1

lemma nonraw_support_rough {T : Finset ℕ} (hT : ∀ p ∈ T, Nat.Prime p)
    {H τ P₀ : ℝ} (hlarge : ∀ p ∈ T, P₀ ≤ (p : ℝ)) {u w : ℕ}
    (hw : w ∈ nonrawRoughSupport T H τ u) : HasNoPrimeFactorBelow P₀ w := by
  intro p hp hp₀ hdiv
  have hwpos : 0 < w := lt_trans Nat.zero_lt_one (mem_filter.mp hw).2.1
  have hpw : p ∈ w.primeFactors := hp.mem_primeFactors hdiv hwpos.ne'
  have hplarge := hlarge p (nonraw_support_primeFactors hT hw hpw)
  exact (not_lt_of_ge hplarge) hp₀

lemma nonraw_support_bin {T : Finset ℕ} {H τ : ℝ} {u w : ℕ} (hu : 0 < u)
    (hw : w ∈ nonrawRoughSupport T H τ u) :
    H / (u : ℝ) < (w : ℝ) ∧ (w : ℝ) ≤ τ * (H / (u : ℝ)) := by
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  have hlo : H < (u : ℝ) * w := by simpa only [Nat.cast_mul] using (mem_filter.mp hw).2.2.1
  have hhi : (u : ℝ) * w ≤ τ * H := by simpa only [Nat.cast_mul] using (mem_filter.mp hw).2.2.2.1
  constructor
  · apply (div_lt_iff₀ hu').mpr
    nlinarith only [hlo]
  · calc
      _ ≤ (τ * H) / (u : ℝ) := (le_div_iff₀ hu').mpr (by nlinarith only [hhi])
      _ = _ := by ring

lemma nonrawRoughData_inBin {T : Finset ℕ} (hT : ∀ p ∈ T, Nat.Prime p)
    (H τ P₀ : ℝ) (hlarge : ∀ p ∈ T, P₀ ≤ (p : ℝ))
    (a : ℕ → ℂ) (ha : OneBounded a) (θ : ℂ) (hθ : ‖θ‖ ≤ 1)
    (u : ℕ) (hu : 0 < u) :
    (nonrawRoughData T H τ a θ u).InBin (H / (u : ℝ)) τ P₀ := by
  constructor
  · intro w hw
    exact ⟨(nonraw_support_bin hu hw).1, (nonraw_support_bin hu hw).2,
      nonraw_support_rough hT hlarge hw⟩
  · intro w hw
    have hwpos : 0 < w := lt_trans Nat.zero_lt_one (mem_filter.mp hw).2.1
    change ‖a (u * w) * (-θ) ^ w.primeFactors.card‖ ≤ 1
    rw [norm_mul, norm_pow, norm_neg]
    exact (mul_le_mul (ha _ (Nat.mul_pos hu hwpos))
      (pow_le_one₀ (norm_nonneg θ) hθ) (by positivity) zero_le_one).trans_eq (one_mul 1)

lemma activeNonrawDivisor_pos {S T : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    {H τ : ℝ} {u : ℕ} (hu : u ∈ activeNonrawDivisors S T H τ) : 0 < u :=
  retainedPrimeDivisor_pos S hS (mem_filter.mp hu).1

lemma activeNonrawDivisor_lower {S T : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hT : ∀ p ∈ T, Nat.Prime p)
    {H τ P₀ : ℝ} (hτ : 0 < τ) (hlarge : ∀ p ∈ T, P₀ ≤ (p : ℝ))
    {u : ℕ} (hu : u ∈ activeNonrawDivisors S T H τ) :
    P₀ / τ ≤ H / (u : ℝ) := by
  obtain ⟨w, hw⟩ := (mem_filter.mp hu).2
  have hw₁ : 1 < w := (mem_filter.mp hw).2.1
  obtain ⟨p, hp, hpw⟩ := Nat.exists_prime_and_dvd hw₁.ne'
  have hwpos : 0 < w := lt_trans Nat.zero_lt_one hw₁
  have hpT := nonraw_support_primeFactors hT hw (hp.mem_primeFactors hpw hwpos.ne')
  have hpw' : (p : ℝ) ≤ w := by exact_mod_cast Nat.le_of_dvd hwpos hpw
  have hPw : P₀ ≤ (w : ℝ) := (hlarge p hpT).trans hpw'
  have hub : (0 : ℝ) < u := by exact_mod_cast activeNonrawDivisor_pos hS hu
  have hhi : (u : ℝ) * w ≤ τ * H := by simpa only [Nat.cast_mul] using (mem_filter.mp hw).2.2.2.1
  apply (div_le_div_iff₀ hτ hub).mpr
  have hmul := mul_le_mul_of_nonneg_left hPw hub.le
  nlinarith only [hhi, hmul]

lemma nonraw_support_same_core {C T : Finset ℕ}
    (hC : ∀ p ∈ C, Nat.Prime p) (hT : ∀ p ∈ T, Nat.Prime p)
    (hdisj : Disjoint C T) {H τ : ℝ} {u w : ℕ}
    (hw : w ∈ nonrawRoughSupport T H τ u) :
    ∀ p ∈ C, p ∣ u * w ↔ p ∣ u := by
  intro p hp
  have hnot : ¬p ∣ w := by
    intro hpw
    have hwpos : 0 < w := lt_trans Nat.zero_lt_one (mem_filter.mp hw).2.1
    have hpT := nonraw_support_primeFactors hT hw ((hC p hp).mem_primeFactors hpw hwpos.ne')
    exact disjoint_left.mp hdisj hp hpT
  simp only [(hC p hp).dvd_mul, hnot, or_false]

lemma nonraw_cutoff_dilation {C T : Finset ℕ}
    (hC : ∀ p ∈ C, Nat.Prime p) (hT : ∀ p ∈ T, Nat.Prime p)
    (hdisj : Disjoint C T) {H τ : ℝ} {u w : ℕ}
    (hw : w ∈ nonrawRoughSupport T H τ u) (μ σ : ℝ) (F : ℝ → ℂ) (n : ℕ) :
    primeCountCutoff (C.filter (fun p => ¬p ∣ u * w)) μ σ F (u * n) =
      primeCountCutoff (C.filter (fun p => ¬p ∣ u)) μ σ F n :=
  primeCountCutoff_same_core_factors C hC (u * w) u n
    (nonraw_support_same_core hC hT hdisj hw) μ σ F

end TwoPointCorrelations

end OAI
