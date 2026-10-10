import OAI.NumberTheory.TwoPointCorrelations.MRTPrimeBands
import OAI.NumberTheory.TwoPointCorrelations.RoughSieveProbability
import OAI.NumberTheory.TwoPointCorrelations.CrudeWordCounting

namespace OAI

/-! The finite missing-band sieve in MRT, with its full Bonferroni and
interval-boundary errors.  CRT, not an independence assumption on integers,
supplies every intersection estimate. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical BigOperators

theorem mrt_prime_avoidance_probability (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (A N : ℕ) [NeZero N] (r : ℕ) (Y : ℝ)
    (hY : 0 ≤ Y) (hmax : ∀ p ∈ P, (p : ℝ) ≤ Y) :
    (uniformFiniteLaw (Fin N)).probability (fun j => mrtPrimeAvoids P (A + j.val)) ≤
      Real.exp (-(∑ p ∈ P, 1 / (p : ℝ))) +
        Real.exp (2 * ∑ p ∈ P, 1 / (p : ℝ)) / (2 : ℝ) ^ (2 * r + 1) +
        1 / (N : ℝ) * (2 * r + 1 : ℕ) * ((P.card : ℝ) * Y + 1) ^ (2 * r) := by
  let (p : P) : NeZero (p : ℕ) := ⟨(hP p p.property).ne_zero⟩
  have hh := finite_interval_sieve (fun p : P => (p : ℕ)) (primeSet_pairwise_coprime P hP)
    A N (fun _ x => x = 0) r Y hY (fun p => hmax p p.property)
  have he : avoidsEvents univ (fun p : P => fun j : Fin N =>
      ((A + j.val : ℕ) : ZMod (p : ℕ)) = 0) =
      (fun j => mrtPrimeAvoids P (A + j.val)) := by
    funext j
    simp only [avoidsEvents, mem_univ, forall_true_left, mrtPrimeAvoids,
      Subtype.forall, ZMod.natCast_eq_zero_iff]
  simp only [he, oneFormBadDensity, Fintype.card_coe] at hh
  have ht := elementarySymmetric_exp_bound (univ : Finset P)
    (fun p => 1 / (p : ℝ)) (fun p _ => by positivity) (2 * r + 1) 2 (by norm_num)
  have hp := oneForm_product_bound P (fun p hp => (hP p hp).two_le)
  rw [prod_subtype (p := fun p : ℕ => p ∈ P) P (fun _ => Iff.rfl)] at hp
  have hsum : (∑ p : P, 1 / (p : ℝ)) = ∑ p ∈ P, 1 / (p : ℝ) :=
    (sum_subtype (p := fun p : ℕ => p ∈ P) P (fun _ => Iff.rfl)
      (fun p => (1 : ℝ) / p)).symm
  rw [hsum] at ht
  exact hh.trans (add_le_add (add_le_add hp ht) le_rfl)

/-- Mertens supplies the main term `log P/log Q`; both finite-sieve errors
remain explicit for choosing the typical-factorization parameters. -/
theorem mrt_missing_band_probability : ∃ C : ℝ, 0 < C ∧
    ∀ (P Q : ℝ), 2 ≤ P → P ≤ Q → ∀ (A N : ℕ) [NeZero N] (r : ℕ),
    (uniformFiniteLaw (Fin N)).probability
      (fun j => mrtPrimeAvoids (mrtPrimeBand P Q) (A + j.val)) ≤
      C * Real.log P / Real.log Q +
        Real.exp (2 * ∑ p ∈ mrtPrimeBand P Q, 1 / (p : ℝ)) / (2 : ℝ) ^ (2 * r + 1) +
        1 / (N : ℝ) * (2 * r + 1 : ℕ) *
          (((mrtPrimeBand P Q).card : ℝ) * Q + 1) ^ (2 * r) := by
  obtain ⟨C, hC, hprod⟩ := mrt_prime_band_product
  refine ⟨C, hC, ?_⟩
  intro P Q hP hPQ A N _ r
  have hQ : 0 ≤ Q := (by linarith : (0 : ℝ) ≤ P).trans hPQ
  have hh := mrt_prime_avoidance_probability (mrtPrimeBand P Q)
    (fun _ hp => mrtPrimeBand_prime hp) A N r Q hQ
    (fun _ hp => (mrtPrimeBand_bounds (by linarith) hQ hp).2)
  exact hh.trans (add_le_add (add_le_add (hprod P Q hP hPQ) le_rfl) le_rfl)

/-- Failure of typical factorization is a union of the literal missing-band
events, so the numerical single-band bounds add without any independence. -/
theorem mrtTypical_missing_union {ι α : Type*} [Fintype ι] [Fintype α]
    (P : ι → Finset ℕ) (μ : FiniteLaw α) (n : α → ℕ) :
    μ.probability (fun x => ¬mrtTypical univ P (n x)) ≤
      ∑ i, μ.probability (fun x => mrtPrimeAvoids (P i) (n x)) := by
  have he : (fun x => ¬mrtTypical univ P (n x)) =
      (fun x => ∃ i, mrtPrimeAvoids (P i) (n x)) := by
    funext x
    simp only [mrtTypical, mem_univ, forall_true_left, mrtPrimeAvoids]
    push Not
    rfl
  rw [he]
  exact μ.probability_exists_le _

end TwoPointCorrelations

end OAI
