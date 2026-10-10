import OAI.NumberTheory.Ostmann.Characters.CharacterTargetCellData
import OAI.NumberTheory.Ostmann.Construction.BinnedWordNorm

namespace OAI

/-! # One common rotation and the original, unrotated character priors -/
namespace Ostmann
open scoped Classical BigOperators

def quarterTurn (q : Bool × Bool) : ℂ :=
  if q.1 then (if q.2 then 1 else -1) else (if q.2 then Complex.I else -Complex.I)

theorem quarterTurn_norm (q : Bool × Bool) : ‖quarterTurn q‖ = 1 := by
  rcases q with ⟨b, c⟩
  cases b <;> cases c <;> simp [quarterTurn]

theorem exists_positive_quarterTurn (z : ℂ) :
    ∃ q : Bool × Bool, ‖z‖ / 2 ≤ (quarterTurn q * z).re := by
  have hnorm := Complex.norm_le_abs_re_add_abs_im z
  by_cases hr : ‖z‖ / 2 ≤ |z.re|
  · by_cases hs : 0 ≤ z.re
    · refine ⟨(true, true), ?_⟩
      simpa [quarterTurn, abs_of_nonneg hs] using hr
    · refine ⟨(true, false), ?_⟩
      simpa [quarterTurn, abs_of_neg (lt_of_not_ge hs)] using hr
  · have hi : ‖z‖ / 2 ≤ |z.im| := by linarith
    by_cases hs : 0 ≤ z.im
    · refine ⟨(false, false), ?_⟩
      simpa [quarterTurn, Complex.mul_re, abs_of_nonneg hs] using hi
    · refine ⟨(false, true), ?_⟩
      simpa [quarterTurn, Complex.mul_re, abs_of_neg (lt_of_not_ge hs)] using hi

/-- A single quarter turn retains at least a quarter of the prime mass.
Thereafter the word and cell estimates can use the original characters. -/
theorem common_positive_character_rotation (P : Finset ℕ) (m : ℕ → ℂ) (δ : ℝ)
    (hm : ∀ p ∈ P, δ ≤ ‖m p‖) :
    ∃ ζ : ℂ, ∃ E : Finset ℕ, ‖ζ‖ = 1 ∧ E ⊆ P ∧
      (∑ p ∈ P, (p : ℝ)⁻¹) / 4 ≤ (∑ p ∈ E, (p : ℝ)⁻¹) ∧
      ∀ p ∈ E, δ / 2 ≤ (ζ * m p).re := by
  choose q hq using (fun p : ℕ => exists_positive_quarterTurn (m p))
  let mass : (Bool × Bool) → ℝ := fun a => ∑ p ∈ P.filter (fun p => q p = a), (p : ℝ)⁻¹
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ mass Finset.univ_nonempty
  refine ⟨quarterTurn a, P.filter (fun p => q p = a), quarterTurn_norm a,
    Finset.filter_subset _ _, ?_, ?_⟩
  · have hsum : (∑ a, mass a) = ∑ p ∈ P, (p : ℝ)⁻¹ := by
      simp only [mass, Finset.sum_filter]
      rw [Finset.sum_comm]
      simp
    have hbound : (∑ a, mass a) ≤ 4 * mass a := by
      calc
        _ ≤ ∑ _a : Bool × Bool, mass a := Finset.sum_le_sum (fun b hb => ha b hb)
        _ = _ := by simp
    change (∑ p ∈ P, (p : ℝ)⁻¹) / 4 ≤ mass a
    rw [hsum] at hbound
    linarith
  · intro p hp
    obtain ⟨hpP, hpq⟩ := Finset.mem_filter.mp hp
    have hh := hq p
    rw [hpq] at hh
    linarith [hm p hpP]

theorem norm_weighted_common_rotation {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (F : ι → ℂ) (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    ‖∑ i, (w i : ℂ) * (ζ * F i)‖ = ‖∑ i, (w i : ℂ) * F i‖ := by
  have he : (∑ i, (w i : ℂ) * (ζ * F i)) = ζ * ∑ i, (w i : ℂ) * F i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, norm_mul, hζ, one_mul]

/-- The positive rotated cell mean supplies the norm bound used by the
unrotated initial character statistic, without modifying the harmonic law. -/
theorem CharacterTargetWord.cell_unrotated_mean {P : Finset ℕ} {G : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : ℝ} (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (w : CharacterTargetWord P (fun p => ζ * G p) c δ U k T)
    (h : ℕ) (hh : h ∈ w.indices) :
    δ / 2 ≤ ‖∑ p : P, (primeSubsetPrior P (w.cell h) p : ℂ) * G p‖ := by
  have hm := (w.cell_mean h hh).trans (Complex.re_le_norm _)
  rwa [norm_weighted_common_rotation _ _ ζ hζ] at hm

end Ostmann

end OAI
