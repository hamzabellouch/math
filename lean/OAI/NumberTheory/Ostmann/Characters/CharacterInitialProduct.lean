import OAI.NumberTheory.Ostmann.Characters.CharacterTargetCenters
import OAI.NumberTheory.Ostmann.Construction.InitialAtomGuards
import OAI.NumberTheory.Ostmann.Arithmetic.AtomIntervalRanges

namespace OAI

/-! # The complete initial product has the prescribed logarithmic window -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def characterFillerTarget {k : ℕ} (logX Δ J : ℝ)
    (T : Fin k → ℝ) (a : Fin k → Bool → ℝ) : ℝ :=
  (logX + Δ) / 2 - J - (∑ j, T j) - ∑ j, (a j false + a j true)

theorem character_log_center_sum (k : ℕ) (J F : ℝ) (T : Fin k → ℝ)
    (a : Fin k → Bool → ℝ) :
    (∑ v : CharacterRole k, characterLogCenter J T a F v) =
      2 * (J + (∑ j, T j) + (∑ j, (a j false + a j true)) + F) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_option,
    Fintype.sum_sum_type, Fintype.sum_unique, characterLogCenter]
  simp only [add_comm (a _ true) (a _ false)]
  ring

theorem character_initial_center (k : ℕ) (logX Δ J : ℝ) (T : Fin k → ℝ)
    (a : Fin k → Bool → ℝ) :
    (∑ v : CharacterRole k,
      characterLogCenter J T a (characterFillerTarget logX Δ J T a) v) = logX + Δ := by
  rw [character_log_center_sum]
  unfold characterFillerTarget
  ring

/-- Per-atom interval errors remain bounded after taking all positive and
conjugate copies, independent of the number of primes in the word. -/
theorem character_initial_product_window (k : ℕ) (logX Δ J c : ℝ)
    (T : Fin k → ℝ) (a : Fin k → Bool → ℝ)
    (lo hi : CharacterRole k → ℕ)
    (hlo : ∀ v, Real.exp (characterLogCenter J T a
      (characterFillerTarget logX Δ J T a) v - c) ≤ lo v)
    (hhi : ∀ v, (hi v : ℝ) ≤ Real.exp (characterLogCenter J T a
      (characterFillerTarget logX Δ J T a) v + c))
    (x : CopyScheduleAtoms (characterRole k) 0 → ℕ)
    (hx : ∀ r ∈ atomIntervalRanges (characterRole k) lo hi 0, r.Holds x) :
    let C := (Fintype.card (CharacterRole k) : ℝ) * c
    ((∏ v, x v : ℕ) : ℝ) / Real.exp logX ∈ Set.Icc (Real.exp (Δ - C)) (Real.exp (Δ + C)) := by
  intro C
  let w := characterLogCenter J T a (characterFillerTarget logX Δ J T a)
  have hr := (atomIntervalRanges_holds_iff (characterRole k) lo hi 0 x).mp hx
  have he : (∏ v : CharacterRole k, x ⟨v, trivial⟩) = ∏ v, x v :=
    (initialSurvivorEquiv (characterRole k)).prod_comp x
  have hsum : (∑ v : CharacterRole k, w v) = logX + Δ :=
    character_initial_center k logX Δ J T a
  have hl : Real.exp (logX + Δ - C) ≤ ((∏ v, x v : ℕ) : ℝ) := by
    calc
      _ = ∏ v : CharacterRole k, Real.exp (w v - c) := by
        rw [← Real.exp_sum, Finset.sum_sub_distrib, hsum]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, C]
      _ ≤ ∏ v : CharacterRole k, (x ⟨v, trivial⟩ : ℝ) := by
        apply Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le)
        intro v _
        exact (hlo v).trans (by exact_mod_cast (hr ⟨v, trivial⟩).1)
      _ = _ := by rw [← Nat.cast_prod, he]
  have hh : ((∏ v, x v : ℕ) : ℝ) ≤ Real.exp (logX + Δ + C) := by
    calc
      _ = ∏ v : CharacterRole k, (x ⟨v, trivial⟩ : ℝ) := by rw [← Nat.cast_prod, he]
      _ ≤ ∏ v : CharacterRole k, Real.exp (w v + c) := by
        apply Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        intro v _
        exact (show (x ⟨v, trivial⟩ : ℝ) ≤ hi v by exact_mod_cast (hr ⟨v, trivial⟩).2).trans (hhi v)
      _ = _ := by
        rw [← Real.exp_sum, Finset.sum_add_distrib, hsum]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, C]
  constructor
  · apply (le_div_iff₀ (Real.exp_pos logX)).mpr
    calc
      Real.exp (Δ - C) * Real.exp logX = Real.exp (logX + Δ - C) := by
        rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := hl
  · apply (div_le_iff₀ (Real.exp_pos logX)).mpr
    calc
      _ ≤ Real.exp (logX + Δ + C) := hh
      _ = Real.exp (Δ + C) * Real.exp logX := by
        rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
