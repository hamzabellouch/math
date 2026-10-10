import OAI.GroupTheory.PolycyclicRecognition.Algebra.RegularHilbertRepresentation

namespace OAI

/-! # Finite-propagation lazy random walk vectors in the regular representation -/
noncomputable section
namespace PolycyclicRecognition
open Finset
variable {G : Type*} [Group G] [DecidableEq G]

omit [DecidableEq G] in
theorem unitaryLazyStep_eq_average {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (S : Finset G) (hne : S.Nonempty)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (v : E) :
    unitaryLazyStep S ρ v = (1 / 2 : ℝ) • v +
      (1 / (2 * S.card : ℝ)) • ∑ s ∈ S, ρ s v := by
  have hm : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (card_ne_zero.mpr hne)
  have hc : (1 / (2 * S.card : ℝ)) * S.card = 1 / 2 := by field_simp
  rw [unitaryLazyStep, unitaryGeneratorLaplacian_apply, sum_sub_distrib, sum_const,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_sub, ← mul_smul, hc]
  module

def regularLazyWalk (S : Finset G) : ℕ → RegularHilbert G
  | 0 => regularDirac
  | n + 1 => unitaryLazyStep S regularHilbertRepresentation (regularLazyWalk S n)

theorem regularLazyWalk_succ_apply (S : Finset G) (hne : S.Nonempty) (n : ℕ) (x : G) :
    regularLazyWalk S (n + 1) x = (1 / 2 : ℝ) * regularLazyWalk S n x +
      (1 / (2 * S.card : ℝ)) * ∑ s ∈ S, regularLazyWalk S n (s⁻¹ * x) := by
  rw [regularLazyWalk, unitaryLazyStep_eq_average S hne]
  simp only [regularHilbert_add_apply, regularHilbert_smul_apply,
    regularHilbert_sum_apply, regularHilbertRepresentation_apply]

theorem regularLazyWalk_nonneg (S : Finset G) (hne : S.Nonempty) (n : ℕ) (x : G) :
    0 ≤ regularLazyWalk S n x := by
  induction n generalizing x with
  | zero => simp [regularLazyWalk, regularDirac_apply]; split_ifs <;> norm_num
  | succ n ih =>
    rw [regularLazyWalk_succ_apply S hne]
    exact add_nonneg (mul_nonneg (by norm_num) (ih x))
      (mul_nonneg (by positivity) (sum_nonneg (fun _ _ => ih _)))

theorem regularLazyWalk_support (S : Finset G) (hne : S.Nonempty) (n : ℕ)
    (x : G) (hx : x ∉ wordBall S n) : regularLazyWalk S n x = 0 := by
  induction n generalizing x with
  | zero =>
    have hx' : x ≠ 1 := by simpa [wordBall_zero] using hx
    simp [regularLazyWalk, regularDirac_apply, hx']
  | succ n ih =>
    rw [regularLazyWalk_succ_apply S hne]
    have hx' : x ∉ wordBall S n := fun h => hx (wordBall_mono S (Nat.le_succ n) h)
    rw [ih x hx']
    have hzero : ∀ s ∈ S, regularLazyWalk S n (s⁻¹ * x) = 0 := by
      intro s hs
      apply ih
      intro hh
      apply hx
      have hs' : s ∈ wordBall S 1 :=
        (mem_wordBall_iff S 1 s).mpr ⟨[s], le_rfl, by simpa using hs, by simp⟩
      simpa only [mul_inv_cancel_left, Nat.add_comm 1 n] using mul_mem_wordBall hs' hh
    simp [sum_eq_zero hzero]

omit [Group G] [DecidableEq G] in
theorem regularHilbert_sum_extend {A B : Finset G} (hAB : A ⊆ B)
    (v : RegularHilbert G) (hv : ∀ x, x ∉ A → v x = 0) :
    (∑ x ∈ B, v x) = ∑ x ∈ A, v x :=
  (sum_subset hAB (fun x _ hx => hv x hx)).symm

theorem regularHilbert_translated_mass (S : Finset G) (n : ℕ)
    (v : RegularHilbert G) (hv : ∀ x, x ∉ wordBall S n → v x = 0)
    {s : G} (hs : s ∈ S) :
    (∑ x ∈ wordBall S (n + 1), v (s⁻¹ * x)) = ∑ x ∈ wordBall S n, v x := by
  let A := (wordBall S n).image (s * ·)
  have hs' : s ∈ wordBall S 1 :=
    (mem_wordBall_iff S 1 s).mpr ⟨[s], le_rfl, by simpa using hs, by simp⟩
  have hAB : A ⊆ wordBall S (n + 1) := by
    rintro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    simpa only [Nat.add_comm 1 n] using mul_mem_wordBall hs' hy
  calc
    _ = ∑ x ∈ A, v (s⁻¹ * x) := by
      symm
      apply sum_subset hAB
      intro x _ hx
      apply hv
      intro hh
      exact hx (mem_image.mpr ⟨s⁻¹ * x, hh, mul_inv_cancel_left s x⟩)
    _ = _ := by
      rw [sum_image]
      · simp
      · intro x _ y _ h
        exact mul_left_cancel h

theorem regularLazyWalk_mass (S : Finset G) (hne : S.Nonempty) (n : ℕ) :
    (∑ x ∈ wordBall S n, regularLazyWalk S n x) = 1 := by
  induction n with
  | zero => simp [regularLazyWalk, wordBall_zero, regularDirac_apply]
  | succ n ih =>
    simp_rw [regularLazyWalk_succ_apply S hne, sum_add_distrib, ← mul_sum]
    rw [regularHilbert_sum_extend (wordBall_mono S (Nat.le_succ n)) _
      (regularLazyWalk_support S hne n), ih, sum_comm]
    have ht : (∑ s ∈ S, ∑ x ∈ wordBall S (n + 1),
        regularLazyWalk S n (s⁻¹ * x)) = S.card := by
      calc
        _ = ∑ _s ∈ S, (1 : ℝ) := by
          apply sum_congr rfl
          intro s hs
          rw [regularHilbert_translated_mass S n _ (regularLazyWalk_support S hne n) hs, ih]
        _ = _ := by simp
    rw [ht]
    have hm : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (card_ne_zero.mpr hne)
    field_simp
    ring

end PolycyclicRecognition

end

end OAI
