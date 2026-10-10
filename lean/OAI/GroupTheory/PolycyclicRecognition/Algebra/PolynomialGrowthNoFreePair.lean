import OAI.GroupTheory.PolycyclicRecognition.Algebra.CayleyWordMaps
import OAI.GroupTheory.PolycyclicRecognition.Analysis.PolynomialEnergyScales
import Mathlib.GroupTheory.FreeGroup.Reduce

namespace OAI

/-! # Polynomial-growth groups contain no free pair

Positive words give the literal exponential counting obstruction needed for
the linear-group alternative in the polynomial-growth argument.
-/
noncomputable section
namespace PolycyclicRecognition
open Finset Filter
open scoped Topology

def positiveFreeWord {α : Type*} (l : List α) : FreeGroup α :=
  FreeGroup.mk (l.map (fun a => (a, true)))

theorem positiveFreeWord_reduced {α : Type*} (l : List α) :
    FreeGroup.IsReduced (l.map (fun a => (a, true))) := by
  induction l with
  | nil => exact FreeGroup.IsReduced.nil
  | cons a l ih =>
    cases l with
    | nil => exact FreeGroup.IsReduced.singleton
    | cons b l =>
      rw [List.map_cons, List.map_cons, FreeGroup.isReduced_cons_cons]
      exact ⟨fun _ => rfl, ih⟩

theorem positiveFreeWord_injective {α : Type*} [DecidableEq α] :
    Function.Injective (positiveFreeWord (α := α)) := by
  intro l k h
  have ht := congrArg FreeGroup.toWord h
  simp only [positiveFreeWord, FreeGroup.toWord_mk,
    (positiveFreeWord_reduced l).reduce_eq, (positiveFreeWord_reduced k).reduce_eq] at ht
  have hf := congrArg (List.map Prod.fst) ht
  simpa [List.map_map, Function.comp_def] using hf

variable {G : Type*} [Group G] [DecidableEq G]

theorem free_pair_exponential_word_count (S : Finset G) (m : ℕ)
    (f : FreeGroup Bool →* G) (hf : Function.Injective f)
    (hgen : ∀ b : Bool, f (FreeGroup.of b) ∈ wordBall S m) (n : ℕ) :
    2 ^ n ≤ (wordBall S (m * n)).card := by
  have hword (l : List Bool) : f (positiveFreeWord l) ∈ wordBall S (m * l.length) := by
    induction l with
    | nil => simp [positiveFreeWord, ← FreeGroup.one_eq_mk]
    | cons b l ih =>
      have he : positiveFreeWord (b :: l) = FreeGroup.of b * positiveFreeWord l := rfl
      rw [he, map_mul]
      have h := mul_mem_wordBall (hgen b) ih
      simpa only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_comm] using h
  let φ : (Fin n → Bool) → G := fun w => f (positiveFreeWord (List.ofFn w))
  have hφ : Function.Injective φ :=
    hf.comp (positiveFreeWord_injective.comp List.ofFn_injective)
  let A := Finset.univ.image φ
  have hA : A ⊆ wordBall S (m * n) := by
    intro x hx
    obtain ⟨w, _, rfl⟩ := mem_image.mp hx
    simpa only [List.length_ofFn] using hword (List.ofFn w)
  calc
    2 ^ n = A.card := by simp [A, card_image_of_injective _ hφ]
    _ ≤ _ := card_le_card hA

theorem polynomial_word_growth_not_exponential
    (S : Finset G)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d)
    (m : ℕ) : ¬(∀ n, 2 ^ n ≤ (wordBall S (m * n)).card) := by
  intro hcount
  obtain ⟨C, d, hC⟩ := hvol
  have hbound (n : ℕ) : 1 ≤
      ((C : ℝ) * (1 + (m : ℝ)) ^ d) * ((1 + (n : ℝ)) ^ d * (1 / 2 : ℝ) ^ n) := by
    have hpow : (2 : ℝ) ^ n ≤ (C : ℝ) * (1 + ((m * n : ℕ) : ℝ)) ^ d := by
      exact_mod_cast (hcount n).trans (hC (m * n))
    have hbase : 1 + ((m * n : ℕ) : ℝ) ≤ (1 + (m : ℝ)) * (1 + (n : ℝ)) := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) n]
    calc
      1 = (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n := by rw [← mul_pow]; norm_num
      _ ≤ ((C : ℝ) * (1 + ((m * n : ℕ) : ℝ)) ^ d) * (1 / 2 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ ≤ ((C : ℝ) * ((1 + (m : ℝ)) * (1 + (n : ℝ))) ^ d) * (1 / 2 : ℝ) ^ n := by
        gcongr
      _ = _ := by rw [mul_pow]; ring
  have ht : Tendsto
      (fun n : ℕ => ((C : ℝ) * (1 + (m : ℝ)) ^ d) *
        ((1 + (n : ℝ)) ^ d * (1 / 2 : ℝ) ^ n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_nat_add_one_pow_mul_geometric d (q := 1 / 2) (by norm_num) (by norm_num)).const_mul
        ((C : ℝ) * (1 + (m : ℝ)) ^ d)
  have hh : (1 : ℝ) ≤ 0 := ge_of_tendsto ht (Eventually.of_forall hbound)
  norm_num at hh

theorem polynomial_growth_no_free_pair
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d)
    (f : FreeGroup Bool →* G) : ¬Function.Injective f := by
  intro hf
  obtain ⟨m₀, hm₀⟩ := wordBall_exhaustive S hS hgen (f (FreeGroup.of false))
  obtain ⟨m₁, hm₁⟩ := wordBall_exhaustive S hS hgen (f (FreeGroup.of true))
  let m := max m₀ m₁
  have hg (b : Bool) : f (FreeGroup.of b) ∈ wordBall S m := by
    cases b
    · exact wordBall_mono S (le_max_left _ _) hm₀
    · exact wordBall_mono S (le_max_right _ _) hm₁
  exact polynomial_word_growth_not_exponential S hvol m
    (free_pair_exponential_word_count S m f hf hg)

end PolycyclicRecognition

end

end OAI
