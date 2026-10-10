import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-! # Elementary interpolation estimates on measurable sets

Positive length supplies separated interpolation nodes. Lagrange interpolation
then bounds a polynomial on an interval in terms of its values on these nodes.
These bounds give the scalar Remez estimate on measurable sets.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric MeasureTheory Polynomial
open scoped ENNReal

/-- A set of length greater than `2*n*δ` contains `n` points separated by `δ`.
No regularity of the set is needed. -/
theorem exists_separated_finset_of_length (S : Set ℝ) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hm : 2 * (n : ℝ) * δ < (volume S).toReal) :
    ∃ s : Finset ℝ, s.card = n ∧ (↑s : Set ℝ) ⊆ S ∧
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ |x - y| := by
  classical
  induction n with
  | zero => exact ⟨∅, rfl, by simp, by simp⟩
  | succ n ih =>
    have hm' : 2 * (n : ℝ) * δ < (volume S).toReal := by
      push_cast at hm
      nlinarith
    obtain ⟨s, hs, hS, hsep⟩ := ih hm'
    have hex : ∃ x ∈ S, ∀ y ∈ s, δ ≤ |x - y| := by
      by_contra h
      have hcover : S ⊆ ⋃ y ∈ s, ball y δ := by
        intro x hx
        push Not at h
        obtain ⟨y, hy, hxy⟩ := h x hx
        exact mem_iUnion.2 ⟨y, mem_iUnion.2 ⟨hy, by simpa [Real.dist_eq] using hxy⟩⟩
      have hfinite : volume (⋃ y ∈ s, ball y δ) ≠ ∞ :=
        (measure_biUnion_lt_top s.finite_toSet (fun y _ => by
          rw [Real.volume_ball]
          exact ENNReal.ofReal_lt_top)).ne
      have hb := (measureReal_mono hcover hfinite).trans
        (measureReal_biUnion_finset_le (μ := volume) s (fun y => ball y δ))
      simp only [measureReal_def, Real.volume_ball,
        ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * δ), Finset.sum_const,
        nsmul_eq_mul, hs] at hb
      push_cast at hm
      nlinarith
    obtain ⟨x, hx, hxsep⟩ := hex
    have hxs : x ∉ s := by
      intro hx'
      have hh := hxsep x hx'
      simp only [sub_self, abs_zero] at hh
      linarith
    refine ⟨insert x s, by simp [hxs, hs], ?_, ?_⟩
    · simpa only [Finset.coe_insert] using insert_subset hx hS
    · intro a ha b hb hab
      by_cases hax : a = x
      · subst a
        exact hxsep b ((Finset.mem_insert.1 hb).resolve_left (Ne.symm hab))
      · have has : a ∈ s := (Finset.mem_insert.1 ha).resolve_left hax
        by_cases hbx : b = x
        · subst b
          simpa only [abs_sub_comm a x] using hxsep a has
        · exact hsep a has b ((Finset.mem_insert.1 hb).resolve_left hbx) hab

/-- Explicit interpolation bound, with the separation and interval radius
visible. The degree may be strictly smaller than the number of nodes. -/
theorem polynomial_bound_of_separated_nodes (p : ℝ[X]) (s : Finset ℝ)
    (hdeg : p.degree < s.card) (δ R η : ℝ) (hδ : 0 < δ)
    (hR : 0 ≤ R) (hη : 0 ≤ η)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → δ ≤ |a - b|)
    (hs : ∀ a ∈ s, |a| ≤ R) (hp : ∀ a ∈ s, |p.eval a| ≤ η)
    (x : ℝ) (hx : |x| ≤ R) :
    |p.eval x| ≤ (s.card : ℝ) * η * (2 * R / δ) ^ (s.card - 1) := by
  classical
  have hterm (a : ℝ) (ha : a ∈ s) :
      |(Lagrange.basis s id a).eval x| ≤ (2 * R / δ) ^ (s.card - 1) := by
    rw [Lagrange.basis, eval_prod, Finset.abs_prod]
    have hfactor (b : ℝ) (hb : b ∈ s.erase a) :
        |(Lagrange.basisDivisor (id a) (id b)).eval x| ≤ 2 * R / δ := by
      obtain ⟨hba, hb⟩ := Finset.mem_erase.1 hb
      have hsep' := hsep a ha b hb (Ne.symm hba)
      have hnum : |x - b| ≤ 2 * R := by
        have := abs_sub x b
        linarith [hs b hb]
      simp only [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub,
        eval_X, id_eq, abs_mul, abs_inv]
      simpa only [div_eq_mul_inv, mul_comm] using
        (div_le_div₀ (by positivity : 0 ≤ 2 * R) hnum hδ hsep')
    calc
      (∏ b ∈ s.erase a, |(Lagrange.basisDivisor (id a) (id b)).eval x|) ≤
          ∏ _b ∈ s.erase a, (2 * R / δ) :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) hfactor
      _ = (2 * R / δ) ^ (s.card - 1) := by
        rw [Finset.prod_const, Finset.card_erase_of_mem ha]
  have heq := Lagrange.eq_interpolate (v := id) (s := s) Function.injective_id.injOn hdeg
  conv_lhs => rw [heq, Lagrange.interpolate_apply, eval_finsetSum]
  calc
    |∑ a ∈ s, (C (p.eval (id a)) * Lagrange.basis s id a).eval x| ≤
        ∑ a ∈ s, |(C (p.eval (id a)) * Lagrange.basis s id a).eval x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ s, η * (2 * R / δ) ^ (s.card - 1) := by
      apply Finset.sum_le_sum
      intro a ha
      simp only [eval_mul, eval_C, id_eq, abs_mul]
      exact mul_le_mul (hp a ha) (hterm a ha) (abs_nonneg _) hη
    _ = (s.card : ℝ) * η * (2 * R / δ) ^ (s.card - 1) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]

end PolycyclicRecognition

end

end OAI
