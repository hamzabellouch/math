import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.Divergence

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.FiniteEntropy
variable {X Y : Type*} [Fintype X] [Fintype Y]

noncomputable def pushMass (f : X → Y) (P : X → ℝ) (y : Y) : ℝ :=
  ∑ x, if f x = y then P x else 0

omit [Fintype Y] in
lemma pushMass_nonneg (f : X → Y) (P : X → ℝ) (hP : ∀ x, 0 ≤ P x) (y : Y) :
    0 ≤ pushMass f P y := by
  exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp_all

lemma pushMass_sum (f : X → Y) (P : X → ℝ) :
    ∑ y, pushMass f P y = ∑ x, P x := by
  classical
  simp only [pushMass]
  rw [Finset.sum_comm]
  simp

omit [Fintype Y] in
lemma le_pushMass (f : X → Y) (P : X → ℝ) (hP : ∀ x, 0 ≤ P x) (x : X) :
    P x ≤ pushMass f P (f x) := by
  classical
  have := Finset.single_le_sum (s := Finset.univ)
    (f := fun z => if f z = f x then P z else 0)
    (fun z _ => by split_ifs <;> simp_all) (Finset.mem_univ x)
  simpa [pushMass] using this

lemma sum_pushMass_mul (f : X → Y) (P : X → ℝ) (g : Y → ℝ) :
    ∑ y, pushMass f P y * g y = ∑ x, P x * g (f x) := by
  classical
  simp only [pushMass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [ite_mul, zero_mul]
  simp

lemma log_sum_inequality (P R : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hR : ∀ x, 0 ≤ R x) (hs : ∀ x, 0 < P x → 0 < R x) :
    (∑ x, P x)*Real.log ((∑ x, P x)/(∑ x, R x)) ≤ divergence P R := by
  classical
  let A := ∑ x, P x
  let B := ∑ x, R x
  have hA : 0 ≤ A := Finset.sum_nonneg fun x _ => hP x
  rcases eq_or_lt_of_le hA with hA | hA
  · have hz : ∀ x, P x = 0 := by
      intro x
      have hx := Finset.single_le_sum (fun y _ => hP y) (Finset.mem_univ x)
      dsimp [A] at hA
      linarith [hP x]
    simp [hz, divergence]
  have hB : 0 < B := by
    obtain ⟨x, hx⟩ : ∃ x, 0 < P x := by
      by_contra! hn
      have ht := Finset.sum_nonpos (s := Finset.univ) (fun x _ => hn x)
      exact (not_le_of_gt hA) ht
    exact (hs x hx).trans_le (Finset.single_le_sum (fun y _ => hR y) (Finset.mem_univ x))
  let S : X → ℝ := fun x => R x * (A/B)
  have hS : ∀ x, 0 ≤ S x := fun x => mul_nonneg (hR x) (div_pos hA hB).le
  have hpos : ∀ x, 0 < P x → 0 < S x := fun x hx => mul_pos (hs x hx) (div_pos hA hB)
  have hmass : ∑ x, S x = A := by
    simp only [S, ← Finset.sum_mul]
    change B * (A/B) = A
    field_simp
  have hb := mass_sub_le_divergence P S hP hS hpos
  have he : divergence P S = divergence P R - A*Real.log (A/B) := by
    have ht (x : X) : P x * Real.log (P x / S x) =
        P x * Real.log (P x / R x) - P x * Real.log (A/B) := by
      rcases eq_or_lt_of_le (hP x) with hz | hp
      · simp [← hz]
      · have hr := hs x hp
        simp only [S, Real.log_div hp.ne' (mul_pos hr (div_pos hA hB)).ne',
          Real.log_mul hr.ne' (div_pos hA hB).ne', Real.log_div hp.ne' hr.ne']
        ring
    simp only [divergence, ht, Finset.sum_sub_distrib, ← Finset.sum_mul, A]
  rw [hmass, he] at hb
  change A*Real.log (A/B) ≤ divergence P R
  dsimp [A] at hb ⊢
  linarith

theorem divergence_pushMass_le (f : X → Y) (P R : X → ℝ)
    (hP : ∀ x, 0 ≤ P x) (hR : ∀ x, 0 ≤ R x)
    (hs : ∀ x, 0 < P x → 0 < R x) :
    divergence (pushMass f P) (pushMass f R) ≤ divergence P R := by
  classical
  have hf (y : Y) := log_sum_inequality
    (fun x => if f x = y then P x else 0) (fun x => if f x = y then R x else 0)
    (fun x => by split_ifs <;> simp_all) (fun x => by split_ifs <;> simp_all)
    (fun x hx => by split_ifs at hx ⊢ <;> simp_all)
  have ht (x : X) (y : Y) :
      (if f x = y then P x else 0) *
          Real.log ((if f x = y then P x else 0)/(if f x = y then R x else 0)) =
        if f x = y then P x * Real.log (P x / R x) else 0 := by
    split_ifs <;> simp
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun y _ => hf y)
  simp only [divergence, ht] at hh
  rw [Finset.sum_comm] at hh
  simpa [pushMass, divergence] using hh

end CriticalPercolation.FiniteEntropy

end
end

end OAI
