import OAI.Combinatorics.ContingencyTables.Transport.RejectionLaw
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace OAI

/-! # Rejecting a uniform finite object through an explicit successful bijection -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture

noncomputable section
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
variable (p : S → Prop) (e : A ≃ {s // p s})

def partialEquivDraw (s : S) : Option A :=
  if h : p s then some (e.symm ⟨s,h⟩) else none

omit [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] in
lemma partialEquivDraw_eq_some (s : S) (a : A) :
    partialEquivDraw p e s=some a ↔ s=(e a).val := by
  constructor
  · intro h
    unfold partialEquivDraw at h
    split_ifs at h with hs
    · have hh := congrArg (fun a => (e a).val) (Option.some.inj h)
      simpa only [Equiv.apply_symm_apply] using hh
  · intro h
    subst s
    simp [partialEquivDraw,(e a).property]

omit [Fintype A] [Nonempty A] in
lemma partialEquiv_success_mass (a : A) :
    successMass (uniformLaw (α := S)) (partialEquivDraw p e) a=uniformMass (α := S) := by
  unfold successMass
  simp only [partialEquivDraw_eq_some,uniformLaw]
  simp

omit [Nonempty A] in
lemma partialEquiv_failure_mass :
    failureMass (uniformLaw (α := S)) (partialEquivDraw p e)=
      1-(Fintype.card A:ℚ)/(Fintype.card S:ℚ) := by
  have ht := success_failure_total (uniformLaw (α := S)) (partialEquivDraw p e)
  simp only [partialEquiv_success_mass,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at ht
  unfold uniformMass at ht
  rw [mul_one_div] at ht
  linarith

/-- The bound applies before any approximate law is introduced, so later
TV errors can be accumulated without conditioning on success. -/
theorem uniform_partial_retry_variation (fallback : A) (n : ℕ) :
    variation (retryLaw (uniformLaw (α := S)) (partialEquivDraw p e) fallback n)
      (uniformLaw (α := A)) ≤ (1-(Fintype.card A:ℚ)/(Fintype.card S:ℚ))^n := by
  let s : ℚ := (Fintype.card A:ℚ)/(Fintype.card S:ℚ)
  have hs0 : 0 ≤ s := by dsimp only [s]; positivity
  have hc : Fintype.card A ≤ Fintype.card S :=
    Fintype.card_le_of_injective (fun a => (e a).val)
      (Subtype.val_injective.comp e.injective)
  have hs1 : s ≤ 1 := by
    apply (div_le_one (by exact_mod_cast Fintype.card_pos (α := S))).mpr
    exact_mod_cast hc
  have he (a : A) : successMass (uniformLaw (α := S)) (partialEquivDraw p e) a=
      s*uniformMass (α := A) := by
    rw [partialEquiv_success_mass]
    dsimp only [s,uniformMass]
    have hn : (Fintype.card A:ℚ)≠0 := by exact_mod_cast (Fintype.card_pos (α := A)).ne'
    field_simp [hn]
  unfold variation
  simp only [retryLaw_mass,outputMass]
  simp_rw [he,partialEquiv_failure_mass]
  exact stationary_variation s hs0 hs1 n fallback

/-- A lower success bound gives the usual exponential failure tail. -/
theorem uniform_partial_retry_exp (fallback : A) (n : ℕ) (K : ℝ)
    (hs : 1/K ≤ (Fintype.card A:ℝ)/(Fintype.card S:ℝ)) :
    (variation (retryLaw (uniformLaw (α := S)) (partialEquivDraw p e) fallback n)
      (uniformLaw (α := A)):ℝ) ≤ Real.exp (-(n:ℝ)/K) := by
  have hv := uniform_partial_retry_variation p e fallback n
  have hc : Fintype.card A ≤ Fintype.card S :=
    Fintype.card_le_of_injective (fun a => (e a).val)
      (Subtype.val_injective.comp e.injective)
  have hj : (0:ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos (α := S)
  have hn : 0 ≤ 1-(Fintype.card A:ℝ)/(Fintype.card S:ℝ) := by
    have hh := (div_le_one hj).mpr (show (Fintype.card A:ℝ) ≤ Fintype.card S by exact_mod_cast hc)
    linarith
  have hv' : (variation (retryLaw (uniformLaw (α := S)) (partialEquivDraw p e) fallback n)
      (uniformLaw (α := A)):ℝ) ≤ (1-(Fintype.card A:ℝ)/(Fintype.card S:ℝ))^n := by
    simpa only [Rat.cast_pow,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_natCast] using
      (Rat.cast_le (K := ℝ)).mpr hv
  apply hv'.trans
  calc
    _ ≤ (Real.exp (-((Fintype.card A:ℝ)/(Fintype.card S:ℝ))))^n := by
      apply pow_le_pow_left₀ hn
      linarith [Real.add_one_le_exp (-((Fintype.card A:ℝ)/(Fintype.card S:ℝ)))]
    _ = Real.exp (-(n:ℝ)*((Fintype.card A:ℝ)/(Fintype.card S:ℝ))) := by
      rw [←Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hs (show (0:ℝ) ≤ n by positivity)
      rw [mul_one_div] at hh
      rw [neg_div]
      nlinarith

end
end ContingencyTables.FirstSuccess

end OAI
