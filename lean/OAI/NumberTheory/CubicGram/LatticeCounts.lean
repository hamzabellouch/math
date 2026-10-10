import Mathlib
import OAI.NumberTheory.CubicGram.PrimaryNormalization

namespace OAI

/-! Eisenstein lattice counts and arbitrarily small divisor losses. -/

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

@[simp] lemma norm_mul_eq (a b : Eisenstein) : norm (a*b) = norm a * norm b :=
  Complex.normSq_mul _ _
@[simp] lemma norm_one_eq : norm (1 : Eisenstein) = 1 := Complex.normSq_one
lemma norm_pos_of_ne_zero {a : Eisenstein} (ha : a ≠ 0) : 0 < norm a :=
  lt_of_le_of_ne (norm_nonneg a) (Ne.symm (norm_eq_zero_iff.not.mpr ha))
lemma one_le_norm {a : Eisenstein} (ha : a ≠ 0) : 1 ≤ norm a := by
  rw [← normNat_cast]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => ha (norm_eq_zero_iff.mp
    (by rw [← normNat_cast, h]; simp)))
lemma norm_finset_prod {α : Type*} (s : Finset α) (f : α → Eisenstein) :
    norm (∏ p ∈ s, f p) = ∏ p ∈ s, norm (f p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih => simp [hp, ih]

def nonzeroNormBall (X : ℝ) : Finset Eisenstein :=
  (finite_norm_le X).toFinset.filter (· ≠ 0)
@[simp] lemma mem_nonzeroNormBall {z : Eisenstein} {X : ℝ} :
    z ∈ nonzeroNormBall X ↔ norm z ≤ X ∧ z ≠ 0 := by
  simp [nonzeroNormBall]

theorem nonzeroNormBall_card_le {X : ℝ} (hX : 0 ≤ X) :
    ((nonzeroNormBall X).card : ℝ) ≤ 18*X := by
  by_cases hX1 : 1 ≤ X
  · let C : ℤ := ⌊Real.sqrt (2*X)⌋
    have hC1 : (1 : ℤ) ≤ C := Int.le_floor.mpr (by
      exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by norm_num; nlinarith))
    have hC0 : 0 ≤ (C : ℝ) := by exact_mod_cast (show 0 ≤ C by omega)
    have hC : (C : ℝ) ≤ Real.sqrt (2*X) := Int.floor_le _
    have hCsq : (C : ℝ)^2 ≤ 2*X := by
      nlinarith [Real.sq_sqrt (show 0 ≤ 2*X by positivity)]
    let box := (Finset.Icc (-C) C).product (Finset.Icc (-C) C)
    have hsub : nonzeroNormBall X ⊆ box.image (fun p => ofCoords p.1 p.2) := by
      intro z hz
      obtain ⟨a,b,hz'⟩ := exists_coordinates z
      have hn : (a : ℝ)^2 - a*b + b^2 ≤ X := by
        have hn' : norm z = ((a^2-a*b+b^2 : ℤ) : ℝ) := by
          rw [norm, hz', coordinates_norm]
        have hz := (mem_nonzeroNormBall.mp hz).1
        rw [hn'] at hz
        exact_mod_cast hz
      have ha2 : (a : ℝ)^2 ≤ 2*X := by nlinarith [sq_nonneg ((a : ℝ)-b)]
      have hb2 : (b : ℝ)^2 ≤ 2*X := by nlinarith [sq_nonneg ((a : ℝ)-b)]
      have hab : -(Real.sqrt (2*X)) ≤ (a : ℝ) ∧ (a : ℝ) ≤ Real.sqrt (2*X) := by
        have := (sq_le_sq₀ (abs_nonneg (a : ℝ)) (Real.sqrt_nonneg (2*X))).mp
          (by rw [sq_abs, Real.sq_sqrt (show 0 ≤ 2*X by positivity)]; exact ha2)
        exact abs_le.mp this
      have hbb : -(Real.sqrt (2*X)) ≤ (b : ℝ) ∧ (b : ℝ) ≤ Real.sqrt (2*X) := by
        have := (sq_le_sq₀ (abs_nonneg (b : ℝ)) (Real.sqrt_nonneg (2*X))).mp
          (by rw [sq_abs, Real.sq_sqrt (show 0 ≤ 2*X by positivity)]; exact hb2)
        exact abs_le.mp this
      have ha : a ∈ Finset.Icc (-C) C := by
        simp only [Finset.mem_Icc]
        exact ⟨by have := Int.le_floor.mpr (show ((-a : ℤ) : ℝ) ≤ Real.sqrt (2*X) by
                    push_cast; linarith); dsimp [C] at *; omega,
          Int.le_floor.mpr hab.2⟩
      have hb : b ∈ Finset.Icc (-C) C := by
        simp only [Finset.mem_Icc]
        exact ⟨by have := Int.le_floor.mpr (show ((-b : ℤ) : ℝ) ≤ Real.sqrt (2*X) by
                    push_cast; linarith); dsimp [C] at *; omega,
          Int.le_floor.mpr hbb.2⟩
      exact Finset.mem_image.mpr ⟨(a,b), Finset.mem_product.mpr ⟨ha,hb⟩, Subtype.ext hz'.symm⟩
    have hc : (nonzeroNormBall X).card ≤ box.card :=
      (Finset.card_le_card hsub).trans (Finset.card_image_le)
    have heq : (box.card : ℝ) = (2*(C : ℝ)+1)^2 := by
      dsimp [box]
      rw [Finset.card_product, Int.card_Icc]
      push_cast
      have hv : ((C+1- -C).toNat : ℝ) = (C+1- -C : ℤ) := by
        exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ C+1- -C by omega)
      rw [hv]
      push_cast
      ring
    have hc' : ((nonzeroNormBall X).card : ℝ) ≤ (2*(C : ℝ)+1)^2 := by
      rw [← heq]; exact_mod_cast hc
    have hC1' : (1 : ℝ) ≤ C := by exact_mod_cast hC1
    nlinarith [sq_nonneg ((C : ℝ)-1)]
  · have hempty : nonzeroNormBall X = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      have hz := mem_nonzeroNormBall.mp hz
      exact hX1 ((one_le_norm hz.2).trans hz.1)
    simp only [hempty, Finset.card_empty, Nat.cast_zero]
    positivity

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem primeDivisorWeight_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : Eisenstein, primary a → Squarefree a →
      (2 : ℝ)^(primaryPrimeFactors a).card ≤ C * norm a ^ ε := by
  let R : ℝ := (2 : ℝ)^(1/ε)
  let U : Finset Eisenstein := (finite_norm_le R).toFinset
  have hR : 0 < R := Real.rpow_pos_of_pos (by norm_num) _
  have hRe : R^ε = 2 := by
    dsimp [R]
    rw [← Real.rpow_mul (by norm_num), div_mul_cancel₀ _ hε.ne', Real.rpow_one]
  refine ⟨(2 : ℝ)^U.card, by positivity, ?_⟩
  intro a ha hsa
  let P := primaryPrimeFactors a
  have hpoint : ∀ p ∈ P, (2 : ℝ) ≤ (if p ∈ U then 2 else 1) * norm p ^ ε := by
    intro p hp
    have hn1 := one_le_norm (primaryPrimeFactor_spec ha hp).1.2.ne_zero
    by_cases hpU : p ∈ U
    · simp only [ite_eq_left hpU]
      nlinarith [Real.one_le_rpow hn1 hε.le]
    · simp only [ite_eq_right hpU, one_mul]
      have hRp : R ≤ norm p := le_of_lt (not_le.mp (by
        intro he
        exact hpU (by simpa [U] using he)))
      rw [← hRe]
      exact Real.rpow_le_rpow hR.le hRp hε.le
  have hprod := Finset.prod_le_prod₀ (s := P) (fun _ _ => (by norm_num : (0 : ℝ) ≤ 2)) hpoint
  rw [Finset.prod_const, Finset.prod_mul_distrib] at hprod
  have hsmall : (∏ p ∈ P, if p ∈ U then (2 : ℝ) else 1) ≤ (2 : ℝ)^U.card := by
    rw [Finset.prod_ite_mem, Finset.prod_const]
    exact pow_le_pow_right₀ (by norm_num) (Finset.card_le_card (Finset.inter_subset_right))
  have heq : (∏ p ∈ P, norm p ^ ε) = norm a ^ ε := by
    rw [Real.finsetProd_rpow P norm (fun p _ => norm_nonneg p), ← norm_finset_prod]
    rw [primaryPrimeFactors_prod ha hsa]
  rw [heq] at hprod
  exact hprod.trans (mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg (norm_nonneg a) _))

theorem divisorEnergy_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein) (u : Eisenstein → ℂ) (X : ℝ),
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ X) →
      (∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖u a‖^2) ≤
        C * X^ε * ∑ a ∈ S, ‖u a‖^2 := by
  obtain ⟨C,hC,hbound⟩ := primeDivisorWeight_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro S u X hS
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  exact mul_le_mul_of_nonneg_right ((hbound a (hS a ha).1 (hS a ha).2.1).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg a) (hS a ha).2.2 hε.le) hC.le))
    (sq_nonneg _)

end CubicFirstMoment
end
end

end OAI
