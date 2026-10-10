import OAI.Analysis.Pureness.Stabilization.CuntzIdentities
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

namespace OAI
noncomputable section
open scoped NNReal Topology
namespace CuntzTrace
open CFC
section Unital
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma regularized_comparison (a b : A) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (C : ℝ) (hC : 0 ≤ C) (hab : a ≤ C • b) (δ : ℝ) (hδ : 0 < δ) :
    ∃ v : A, v = (b + algebraMap ℝ A δ) ^ (-(1 / 2) : ℝ) * sqrt a ∧
      ‖star v * b * v - a‖ ≤ δ * C := by
  obtain h | h := subsingleton_or_nontrivial A
  · exact ⟨0, Subsingleton.elim _ _, by simp [Subsingleton.elim a 0, mul_nonneg hδ.le hC]⟩
  let d := b + algebraMap ℝ A δ
  have hd : IsStrictlyPositive d := by
    apply IsStrictlyPositive.of_le (a := algebraMap ℝ A δ)
    · exact ⟨by simpa only [Algebra.algebraMap_eq_smul_one] using smul_nonneg hδ.le (zero_le_one : (0 : A) ≤ 1), (isUnit_iff_ne_zero.mpr hδ.ne').map (algebraMap ℝ A)⟩
    · exact le_add_of_nonneg_left hb
  let r := d ^ (-(1 / 2) : ℝ)
  have hr : 0 ≤ r := rpow_nonneg
  have hs : star (sqrt a) = sqrt a := (sqrt_nonneg a).star_eq
  have hrstar : star r = r := hr.star_eq
  have hid : r * d * r = 1 := conjugate_rpow_neg_one_half d hd
  let v := r * sqrt a
  have hvd : star v * d * v = a := by
    dsimp [v]
    rw [star_mul, hs, hrstar]
    calc
      _ = sqrt a * (r * d * r) * sqrt a := by noncomm_ring
      _ = a := by rw [hid]; simpa using sqrt_mul_sqrt_self a ha
  have hbound : v * star v ≤ C • (1 : A) := by
    dsimp [v]
    rw [star_mul, hs, hrstar]
    calc
      _ = r * a * r := by rw [mul_assoc r, ← mul_assoc (sqrt a), sqrt_mul_sqrt_self a ha, mul_assoc]
      _ ≤ r * (C • d) * r :=
        conjugate_le_conjugate_of_nonneg (hab.trans (smul_le_smul_of_nonneg_left
          (le_add_of_nonneg_right (show 0 ≤ algebraMap ℝ A δ by simpa only [Algebra.algebraMap_eq_smul_one] using smul_nonneg hδ.le (zero_le_one : (0 : A) ≤ 1))) hC)) hr
      _ = C • (1 : A) := by rw [mul_smul_comm, smul_mul_assoc, hid]
  have hnorm : ‖v‖ ^ 2 ≤ C := by
    have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg hbound (mul_star_self_nonneg v)
    simpa [CStarRing.norm_self_mul_star, norm_smul, abs_of_nonneg hC, pow_two] using hn
  refine ⟨v, rfl, ?_⟩
  have heq : star v * b * v - a = -δ • (star v * v) := by
    rw [← hvd]
    dsimp [d]
    rw [mul_add, add_mul, Algebra.algebraMap_eq_smul_one, mul_smul_comm,
      mul_one, smul_mul_assoc]
    module
  rw [heq, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hδ,
    CStarRing.norm_star_mul_self]
  exact mul_le_mul_of_nonneg_left (by simpa [pow_two] using hnorm) hδ.le
end Unital
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
open Unitization

theorem CuntzBelow.of_le_smul (a b : Positive A) (C : ℝ) (hC : 0 ≤ C)
    (hab : a.1 ≤ C • b.1) : CuntzBelow a b := by
  intro ε hε
  let δ := ε / (C + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  obtain ⟨v, hv, he⟩ := regularized_comparison (a.1 : Unitization ℂ A) (b.1 : Unitization ℂ A)
    (inr_nonneg_iff.mpr a.2) (inr_nonneg_iff.mpr b.2) C hC
    (by rw [← inr_smul]; exact inr_le_inr_iff.mpr hab) δ hδ
  have hvzero : v.fst = 0 := by rw [hv, sqrt_inr]; simp
  have hvback : (v.snd : Unitization ℂ A) = v := by
    have hi := inl_fst_add_inr_snd_eq v
    simpa [hvzero] using hi
  refine ⟨v.snd, ?_⟩
  have hn : ‖star v.snd * b.1 * v.snd - a.1‖ ≤ δ * C := by
    rw [← norm_inr (𝕜 := ℂ), inr_sub, inr_mul, inr_mul, inr_star, hvback]
    exact he
  apply hn.trans_lt
  have hd : δ * (C + 1) = ε := div_mul_cancel₀ ε (by linarith)
  nlinarith

theorem CuntzBelow.of_le (a b : Positive A) (hab : a ≤ b) : CuntzBelow a b := by
  apply CuntzBelow.of_le_smul a b 1 zero_le_one
  simpa using hab
end CuntzTrace

end

end OAI
