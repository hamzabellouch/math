import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TraceCone.Cuntz

namespace OAI


noncomputable section
open scoped NNReal Topology

namespace TraceCone

def squareCutMultiplier (δ : ℝ≥0) (t : ℝ) : ℝ :=
  Real.sqrt (max (t - δ) 0) / max t δ

lemma squareCutMultiplier_continuous {δ : ℝ≥0} (hδ : 0 < δ) :
    Continuous (squareCutMultiplier δ) := by
  exact (Real.continuous_sqrt.comp ((continuous_id.sub continuous_const).max continuous_const)).div
    (continuous_id.max continuous_const) (fun t => ne_of_gt
      (lt_of_lt_of_le hδ (le_max_right _ _)))

lemma squareCutMultiplier_zero (δ : ℝ≥0) : squareCutMultiplier δ 0 = 0 := by
  simp [squareCutMultiplier]

lemma squareCutMultiplier_identity {δ : ℝ≥0} (hδ : 0 < δ) (t : ℝ) :
    squareCutMultiplier δ t * (t * t) * squareCutMultiplier δ t = max (t - δ) 0 := by
  by_cases ht : t ≤ δ
  · simp [squareCutMultiplier, max_eq_right (sub_nonpos.mpr ht)]
  · have ht0 : 0 < t := lt_trans hδ (lt_of_not_ge ht)
    unfold squareCutMultiplier
    rw [max_eq_left (le_of_not_ge ht)]
    calc
      Real.sqrt (max (t - δ) 0) / t * (t * t) * (Real.sqrt (max (t - δ) 0) / t) =
          Real.sqrt (max (t - δ) 0) ^ 2 := by field_simp
      _ = _ := Real.sq_sqrt (le_max_right _ _)

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem starMul_cut_factorization (x : A) (δ : ℝ≥0) (hδ : 0 < δ) :
    ∃ v : A, star v * (x * star x) * v = (Positive.cut δ (Positive.starMul x)).1 := by
  let a := Positive.starMul x
  let f := squareCutMultiplier δ
  have hf : Continuous f := squareCutMultiplier_continuous hδ
  have hf0 : f 0 = 0 := squareCutMultiplier_zero δ
  have ha : IsSelfAdjoint a.1 := IsSelfAdjoint.of_nonneg a.2
  let g : A := cfcₙ f a.1
  have hg : star g = g := (cfcₙ_predicate f a.1).star_eq
  refine ⟨x * g, ?_⟩
  rw [star_mul, hg]
  calc
    g * star x * (x * star x) * (x * g) = g * (a.1 * a.1) * g := by
      dsimp [a, Positive.starMul]
      noncomm_ring
    _ = cfcₙ (fun t : ℝ => f t * (t * t) * f t) a.1 := by
      dsimp [g]
      rw [cfcₙ_mul (fun t : ℝ => f t * (t * t)) f a.1,
        cfcₙ_mul f (fun t : ℝ => t * t) a.1,
        cfcₙ_mul (fun t : ℝ => t) (fun t : ℝ => t) a.1, cfcₙ_id' ℝ a.1]
    _ = (Positive.cut δ a).1 := cfcₙ_congr fun t _ => squareCutMultiplier_identity hδ t

theorem starMul_cuntzBelow_mulStar (x : A) :
    CuntzBelow (Positive.starMul x) (Positive.mulStar x) := by
  apply CuntzBelow.of_cuts
  intro δ hδ η hη
  obtain ⟨v, hv⟩ := starMul_cut_factorization x δ hδ
  exact ⟨v, by simpa [Positive.mulStar, hv] using hη⟩

theorem mulStar_cuntzBelow_starMul (x : A) :
    CuntzBelow (Positive.mulStar x) (Positive.starMul x) := by
  simpa only [Positive.mulStar, Positive.starMul, star_star] using
    starMul_cuntzBelow_mulStar (star x)

theorem starMul_cuntzBelow_iff (x : A) (b : Positive A) :
    CuntzBelow (Positive.starMul x) b ↔ CuntzBelow (Positive.mulStar x) b := by
  exact ⟨fun h => (mulStar_cuntzBelow_starMul x).trans h,
    fun h => (starMul_cuntzBelow_mulStar x).trans h⟩

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
  rw [heq, norm_smul, Real.norm_eq_abs, _root_.abs_neg, abs_of_pos hδ,
    CStarRing.norm_star_mul_self]
  exact mul_le_mul_of_nonneg_left (by simpa [pow_two] using hnorm) hδ.le
end Unital
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

theorem conjugate_cuntzBelow (b : Positive A) (v : A) :
    CuntzBelow ⟨star v * b.1 * v, star_left_conjugate_nonneg b.2 v⟩ b := by
  intro η hη
  exact ⟨v, by simpa using hη⟩

theorem cut_cuntzBelow_of_norm_sub_lt (a b : Positive A) (ε : ℝ≥0) (hε : 0 < ε)
    (hab : ‖a.1 - b.1‖ < (ε : ℝ)) : CuntzBelow (Positive.cut ε a) b := by
  obtain ⟨g, hgs, hga, hgg⟩ := fixedCut_factorization a hε
  let c := Positive.cut ε a
  let d : Positive A := ⟨star g * b.1 * g, star_left_conjugate_nonneg b.2 g⟩
  let k : ℝ := ‖a.1 - b.1‖ * (ε : ℝ)⁻¹
  have hk0 : 0 ≤ k := mul_nonneg (norm_nonneg _) (inv_nonneg.mpr ε.2)
  have hk1 : k < 1 := by
    dsimp [k]
    rw [← div_eq_mul_inv]
    exact (div_lt_one (show (0 : ℝ) < ε from hε)).mpr hab
  have hcd : c.1 - d.1 ≤ k • c.1 := by
    have h := CStarAlgebra.star_left_conjugate_le_norm_smul
      (a := g) (b := a.1 - b.1)
      ((IsSelfAdjoint.of_nonneg a.2).sub (IsSelfAdjoint.of_nonneg b.2))
    rw [hgs] at h
    have heq : c.1 - d.1 = g * (a.1 - b.1) * g := by
      dsimp [c, d]
      rw [hgs, ← hga]
      noncomm_ring
    rw [heq]
    exact h.trans (by simpa only [smul_smul] using
      smul_le_smul_of_nonneg_left hgg (norm_nonneg (a.1 - b.1)))
  have hsmall : (1 - k) • c.1 ≤ d.1 := by
    rw [sub_smul, one_smul]
    exact sub_le_iff_le_add.mpr (by
      have h := sub_le_iff_le_add.mp hcd
      simpa only [add_comm] using h)
  have hdom : c.1 ≤ (1 - k)⁻¹ • d.1 := by
    have h := smul_le_smul_of_nonneg_left hsmall (inv_nonneg.mpr (by linarith : 0 ≤ 1-k))
    simpa only [smul_smul, inv_mul_cancel₀ (by linarith : 1-k ≠ 0), one_smul] using h
  exact (CuntzBelow.of_le_smul c d (1-k)⁻¹ (inv_nonneg.mpr (by linarith)) hdom).trans
    (conjugate_cuntzBelow b g)
end TraceCone
end

end OAI
