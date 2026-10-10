import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TraceCone.AbsoluteComparison
import OAI.Analysis.JiangSu.TraceCone.RankCyclic

namespace OAI


noncomputable section
open scoped NNReal Topology

namespace TraceCone
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma abs_mul_left_cuntzBelow (b x : A) : CuntzBelow (Positive.abs (b*x)) (Positive.abs x) := by
  have h := CStarAlgebra.star_left_conjugate_le_norm_smul
    (a := x) (b := star b*b) (IsSelfAdjoint.of_nonneg (star_mul_self_nonneg b))
  have ho : (Positive.starMul (b*x)).1 ≤ ‖star b*b‖ • (Positive.starMul x).1 := by
    change star (b*x)*(b*x) ≤ ‖star b*b‖ • (star x*x)
    rw [star_mul]
    convert h using 1
    noncomm_ring
  exact (abs_cuntzBelow_starMul (b*x)).trans
    ((CuntzBelow.of_le_smul _ _ ‖star b*b‖ (norm_nonneg _) ho).trans (starMul_cuntzBelow_abs x))

lemma abs_star_cuntzBelow (x : A) : CuntzBelow (Positive.abs (star x)) (Positive.abs x) := by
  have h : CuntzBelow (Positive.starMul (star x)) (Positive.starMul x) := by
    simpa only [Positive.starMul, Positive.mulStar, star_star] using mulStar_cuntzBelow_starMul x
  exact (abs_cuntzBelow_starMul (star x)).trans (h.trans (starMul_cuntzBelow_abs x))

lemma abs_mul_right_cuntzBelow (b x : A) : CuntzBelow (Positive.abs (x*b)) (Positive.abs x) := by
  have h := abs_star_cuntzBelow (star (x*b))
  rw [star_star, star_mul] at h
  exact h.trans ((abs_mul_left_cuntzBelow (star b) (star x)).trans (abs_star_cuntzBelow x))

theorem product_cut_comparisons (b x : A) (ε : ℝ≥0) (hε : 0 < ε)
    (M : ℝ≥0) (hM : 0 < M) (hb : ‖b‖ ≤ M) :
    CuntzBelow (Positive.cut ε (Positive.abs (b*x)))
      (Positive.cut (ε/(2*M)) (Positive.abs x)) ∧
    CuntzBelow (Positive.cut ε (Positive.abs (x*b)))
      (Positive.cut (ε/(2*M)) (Positive.abs x)) := by
  let δ := ε/(2*M)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨z, hz, haz⟩ := exists_cut_truncation x δ hδ
  have hbound : (M : ℝ)*(δ : ℝ) < ε := by
    dsimp [δ]
    have he : (M : ℝ)*(ε / (2*M) : ℝ) = (ε : ℝ)/2 := by
      rw [← mul_div_assoc, mul_comm (2 : ℝ),
        mul_div_mul_left _ _ (ne_of_gt (show (0 : ℝ) < M from hM))]
    rw [he]
    exact half_lt_self hε
  have hl : ‖b*x-b*z‖ < ε := by
    rw [← mul_sub]
    exact (norm_mul_le _ _).trans_lt ((mul_le_mul hb hz (norm_nonneg _) M.2).trans_lt hbound)
  have hr : ‖x*b-z*b‖ < ε := by
    rw [← sub_mul]
    exact (norm_mul_le _ _).trans_lt ((mul_le_mul hz hb (norm_nonneg _) δ.2).trans_lt
      (by simpa only [mul_comm] using hbound))
  constructor
  · simpa only [haz] using (abs_cut_cuntzBelow_of_norm_sub_lt (b*x) (b*z) ε hε hl).trans
      (abs_mul_left_cuntzBelow b z)
  · simpa only [haz] using (abs_cut_cuntzBelow_of_norm_sub_lt (x*b) (z*b) ε hε hr).trans
      (abs_mul_right_cuntzBelow b z)

theorem perturbation_cut_comparison (x y : A) (ε : ℝ≥0) (hε : 0 < ε)
    (hxy : ‖x-y‖ < (ε : ℝ)/4) :
    CuntzBelow (Positive.cut ε (Positive.abs x)) (Positive.cut (ε/2) (Positive.abs y)) := by
  obtain ⟨z, hz, haz⟩ := exists_cut_truncation y (ε/2) (by positivity)
  have h : ‖x-z‖ < ε := by
    have ht : ‖x-z‖ ≤ ‖x-y‖ + ‖y-z‖ := norm_sub_le_norm_sub_add_norm_sub x y z
    have hz' : ‖y-z‖ ≤ (ε : ℝ)/2 := by exact_mod_cast hz
    linarith [show (0 : ℝ) < ε from hε]
  simpa only [haz] using abs_cut_cuntzBelow_of_norm_sub_lt x z ε hε h

theorem product_cut_ranks (τ : ExtendedTrace A) (b x : A) (ε : ℝ≥0) (hε : 0 < ε)
    (M : ℝ≥0) (hM : 0 < M) (hb : ‖b‖ ≤ M) :
    τ.rank (Positive.cut ε (Positive.abs (b*x))) ≤ τ.rank (Positive.cut (ε/(2*M)) (Positive.abs x)) ∧
    τ.rank (Positive.cut ε (Positive.abs (x*b))) ≤ τ.rank (Positive.cut (ε/(2*M)) (Positive.abs x)) := by
  obtain ⟨hl, hr⟩ := product_cut_comparisons b x ε hε M hM hb
  exact ⟨τ.rank_le_of_cuntzBelow hl, τ.rank_le_of_cuntzBelow hr⟩

theorem adjoint_cut_comparison (x : A) (ε : ℝ≥0) (hε : 0 < ε) :
    CuntzBelow (Positive.cut ε (Positive.abs (star x))) (Positive.cut ε (Positive.abs x)) := by
  obtain ⟨z, hz, haz⟩ := exists_cut_truncation x ε hε
  apply CuntzBelow.of_cuts
  intro δ hδ
  rw [Positive.cut_cut, add_comm ε δ]
  have hn : ‖star x-star z‖ < ((δ+ε : ℝ≥0) : ℝ) := by
    rw [← star_sub, norm_star]
    exact hz.trans_lt (by exact_mod_cast lt_add_of_pos_left ε hδ)
  have h := (abs_cut_cuntzBelow_of_norm_sub_lt (star x) (star z) (δ+ε) (by positivity) hn).trans
    (abs_star_cuntzBelow z)
  simpa only [haz] using h

theorem adjoint_cut_ranks (τ : ExtendedTrace A) (x : A) (ε : ℝ≥0) (hε : 0 < ε) :
    τ.rank (Positive.cut ε (Positive.abs (star x))) = τ.rank (Positive.cut ε (Positive.abs x)) := by
  apply τ.rank_eq_of_cuntzEquivalent (adjoint_cut_comparison x ε hε)
  simpa only [star_star] using adjoint_cut_comparison (star x) ε hε
end TraceCone

end


noncomputable section
open scoped ENNReal

namespace TraceCone

theorem ennreal_add_self_eq_iff (r : ℝ≥0∞) : r + r = r ↔ r = 0 ∨ r = ∞ := by
  constructor
  · intro h
    by_cases ht : r = ∞
    · exact Or.inr ht
    · left
      by_contra hz
      exact (ENNReal.lt_add_right ht hz).ne h.symm
  · rintro (rfl | rfl) <;> simp

def idealIndicator {α : Type*} (I : Set α) (a : α) : ℝ≥0∞ :=
  @ite _ (a ∈ I) (Classical.propDecidable _) 0 ∞

@[simp] theorem idealIndicator_eq_zero {α : Type*} (I : Set α) (a : α) :
    idealIndicator I a = 0 ↔ a ∈ I := by
  classical
  simp [idealIndicator]

theorem idealIndicator_add_eq_iff {α : Type*} (I J : Set α) :
    (fun a => idealIndicator I a + idealIndicator J a) = idealIndicator I ↔ I ⊆ J := by
  classical
  constructor
  · intro h a ha
    have := congrFun h a
    simpa [idealIndicator, ha] using this
  · intro h
    funext a
    by_cases ha : a ∈ I
    · simp [idealIndicator, ha, h ha]
    · simp [idealIndicator, ha]

theorem idempotent_function_iff_indicator {α : Type*} (f : α → ℝ≥0∞) :
    (∀ a, f a + f a = f a) ↔ f = idealIndicator {a | f a = 0} := by
  classical
  constructor
  · intro h
    funext a
    rcases (ennreal_add_self_eq_iff (f a)).mp (h a) with hz | ht
    · simp [idealIndicator, hz]
    · simp [idealIndicator, ht]
  · intro h a
    rw [h]
    simp only [idealIndicator]
    split <;> simp

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace ExtendedTrace

theorem isClosed_zeroSet (τ : ExtendedTrace A) : IsClosed {a | τ a = 0} := by
  simpa only [Set.preimage, Set.mem_Iic, nonpos_iff_eq_zero] using
    τ.lowerSemicontinuous.isClosed_preimage 0

theorem idempotent_iff_zero_or_top (τ : ExtendedTrace A) :
    (∀ a, τ a + τ a = τ a) ↔ ∀ a, τ a = 0 ∨ τ a = ∞ := by
  simp only [ennreal_add_self_eq_iff]

theorem idempotent_eq_indicator (τ : ExtendedTrace A)
    (h : ∀ a, τ a + τ a = τ a) :
    (fun a => τ a) = idealIndicator {a | τ a = 0} :=
  (idempotent_function_iff_indicator _).mp h

end ExtendedTrace
end TraceCone
end


noncomputable section
open scoped ENNReal NNReal

namespace TraceCone

theorem lowerSemicontinuous_idealIndicator {α : Type*} [TopologicalSpace α]
    {I : Set α} (hI : IsClosed I) : LowerSemicontinuous (idealIndicator I) := by
  classical
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro r
  by_cases hr : r = ∞
  · subst r
    simp
  · have heq : idealIndicator I ⁻¹' Set.Iic r = I := by
      ext a
      simp only [Set.mem_preimage, Set.mem_Iic, idealIndicator]
      by_cases ha : a ∈ I <;> simp [ha, top_le_iff, hr]
    rw [heq]
    exact hI

variable (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def zeroIdealWeight : ExtendedTrace A where
  toFun := idealIndicator {a : Positive A | a.1 = 0}
  map_zero := by simp [idealIndicator, Positive.zero]
  map_add a b := by
    classical
    have hz : a.1 + b.1 = 0 ↔ a.1 = 0 ∧ b.1 = 0 :=
      add_eq_zero_iff_of_nonneg a.2 b.2
    change (if a.1 + b.1 = 0 then (0 : ℝ≥0∞) else ∞) =
      (if a.1 = 0 then 0 else ∞) + (if b.1 = 0 then 0 else ∞)
    by_cases ha : a.1 = 0 <;> by_cases hb : b.1 = 0 <;> simp [hz, ha, hb]
  map_smul r a := by
    classical
    by_cases hr : r = 0
    · subst r
      simp [idealIndicator, Positive.smul]
    · have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
      by_cases ha : a.1 = 0
      · simp [idealIndicator, Positive.smul, ha]
      · simp [idealIndicator, Positive.smul, ha, hr, hr']
  tracial x := by
    classical
    change (if star x * x = 0 then (0 : ℝ≥0∞) else ∞) =
      (if x * star x = 0 then 0 else ∞)
    rw [CStarRing.star_mul_self_eq_zero_iff, CStarRing.mul_star_self_eq_zero_iff]
  lowerSemicontinuous := lowerSemicontinuous_idealIndicator
    (isClosed_eq continuous_subtype_val continuous_const)

@[simp] theorem zeroIdealWeight_eq_zero (a : Positive A) :
    zeroIdealWeight A a = 0 ↔ a.1 = 0 := by
  exact idealIndicator_eq_zero _ _

theorem zeroIdealWeight_lt_top (a : Positive A) :
    zeroIdealWeight A a < ∞ ↔ a.1 = 0 := by
  classical
  change idealIndicator _ a < ∞ ↔ _
  by_cases ha : a.1 = 0 <;> simp [idealIndicator, ha]

theorem zeroIdealWeight_detects (x : A) (hx : x ≠ 0) :
    zeroIdealWeight A (Positive.starMul x) = ∞ := by
  classical
  change idealIndicator _ _ = ∞
  simp [idealIndicator, Positive.starMul, CStarRing.star_mul_self_eq_zero_iff, hx]

end TraceCone
end

end OAI
