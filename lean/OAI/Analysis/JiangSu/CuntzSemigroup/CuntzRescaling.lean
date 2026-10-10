import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CuntzSemigroup.FiniteDimensionRegularization

namespace OAI

namespace Pureness
open Filter Topology

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
theorem CuntzSubequiv.smul_left {a b : A} (h : CuntzSubequiv a b)
    (t : ℝ) (ht : 0 ≤ t) : CuntzSubequiv (t • a) b := by
  obtain ⟨v, hv⟩ := (cuntzSubequiv_iff_sequence a b).mp h
  apply (cuntzSubequiv_iff_sequence _ _).mpr
  refine ⟨fun j => Real.sqrt t • v j, ?_⟩
  have hlim := hv.const_smul t
  convert hlim using 1
  ext j
  simp only [star_smul, star_trivial, smul_mul_assoc, mul_smul_comm, smul_smul,
    Real.mul_self_sqrt ht]

theorem positive_smul_cuntz_equiv (a : A) (t : ℝ) (ht : 0 < t) :
    CuntzSubequiv (t • a) a ∧ CuntzSubequiv a (t • a) := by
  constructor
  · exact (cstar_cuntzSubequiv_refl a).smul_left t ht.le
  · have h := (cstar_cuntzSubequiv_refl (t • a)).smul_left t⁻¹ (inv_nonneg.mpr ht.le)
    simpa only [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] using h

theorem exists_small_cuntz_equivalent (a : A) (ha : 0 ≤ a) (δ : ℝ) (hδ : 0 < δ) :
    ∃ b : A, 0 ≤ b ∧ ‖b‖ ≤ δ ∧ CuntzSubequiv b a ∧ CuntzSubequiv a b := by
  let t := δ / (‖a‖ + 1)
  have hden : 0 < ‖a‖ + 1 := by positivity
  have ht : 0 < t := div_pos hδ hden
  refine ⟨t • a, smul_nonneg ht.le ha, ?_, (positive_smul_cuntz_equiv a t ht).1,
    (positive_smul_cuntz_equiv a t ht).2⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have heq : t * (‖a‖ + 1) = δ := div_mul_cancel₀ δ hden.ne'
  calc
    t * ‖a‖ ≤ t * (‖a‖ + 1) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) ht.le
    _ = δ := heq

theorem exists_summable_cuntz_rescaling (a : ℕ → A) (ha : ∀ j, 0 ≤ a j) :
    ∃ b : ℕ → A, (∀ j, 0 ≤ b j ∧ ‖b j‖ ≤ (1 / 2 : ℝ) ^ j ∧
      CuntzSubequiv (b j) (a j) ∧ CuntzSubequiv (a j) (b j)) ∧ Summable b := by
  have hδ : ∀ j : ℕ, 0 < (1 / 2 : ℝ) ^ j := fun j => pow_pos (by norm_num) j
  choose b hb using fun j => exists_small_cuntz_equivalent (a j) (ha j) _ (hδ j)
  refine ⟨b, hb, ?_⟩
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun j => norm_nonneg (b j)) (fun j => (hb j).2.1)
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1))

end Pureness

noncomputable section
namespace Pureness
open TraceCone
open scoped NNReal ENNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma positive_projection_cut {D : Type*} [NonUnitalCStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D] (p : Positive D) (hp : IsIdempotentElem p.1)
    (ε : ℝ≥0) (hε : ε < 1) : (Positive.cut ε p).1 = (1-(ε : ℝ)) • p.1 := by
  change cfcₙ (fun t : ℝ => max (t-ε) 0) p.1 = _
  rw [← cfcₙ_const_mul_id (1-(ε : ℝ)) p.1]
  apply cfcₙ_congr
  intro t ht
  have hs : t = 0 ∨ t = 1 := by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hp.quasispectrum_subset ℝ ht
  rcases hs with rfl | rfl
  · simp
  · simp only [mul_one, max_eq_left (sub_nonneg.mpr (le_of_lt (show (ε : ℝ) < 1 from hε)))]

lemma finiteProjection_cut_class (n : ℕ) (p : Positive (FinMatrix A n))
    (hp : IsIdempotentElem p.1) (ε : ℝ≥0) (hε : ε < 1) :
    finitePositiveClass n (Positive.cut ε p) = finitePositiveClass n p := by
  have h := positive_smul_cuntz_equiv p.1 (1-(ε : ℝ)) (sub_pos.mpr hε)
  apply le_antisymm
  · apply (finitePositiveClass_le_iff n _ _).mpr
    rw [positive_projection_cut p hp ε hε]
    exact h.1
  · apply (finitePositiveClass_le_iff n _ _).mpr
    rw [positive_projection_cut p hp ε hε]
    exact h.2

theorem regularizedFiniteDimension_projection
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (p : Positive (FinMatrix A n)) (hp : IsIdempotentElem p.1) :
    regularizedFiniteDimension d hd (finitePositiveClass n p) = d (finitePositiveClass n p) := by
  apply le_antisymm (regularizedFiniteDimension_le d hd _)
  rw [regularizedFiniteDimension_eval]
  have h := cut_class_value_le_regularized d n p (1/2) (by norm_num)
  rwa [finiteProjection_cut_class n p hp (1/2) (by norm_num)] at h

def regularizedProjectionState (n : ℕ) (p : Positive (FinMatrix A n))
    (hp : IsIdempotentElem p.1) (f : OrderedSemigroup.StateSpace (finitePositiveClass n p)) :
    OrderedSemigroup.StateSpace (finitePositiveClass n p) := by
  let d := regularizedFiniteDimension f.toAddHom f.monotone
  refine ⟨d, d.map_zero, d.map_add, regularizedFiniteDimension_monotone f.toAddHom f.monotone, ?_⟩
  change regularizedFiniteDimension f.toAddHom f.monotone (finitePositiveClass n p) = 1
  rw [regularizedFiniteDimension_projection f.toAddHom f.monotone n p hp]
  exact f.at_unit

end Pureness
end

end OAI
