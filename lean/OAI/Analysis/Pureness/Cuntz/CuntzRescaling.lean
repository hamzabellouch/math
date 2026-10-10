import OAI.Analysis.Pureness.Cuntz.CStarCuntz
import Mathlib.Analysis.SpecificLimits.Normed

namespace OAI
namespace CuntzPureness
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
  nlinarith

theorem exists_summable_cuntz_rescaling (a : ℕ → A) (ha : ∀ j, 0 ≤ a j) :
    ∃ b : ℕ → A, (∀ j, 0 ≤ b j ∧ ‖b j‖ ≤ (1 / 2 : ℝ) ^ j ∧
      CuntzSubequiv (b j) (a j) ∧ CuntzSubequiv (a j) (b j)) ∧ Summable b := by
  have hδ : ∀ j : ℕ, 0 < (1 / 2 : ℝ) ^ j := fun j => pow_pos (by norm_num) j
  choose b hb using fun j => exists_small_cuntz_equivalent (a j) (ha j) _ (hδ j)
  refine ⟨b, hb, ?_⟩
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun j => norm_nonneg (b j)) (fun j => (hb j).2.1)
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1))
end CuntzPureness

end OAI
