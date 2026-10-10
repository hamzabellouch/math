import OAI.Analysis.WeakInfiniteness.CentralizationEstimates

namespace OAI

/-! The multiplicative-domain calculation in KR02 Lemma 7.9.  Preserving
an element and its square by a contractive compression forces the relative
commutation and initial-support identities. -/

noncomputable section

namespace WeakPureInfiniteness

variable {A : Type*} [NonUnitalCStarAlgebra A]

theorem relative_relations_of_fixed_compression (v a : A) (hv : ‖v‖ ≤ 1)
    (ha : star v * a * v = a)
    (ha2 : star v * (star a * a) * v = star a * a) :
    a * v = v * a ∧ (star v * v) * a = a := by
  have hcomm : a * v = v * a := by
    have h := norm_commutator_sq_le v a hv
    simp only [ha, ha2, sub_self, norm_zero, mul_zero, add_zero] at h
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (a * v - v * a)]
  refine ⟨hcomm, ?_⟩
  have h := norm_relative_initial_defect_le v a hv
  simp only [hcomm, ha, sub_self, norm_zero, zero_add] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

theorem fixed_compression_of_relative_relations (v a : A)
    (hcomm : a * v = v * a) (hinit : (star v * v) * a = a) :
    star v * a * v = a := by
  calc
    _ = star v * (a * v) := mul_assoc _ _ _
    _ = star v * (v * a) := by rw [hcomm]
    _ = a := by rw [← mul_assoc, hinit]

theorem selfAdjoint_fixed_compression_iff (v a : A) (hv : ‖v‖ ≤ 1)
    (ha : IsSelfAdjoint a) :
    (star v * a * v = a ∧ star v * (a * a) * v = a * a) ↔
      (a * v = v * a ∧ (star v * v) * a = a) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact relative_relations_of_fixed_compression v a hv h1
      (by simpa only [ha.star_eq] using h2)
  · rintro ⟨hcomm, hinit⟩
    refine ⟨fixed_compression_of_relative_relations v a hcomm hinit, ?_⟩
    have hcomm2 : (a * a) * v = v * (a * a) := by
      calc
        _ = a * (a * v) := mul_assoc _ _ _
        _ = a * (v * a) := by rw [hcomm]
        _ = (a * v) * a := (mul_assoc _ _ _).symm
        _ = (v * a) * a := by rw [hcomm]
        _ = _ := mul_assoc _ _ _
    have hinit2 : (star v * v) * (a * a) = a * a := by
      rw [← mul_assoc, hinit]
    exact fixed_compression_of_relative_relations v (a * a) hcomm2 hinit2

end WeakPureInfiniteness

end

end OAI
