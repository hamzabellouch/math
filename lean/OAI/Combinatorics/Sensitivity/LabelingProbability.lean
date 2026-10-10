import OAI.Combinatorics.Sensitivity.LabelingEvents
import OAI.Combinatorics.Sensitivity.UniformCoordinates
import OAI.Combinatorics.Sensitivity.LabelingEstimate

namespace OAI

/-! The uniform-label probability calculation and the numerical union bound. -/

noncomputable section
open scoped Classical

namespace Paper320.Tournament
variable {k r n : ℕ} [NeZero r] [NeZero n] (T : Tournament k)

theorem labelingEvent_probability (v : Fin n → Fin k) (m : Fin n → Fin r)
    (hv : Function.Injective v) :
    ((PMF.uniformOfFintype ((Fin k × Fin k) → Fin r)).toOuterMeasure
      (T.labelingEvent v m)).toReal = 1 / (r : ℝ)^(n.choose 2) := by
  have hs : (T.labelingEvent v m : Set ((Fin k × Fin k) → Fin r)) =
      {A | ∀ p ∈ T.internalEdges (Finset.univ.image v),
        A p = m (Function.invFun v p.2)} := by
    ext A
    change A ∈ T.labelingEvent v m ↔ _
    apply (T.mem_labelingEvent_iff hv).trans
    simpa only [Finset.mem_univ, forall_const, Set.mem_ofPred_eq] using
      T.labelingConstraint_iff Finset.univ v m hv A
  rw [hs, uniform_fixedCoordinates_probability, T.card_internalEdges,
    Finset.card_image_of_injective _ hv]
  simp only [Finset.card_univ, Fintype.card_fin]

theorem badLabelings_probability_le (hN : n.choose 2 ≤ k*k) :
    ((PMF.uniformOfFintype ((Fin k × Fin k) → Fin r)).toOuterMeasure
      (T.badLabelings n r)).toReal ≤ (k : ℝ)^n * (r : ℝ)^n / (r : ℝ)^(n.choose 2) := by
  have hset : Fintype.card (T.badLabelings n r : Set ((Fin k × Fin k) → Fin r)) =
      (T.badLabelings n r).card := Fintype.card_coe _
  have htotal : Fintype.card ((Fin k × Fin k) → Fin r) = r^(k*k) := by
    simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, hset, htotal]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, Nat.cast_pow]
  have hr : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  have hc : ((T.badLabelings n r).card : ℝ) ≤
      (k : ℝ)^n * (r : ℝ)^n * (r : ℝ)^(k*k-n.choose 2) := by
    exact_mod_cast T.card_badLabelings_le (n := n) (r := r)
  calc
    ((T.badLabelings n r).card : ℝ) / (r : ℝ)^(k*k) ≤
        (k : ℝ)^n * (r : ℝ)^n * (r : ℝ)^(k*k-n.choose 2) / (r : ℝ)^(k*k) :=
      div_le_div_of_nonneg_right hc (pow_nonneg hr.le _)
    _ = (k : ℝ)^n * (r : ℝ)^n / (r : ℝ)^(n.choose 2) := by
      rw [div_eq_div_iff (pow_ne_zero _ hr.ne') (pow_ne_zero _ hr.ne'),
        mul_assoc, ← pow_add, Nat.sub_add_cancel hN]

theorem bad_sixteen_probability_le (hN : 120 ≤ k*k) :
    ((PMF.uniformOfFintype ((Fin k × Fin k) → Fin r)).toOuterMeasure
      (T.badLabelings 16 r)).toReal ≤ (k : ℝ)^16 / (r : ℝ)^104 := by
  have hr : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  apply (T.badLabelings_probability_le (n := 16) hN).trans_eq
  rw [div_eq_div_iff (pow_ne_zero _ hr.ne') (pow_ne_zero _ hr.ne'),
    mul_assoc, ← pow_add]
  rfl

theorem bad_source_probability_lt_one {M : ℕ} (hM : 3 ≤ M) (hMr : M ≤ r^2)
    (S : Tournament (2*M^2+1)) :
    ((PMF.uniformOfFintype ((Fin (2*M^2+1) × Fin (2*M^2+1)) → Fin r)).toOuterMeasure
      (S.badLabelings 16 r)).toReal < 1 := by
  have h := Paper320.labeling_union_bound_real hM hMr
  apply (S.bad_sixteen_probability_le (Paper320.labeling_space_large hM)).trans_lt
  simpa only [Nat.cast_pow] using h.1.trans_lt h.2

end Paper320.Tournament

end

end OAI
