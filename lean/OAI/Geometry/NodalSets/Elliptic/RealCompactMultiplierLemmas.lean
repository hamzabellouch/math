import OAI.Geometry.NodalSets.Elliptic.RealCompactL2

namespace OAI

noncomputable section

namespace Yau

open MeasureTheory Set

theorem real_compact_multiplier_bound {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (a : (Fin n → ℝ) → ℝ) (ha : Continuous a) :
    ∃ C > 0, ∀ u : (Fin n → ℝ) → ℝ, MemLp u 2 (volume.restrict K) →
      MemLp (fun x ↦ a x*u x) 2 (volume.restrict K) ∧
      (∫ x in K, (a x*u x)^2) ≤ C*(∫ x in K, (u x)^2) := by
  obtain ⟨B,hB,hb⟩ := (hK.image ha).isBounded.exists_pos_norm_le
  refine ⟨B^2,sq_pos_of_pos hB,?_⟩
  intro u hu
  have hmul : MemLp (fun x ↦ a x*u x) 2 (volume.restrict K) :=
    hu.of_le_mul (ha.aestronglyMeasurable.mul hu.aestronglyMeasurable) (by
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hb _ ⟨x,hx,rfl⟩) (norm_nonneg _))
  refine ⟨hmul,?_⟩
  calc
    _ ≤ ∫ x in K, B^2*(u x)^2 := by
      apply setIntegral_mono_on hmul.integrable_sq (hu.integrable_sq.const_mul _) hK.measurableSet
      intro x hx
      have hab : (a x)^2 ≤ B^2 := by
        have h := hb _ ⟨x,hx,rfl⟩
        rw [Real.norm_eq_abs] at h
        nlinarith [sq_abs (a x),abs_nonneg (a x)]
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right hab (sq_nonneg _)
    _ = _ := integral_const_mul _ _

theorem real_L2_test_pairing {X : Type*} [MeasurableSpace X] {m : Measure X}
    (f : Lp ℝ 2 m) (g : X → ℝ) (hg : MemLp g 2 m) :
    Integrable (fun x ↦ f x*g x) m ∧
    inner ℝ f (hg.toLp g) = ∫ x, f x*g x ∂m := by
  have he : (fun x ↦ inner ℝ (f x) (hg.toLp g x)) =ᵐ[m] (fun x ↦ f x*g x) := by
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx]
    change g x*f x = f x*g x
    ring
  exact ⟨(L2.integrable_inner f (hg.toLp g)).congr he,by rw [L2.inner_def,integral_congr_ae he]⟩

theorem real_toLp_inner {X : Type*} [MeasurableSpace X] {m : Measure X}
    (f g : X → ℝ) (hf : MemLp f 2 m) (hg : MemLp g 2 m) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x*g x ∂m := by
  rw [(real_L2_test_pairing _ g hg).2]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

theorem real_Lp_restricted_square_le {X : Type*} [MeasurableSpace X]
    {mu nu : Measure X} (hmeasure : mu ≤ nu) (u : Lp ℝ 2 nu) :
    MemLp (u : X → ℝ) 2 mu ∧ (∫ x, (u x)^2 ∂mu) ≤ ‖u‖^2 := by
  refine ⟨(Lp.memLp u).mono_measure hmeasure,?_⟩
  have hnorm : ‖u‖^2=∫ x, (u x)^2 ∂nu := by
    simpa only [Lp.toLp_coeFn] using real_toLp_norm_sq _ (Lp.memLp u)
  rw [hnorm]
  exact integral_mono_measure hmeasure (Filter.Eventually.of_forall (fun x ↦ sq_nonneg (u x)))
    (Lp.memLp u).integrable_sq

end Yau

end

end OAI
