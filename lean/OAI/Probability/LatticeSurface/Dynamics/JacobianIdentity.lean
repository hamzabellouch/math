import Mathlib

namespace OAI

open Set MeasureTheory Filter

open scoped Topology

namespace TangentialJacobian

variable {V : Type*} [Fintype V]

lemma lipschitz_image_null {K : NNReal} {f : (V → ℝ) → (V → ℝ)}
    (hf : LipschitzWith K f) {S : Set (V → ℝ)} (hS : volume S = 0) :
    volume (f '' S) = 0 := by
  have hh := hf.hausdorffMeasure_image_le (d := (Fintype.card V : ℝ)) (by positivity) S
  rw [hausdorffMeasure_pi_real, hS, mul_zero] at hh
  exact le_antisymm hh (zero_le)

lemma lipschitz_area {K : NNReal} {f : (V → ℝ) → (V → ℝ)}
    (hf : LipschitzWith K f) {S : Set (V → ℝ)} (hS : MeasurableSet S)
    (hinj : Set.InjOn f S) :
    (∫⁻ x in S, ENNReal.ofReal |(fderiv ℝ f x).det|) = volume (f '' S) := by
  let D : Set (V → ℝ) := {x | DifferentiableAt ℝ f x}
  have hD : MeasurableSet D := measurableSet_of_differentiableAt ℝ f
  have hSD : (S ∩ D : Set (V → ℝ)) =ᵐ[volume] S := by
    filter_upwards [hf.ae_differentiableAt (μ := volume)] with x hx
    apply propext
    change (x ∈ S ∧ DifferentiableAt ℝ f x) ↔ x ∈ S
    exact and_iff_left hx
  have hn : volume (S \ (S ∩ D)) = 0 := (ae_eq_set.mp hSD).2
  have hi : f '' S =ᵐ[volume] f '' (S ∩ D) := by
    have he : f '' S = f '' (S ∩ D) ∪ f '' (S \ (S ∩ D)) := by
      rw [← Set.image_union, Set.union_sdiff_cancel (Set.inter_subset_left)]
    rw [he]
    exact union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr (lipschitz_image_null hf hn))
  rw [← setLIntegral_congr hSD, measure_congr hi]
  exact lintegral_abs_det_fderiv_eq_addHaar_image volume (hS.inter hD)
    (fun x hx => hx.2.hasFDerivAt.hasFDerivWithinAt) (hinj.mono Set.inter_subset_left)

lemma det_one_add_ne_zero (A : (V → ℝ) →L[ℝ] (V → ℝ)) (hA : ‖A‖ < 1) :
    (1 + A).det ≠ 0 := by
  have hh : IsUnit (1 + A) := by
    simpa only [norm_neg, sub_neg_eq_add] using
      (isUnit_one_sub_of_norm_lt_one (x := -A) (by simpa using hA))
  exact (LinearMap.isUnit_det _ (hh.map ContinuousLinearMap.toLinearMapRingHom)).ne_zero

lemma det_one_add_pos (A : (V → ℝ) →L[ℝ] (V → ℝ)) (hA : ‖A‖ < 1) :
    0 < (1 + A).det := by
  have hc : Continuous (fun r : ℝ => (1 + r • A).det) :=
    ContinuousLinearMap.continuous_det.comp (continuous_const.add (continuous_id.smul continuous_const))
  have h0 : (1 + (0 : ℝ) • A).det = 1 := by simp [ContinuousLinearMap.det]
  have h1 : (1 + (1 : ℝ) • A).det = (1 + A).det := by simp
  by_contra hn
  have hle : (1 + A).det ≤ 0 := le_of_not_gt hn
  obtain ⟨r, hr, hz⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1)
    hc.continuousOn (show (0 : ℝ) ∈ Set.Icc (1 + (1 : ℝ) • A).det (1 + (0 : ℝ) • A).det by
      rw [h0, h1]; exact ⟨hle, by norm_num⟩)
  apply det_one_add_ne_zero (r • A) _ hz
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr.1]
  exact (mul_le_of_le_one_left (norm_nonneg A) hr.2).trans_lt hA

lemma lipschitz_id_add_smul {u : (V → ℝ) → (V → ℝ)} {K : NNReal}
    (hu : LipschitzWith K u) (t : ℝ) :
    LipschitzWith (1 + ‖t‖₊ * K) (fun x => x + t • u x) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro x y
  change ‖(x + t • u x) - (y + t • u y)‖ ≤ (1 + |t| * K) * ‖x-y‖
  calc
    _ = ‖(x-y) + t • (u x-u y)‖ := by congr 1; module
    _ ≤ ‖x-y‖ + ‖t • (u x-u y)‖ := norm_add_le _ _
    _ = ‖x-y‖ + |t| * ‖u x-u y‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖x-y‖ + |t| * (K * ‖x-y‖) := by
      gcongr
      exact lipschitzWith_iff_norm_sub_le.mp hu x y
    _ = _ := by ring

lemma det_fderiv_positive {u : (V → ℝ) → (V → ℝ)} {K : NNReal}
    (hu : LipschitzWith K u) (t : ℝ) (ht : |t| * K < 1) (x : V → ℝ) :
    0 < (1 + t • fderiv ℝ u x).det := by
  apply det_one_add_pos
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (norm_fderiv_le_of_lipschitz ℝ hu) (abs_nonneg t)).trans_lt ht

lemma ae_fderiv_id_add_smul {u : (V → ℝ) → (V → ℝ)} {K : NNReal}
    (hu : LipschitzWith K u) (t : ℝ) :
    ∀ᵐ x ∂(volume : Measure (V → ℝ)),
      fderiv ℝ (fun x => x + t • u x) x = 1 + t • fderiv ℝ u x := by
  filter_upwards [hu.ae_differentiableAt (μ := volume)] with x hx
  exact ((hasFDerivAt_id x).add (hx.hasFDerivAt.const_smul t)).fderiv

lemma det_lintegral_of_invariant (u : (V → ℝ) → (V → ℝ)) (K : NNReal)
    (hu : LipschitzWith K u) (P : Set (V → ℝ)) (hP : MeasurableSet P)
    (t : ℝ) (ht : |t| * K < 1)
    (hinj : Set.InjOn (fun x => x + t • u x) P)
    (himage : (fun x => x + t • u x) '' P = P) :
    (∫⁻ x in P, ENNReal.ofReal ((1 + t • fderiv ℝ u x).det)) = volume P := by
  have hi := lipschitz_area (lipschitz_id_add_smul hu t) hP hinj
  rw [himage] at hi
  rw [← hi]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae (ae_fderiv_id_add_smul hu t)] with x hx
  rw [hx, abs_of_pos (det_fderiv_positive hu t ht x)]

lemma det_jacobian_measurable (u : (V → ℝ) → (V → ℝ)) (t : ℝ) :
    Measurable (fun x => (1 + t • fderiv ℝ u x).det) := by
  apply ContinuousLinearMap.continuous_det.measurable.comp
  exact measurable_const.add ((measurable_fderiv ℝ u).const_smul t)

lemma det_integral_of_invariant (u : (V → ℝ) → (V → ℝ)) (K : NNReal)
    (hu : LipschitzWith K u) (P : Set (V → ℝ)) (hP : MeasurableSet P)
    (t : ℝ) (ht : |t| * K < 1)
    (hinj : Set.InjOn (fun x => x + t • u x) P)
    (himage : (fun x => x + t • u x) '' P = P) :
    ∫ x in P, (1 + t • fderiv ℝ u x).det = (volume P).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => (det_fderiv_positive hu t ht x).le)
    (det_jacobian_measurable u t).aestronglyMeasurable,
    det_lintegral_of_invariant u K hu P hP t ht hinj himage]

end TangentialJacobian

end OAI
