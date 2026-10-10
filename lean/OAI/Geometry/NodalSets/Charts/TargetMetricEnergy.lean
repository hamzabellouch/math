import OAI.Geometry.NodalSets.Elliptic.TargetAmbientMeasure

namespace OAI

namespace Yau.Target
open Bundle Manifold Set MeasureTheory
open scoped ENNReal NNReal ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma smooth_projection_energy_bound (g : SmoothMetric) (P : Manifold5 → F)
    (hP : ContMDiff modelWithCorners 𝓘(ℝ,F) ∞ P) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (x : Manifold5) (v : TangentSpace modelWithCorners x),
      ‖mfderiv modelWithCorners 𝓘(ℝ,F) P x v‖^2 ≤ (C:ℝ)^2*g.inner x v v := by
  let : RiemannianBundle (fun x : Manifold5 ↦ TangentSpace modelWithCorners x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle Model
      (fun x : Manifold5 ↦ TangentSpace modelWithCorners x) :=
    ⟨g.inner, g.contMDiff.continuous, fun x v w ↦ rfl⟩
  obtain ⟨C,hpos,hC⟩ := Yau.Geometry.compact_norm_mfderiv_bound P
    (hP.of_le (by simp)) isCompact_univ
  refine ⟨C,hpos,?_⟩
  intro x v
  let L : TangentSpace modelWithCorners x →L[ℝ] F :=
    mfderiv modelWithCorners 𝓘(ℝ,F) P x
  have hnorm : ‖L‖ₑ ≤ C := hC x (mem_univ x)
  have hop : ‖L‖ ≤ (C:ℝ) := by exact_mod_cast hnorm
  have hbound : ‖mfderiv modelWithCorners 𝓘(ℝ,F) P x v‖ ≤ (C:ℝ)*‖v‖ := by
    exact (ContinuousLinearMap.le_opNorm L v).trans
      (mul_le_mul_of_nonneg_right hop (norm_nonneg v))
  have hi : g.inner x v v = ‖v‖^2 := real_inner_self_eq_norm_sq v
  rw [hi]
  nlinarith [sq_nonneg (‖mfderiv modelWithCorners 𝓘(ℝ,F) P x v‖-(C:ℝ)*‖v‖),
    mul_nonneg (sub_nonneg.mpr hbound) (add_nonneg (norm_nonneg (mfderiv modelWithCorners 𝓘(ℝ,F) P x v))
      (mul_nonneg C.coe_nonneg (norm_nonneg v)))]

variable [MeasurableSpace F] [BorelSpace F]

lemma energy_projection_nodal_measure (g : SmoothMetric) (P : Manifold5 → F)
    (hP : ContMDiff modelWithCorners 𝓘(ℝ,F) ∞ P) (C : ℝ≥0) (hpos : 0 < C)
    (hE : ∀ (x : Manifold5) (v : TangentSpace modelWithCorners x),
      ‖mfderiv modelWithCorners 𝓘(ℝ,F) P x v‖^2 ≤ (C:ℝ)^2*g.inner x v v) :
    ∀ (u : Manifold5 → ℝ) (Z : Set F), Z ⊆ P '' {x | u x = 0} →
      Measure.hausdorffMeasure (4:ℝ) Z ≤ (C : ℝ≥0∞)^4 * nodalMeasure g u := by
  let : RiemannianBundle (fun x : Manifold5 ↦ TangentSpace modelWithCorners x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle Model
      (fun x : Manifold5 ↦ TangentSpace modelWithCorners x) :=
    ⟨g.inner, g.contMDiff.continuous, fun x v w ↦ rfl⟩
  let L (x : Manifold5) : TangentSpace modelWithCorners x →L[ℝ] F :=
    mfderiv modelWithCorners 𝓘(ℝ,F) P x
  have hop (x : Manifold5) : ‖L x‖ ≤ (C:ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ C.coe_nonneg
    intro v
    have hi : g.inner x v v = ‖v‖^2 := real_inner_self_eq_norm_sq v
    have he := hE x v
    rw [hi] at he
    change ‖L x v‖^2 ≤ (C:ℝ)^2*‖v‖^2 at he
    nlinarith only [he, norm_nonneg (L x v),
      mul_nonneg C.coe_nonneg (norm_nonneg v)]
  have hC (x : Manifold5) : ‖L x‖ₑ ≤ C := by exact_mod_cast hop x
  have hd := Yau.Geometry.map_edist_le_riemannianEDist P (hP.of_le (by simp)) C hpos hC
  let : MeasurableSpace Manifold5 := borel Manifold5
  let : BorelSpace Manifold5 := ⟨rfl⟩
  let : EMetricSpace Manifold5 := EMetricSpace.ofRiemannianMetric modelWithCorners Manifold5
  let : PseudoEMetricSpace Manifold5 :=
    (EMetricSpace.ofRiemannianMetric modelWithCorners Manifold5).toPseudoEMetricSpace
  have hLip : LipschitzWith C P := hd
  intro u Z hZ
  have hh := (measure_mono hZ).trans
    (hLip.hausdorffMeasure_image_le (by norm_num : (0:ℝ) ≤ 4) {x | u x = 0})
  simpa only [show (4:ℝ) = (4:ℕ) by norm_num, ENNReal.rpow_natCast, nodalMeasure] using hh

end
end Yau.Target

end OAI
