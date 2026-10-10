import OAI.Analysis.Mahler.HemisphereArea
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

noncomputable section
open Set MeasureTheory Metric WithLp
namespace MahlerStokes

/-- The positive normal coordinate cancels the reciprocal-chord surface
Jacobian, giving exactly the coordinate hemisphere integral used by Stokes. -/
theorem integral_upperHemisphere {n : ℕ} (i : Fin (n+1))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ) :
    (∫ z in range (hemisphereParam i),
      (z : EuclideanSpace ℝ (Fin (n+1))) i * f z
      ∂(volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere) =
    ∫ y in coordBall n 1, f (toLp 2 (hemisphereGraph i y)) := by
  have hw : Measurable (fun y : coordBall n 1 => ENNReal.ofReal ((chord 1 (y : Fin n → ℝ))⁻¹)) := by
    apply Measurable.ennreal_ofReal
    apply Measurable.inv
    exact ((show Continuous (chord (n := n) 1) by unfold chord radiusSq; fun_prop).comp continuous_subtype_val).measurable
  rw [← (measurePreserving_hemisphereParam i).integral_comp
    (hemisphereParam_measurableEmbedding i)
    (fun z => (z : EuclideanSpace ℝ (Fin (n+1))) i * f z),
    hemisphereParameterArea, integral_withDensity_eq_integral_toReal_smul
      hw (by simp)]
  calc
    _ = ∫ y : coordBall n 1, f (toLp 2 (hemisphereGraph i y)) ∂volume.comap Subtype.val := by
      apply integral_congr_ae
      filter_upwards [] with y
      have hc := chord_pos y.property
      simp [hemisphereParam, hemisphereGraph, ENNReal.toReal_ofReal (inv_nonneg.2 hc.le),
        smul_eq_mul, hc.ne']
    _ = _ := integral_subtype_comap (measurableSet_coordBall n 1) (fun y => f (toLp 2 (hemisphereGraph i y)))

lemma coordBall_neg_preimage (n : ℕ) :
    (Neg.neg : (Fin n → ℝ) → (Fin n → ℝ)) ⁻¹' coordBall n 1 = coordBall n 1 := by
  ext y
  simp [coordBall, radiusSq]

lemma neg_hemisphereGraph {n : ℕ} (i : Fin (n+1)) (y : Fin n → ℝ) :
    -(hemisphereGraph i y) = i.insertNth (-chord 1 (-y)) (-y) := by
  apply funext
  rw [i.forall_iff_succAbove]
  constructor
  · simp [hemisphereGraph, chord, radiusSq]
  · intro j; simp [hemisphereGraph]

/-- Lower hemisphere, with the negative normal coordinate and the same
positive coordinate measure on the parameter ball. -/
theorem integral_lowerHemisphere {n : ℕ} (i : Fin (n+1))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ) :
    (∫ z in {z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 |
        (z : EuclideanSpace ℝ (Fin (n+1))) i < 0},
      (z : EuclideanSpace ℝ (Fin (n+1))) i * f z
      ∂(volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere) =
    -(∫ y in coordBall n 1, f (toLp 2 (i.insertNth (-chord 1 y) y))) := by
  let e := sphereIsometry (LinearIsometryEquiv.neg ℝ :
    EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)))
  have hp := measurePreserving_sphereIsometry
    (LinearIsometryEquiv.neg ℝ : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] _) volume volume
    (LinearIsometryEquiv.neg ℝ).measurePreserving
  have hpre : e ⁻¹' {z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 |
      (z : EuclideanSpace ℝ (Fin (n+1))) i < 0} = range (hemisphereParam i) := by
    rw [hemisphereParam_range]
    ext z
    simp [e, sphereIsometry]
  have hi := hp.setIntegral_preimage_emb e.measurableEmbedding
    (fun z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 =>
      (z : EuclideanSpace ℝ (Fin (n+1))) i * f z)
    {z | (z : EuclideanSpace ℝ (Fin (n+1))) i < 0}
  rw [hpre] at hi
  rw [← hi]
  have he : (fun z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 =>
      (e z : EuclideanSpace ℝ (Fin (n+1))) i * f (e z)) =
    (fun z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 => -((z : EuclideanSpace ℝ (Fin (n+1))) i * f (-(z : EuclideanSpace ℝ (Fin (n+1)))))) := by
    funext z
    simp [e, sphereIsometry]
  rw [he, integral_neg, integral_upperHemisphere i (fun z => f (-z))]
  congr 1
  have hnegPi : MeasurePreserving (Neg.neg : (Fin n → ℝ) → (Fin n → ℝ)) :=
    volume_preserving_pi (fun _ : Fin n =>
      (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).measurePreserving)
  have hb := hnegPi.setIntegral_preimage_emb
    (MeasurableEquiv.neg (Fin n → ℝ)).measurableEmbedding
    (fun y => f (toLp 2 (i.insertNth (-chord 1 y) y))) (coordBall n 1)
  rw [coordBall_neg_preimage] at hb
  convert! hb using 1
  apply setIntegral_congr_fun (measurableSet_coordBall n 1)
  intro y _
  dsimp only
  rw [← neg_hemisphereGraph]
  rfl

lemma integral_sphere_coordinate_of_integrable {n : ℕ} (i : Fin (n+1))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (hf : Integrable (fun z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 =>
      (z : EuclideanSpace ℝ (Fin (n+1))) i * f z)
      (volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere)
    (hp : IntegrableOn (fun y => f (toLp 2 (hemisphereGraph i y))) (coordBall n 1))
    (hm : IntegrableOn (fun y => f (toLp 2 (i.insertNth (-chord 1 y) y))) (coordBall n 1)) :
    (∫ z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1,
      (z : EuclideanSpace ℝ (Fin (n+1))) i * f z
      ∂(volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere) =
    ∫ y in coordBall n 1,
      f (toLp 2 (i.insertNth (chord 1 y) y)) - f (toLp 2 (i.insertNth (-chord 1 y) y)) := by
  have hneg : MeasurableSet {z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 |
      (z : EuclideanSpace ℝ (Fin (n+1))) i < 0} := by
    exact isOpen_lt (by fun_prop) continuous_const |>.measurableSet
  have he : (∫ z in (range (hemisphereParam i))ᶜ,
      (z : EuclideanSpace ℝ (Fin (n+1))) i * f z
      ∂(volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere) =
      ∫ z in {z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 | (z : EuclideanSpace ℝ (Fin (n+1))) i < 0},
      (z : EuclideanSpace ℝ (Fin (n+1))) i * f z
      ∂(volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere := by
    rw [← integral_indicator (measurableSet_hemisphereRange i).compl, ← integral_indicator hneg]
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : (z : EuclideanSpace ℝ (Fin (n+1))) i < 0
    · have hn : ¬0 < (z : EuclideanSpace ℝ (Fin (n+1))) i := by linarith
      simp [hemisphereParam_range, hz, hn]
    · by_cases hp : 0 < (z : EuclideanSpace ℝ (Fin (n+1))) i
      · simp [hemisphereParam_range, hp, hz]
      · have hzero : (z : EuclideanSpace ℝ (Fin (n+1))) i = 0 := by linarith
        simp [hzero]
  rw [← integral_add_compl (measurableSet_hemisphereRange i) hf, he,
    integral_upperHemisphere, integral_lowerHemisphere, ← sub_eq_add_neg, ← integral_sub hp hm]
  rfl

lemma mem_unitSphere_of_radiusSq {n : ℕ} {x : Fin n → ℝ} (hx : radiusSq x = 1) :
    (toLp 2 x : EuclideanSpace ℝ (Fin n)) ∈ sphere 0 1 := by
  simp only [mem_sphere, dist_zero_right]
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [← radiusSq_eq_euclidean_norm_sq, hx, one_pow]

/-- Continuity only on the sphere supplies every integrability premise.
The integrand may be singular at the origin. -/
theorem integral_sphere_coordinate {n : ℕ} (i : Fin (n+1))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (hf : ContinuousOn f (sphere 0 1)) :
    (∫ z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1,
      (z : EuclideanSpace ℝ (Fin (n+1))) i * f z
      ∂(volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere) =
    ∫ y in coordBall n 1,
      f (toLp 2 (i.insertNth (chord 1 y) y)) - f (toLp 2 (i.insertNth (-chord 1 y) y)) := by
  apply integral_sphere_coordinate_of_integrable i f
  · let : CompactSpace (sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) :=
      isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
    have hc : Continuous (fun z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 =>
        (z : EuclideanSpace ℝ (Fin (n+1))) i * f z) :=
      (by fun_prop : Continuous (fun z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 =>
        (z : EuclideanSpace ℝ (Fin (n+1))) i)).mul (hf.comp_continuous continuous_subtype_val (fun z => z.property))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · refine IntegrableOn.mono_set (s := coordBall n 1) (t := coordClosedBall n 1) ?_
      (fun y hy => (show radiusSq y < 1^2 from hy).le)
    apply ContinuousOn.integrableOn_compact (isCompact_coordClosedBall n 1)
    apply hf.comp ((PiLp.continuous_toLp 2 _).comp (continuous_hemisphereGraph i)).continuousOn
    intro y hy
    apply mem_unitSphere_of_radiusSq
    simpa [hemisphereGraph] using (radiusSq_boundary i 1 hy).1
  · refine IntegrableOn.mono_set (s := coordBall n 1) (t := coordClosedBall n 1) ?_
      (fun y hy => (show radiusSq y < 1^2 from hy).le)
    apply ContinuousOn.integrableOn_compact (isCompact_coordClosedBall n 1)
    apply hf.comp (show Continuous (fun y : Fin n → ℝ =>
      (toLp 2 (i.insertNth (-chord 1 y) y) : EuclideanSpace ℝ (Fin (n+1)))) by
        unfold chord radiusSq; fun_prop).continuousOn
    intro y hy
    apply mem_unitSphere_of_radiusSq
    simpa using (radiusSq_boundary i 1 hy).2

end MahlerStokes

end

end OAI
