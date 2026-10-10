import OAI.Analysis.Mahler.HemisphereMeasure
import OAI.Analysis.Mahler.SphereTransport

namespace OAI

noncomputable section
open Set MeasureTheory Metric WithLp
open scoped ENNReal Pointwise
namespace MahlerStokes

lemma continuous_hemisphereGraph {n : ℕ} (i : Fin (n+1)) : Continuous (hemisphereGraph i) := by
  unfold hemisphereGraph chord radiusSq
  fun_prop

/-- The upper hemisphere parametrization into the actual Euclidean unit sphere. -/
def hemisphereParam {n : ℕ} (i : Fin (n+1)) :
    coordBall n 1 → sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 := fun y =>
  ⟨toLp 2 (hemisphereGraph i y), by
    simp only [mem_sphere, dist_zero_right]
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [← radiusSq_eq_euclidean_norm_sq, radiusSq_hemisphereGraph i y.property, one_pow]⟩

lemma continuous_hemisphereParam {n : ℕ} (i : Fin (n+1)) : Continuous (hemisphereParam i) := by
  apply continuous_induced_rng.2
  exact (PiLp.continuous_toLp 2 _).comp ((continuous_hemisphereGraph i).comp continuous_subtype_val)

lemma hemisphereParam_injective {n : ℕ} (i : Fin (n+1)) : Function.Injective (hemisphereParam i) := by
  intro y z h
  apply Subtype.ext
  funext j
  have he := congrArg (fun w : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 =>
    (w : EuclideanSpace ℝ (Fin (n+1))) (i.succAbove j)) h
  simpa [hemisphereParam, hemisphereGraph] using he

lemma hemisphereParam_range {n : ℕ} (i : Fin (n+1)) :
    range (hemisphereParam i) =
      {z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 | 0 < (z : EuclideanSpace ℝ (Fin (n+1))) i} := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    simpa [hemisphereParam, hemisphereGraph] using chord_pos y.property
  · intro hz
    let x : Fin (n+1) → ℝ := ofLp (z : EuclideanSpace ℝ (Fin (n+1)))
    have hnorm : ‖(z : EuclideanSpace ℝ (Fin (n+1)))‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using z.property
    have hr : radiusSq x = 1 := by rw [radiusSq_eq_euclidean_norm_sq]; simp [x, hnorm]
    have hs : radiusSq x = (x i)^2 + radiusSq (i.removeNth x) := by
      have he : i.insertNth (x i) (i.removeNth x) = x := by simp
      rw [← he, radiusSq_insertNth]; simp
    have hi : 0 < x i := hz
    have hy : i.removeNth x ∈ coordBall n 1 := by
      change radiusSq (i.removeNth x) < 1^2
      nlinarith
    have hc : chord 1 (i.removeNth x) = x i := by
      apply (sq_eq_sq₀ (chord_pos hy).le hi.le).1
      rw [chord_sq hy]
      linarith
    refine ⟨⟨i.removeNth x, hy⟩, ?_⟩
    apply Subtype.ext
    change toLp 2 (hemisphereGraph i (i.removeNth x)) = toLp 2 x
    congr 1
    simp [hemisphereGraph, hc]

lemma hemisphereParam_measurableEmbedding {n : ℕ} (i : Fin (n+1)) :
    MeasurableEmbedding (hemisphereParam i) := by
  let := (measurableSet_coordBall n 1).standardBorel
  exact (continuous_hemisphereParam i).measurable.measurableEmbedding (hemisphereParam_injective i)

lemma hemisphereCone_image_toLp {n : ℕ} (i : Fin (n+1)) (S : Set (Fin n → ℝ)) :
    (toLp 2 : (Fin (n+1) → ℝ) → EuclideanSpace ℝ (Fin (n+1))) ''
      (hemisphereCone i '' coneStrip i S) =
    Ioo (0 : ℝ) 1 • ((fun y => (toLp 2 (hemisphereGraph i y) : EuclideanSpace ℝ (Fin (n+1)))) '' S) := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x i, hx.1, toLp 2 (hemisphereGraph i (i.removeNth x)),
      ⟨i.removeNth x, hx.2, rfl⟩, rfl⟩
  · rintro ⟨r, hr, _, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨hemisphereCone i (i.insertNth r y), ⟨i.insertNth r y, ?_, rfl⟩, ?_⟩
    · simpa [coneStrip] using And.intro hr hy
    · simp [hemisphereCone]

lemma volume_toLp_image {n : ℕ} (S : Set (Fin n → ℝ)) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (toLp 2 '' S) = volume S := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
  have h := (PiLp.volume_preserving_toLp (Fin n)).measure_preimage_emb
    e.toHomeomorph.measurableEmbedding (e '' S)
  change volume (e ⁻¹' (e '' S)) = volume (e '' S) at h
  rw [e.injective.preimage_image] at h
  exact h.symm

/-- The hemisphere chart pushes forward exactly the reciprocal-chord area
measure. This is proved from the cone definition of volume.toSphere. -/
theorem toSphere_hemisphereParam_image {n : ℕ} (i : Fin (n+1))
    {S : Set (coordBall n 1)} (hS : MeasurableSet S) :
    (volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere (hemisphereParam i '' S) =
      ∫⁻ y in (Subtype.val '' S), ENNReal.ofReal (chord 1 y)⁻¹ := by
  have hm := (hemisphereParam_measurableEmbedding i).measurableSet_image.mpr hS
  rw [Measure.toSphere_apply' _ hm]
  have he : Subtype.val '' (hemisphereParam i '' S) =
      (fun y => (toLp 2 (hemisphereGraph i y) : EuclideanSpace ℝ (Fin (n+1)))) '' (Subtype.val '' S) := by
    rw [← image_comp, image_image]
    rfl
  rw [he, ← hemisphereCone_image_toLp, volume_toLp_image,
    volume_hemisphereCone_strip i
      ((MeasurableEmbedding.subtype_coe (measurableSet_coordBall n 1)).measurableSet_image.mpr hS)
      (by rintro y ⟨z, hz, rfl⟩; exact z.property)]
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1 := by simp
  rw [hd, ← mul_assoc]
  have hc : (↑(n+1) : ℝ≥0∞) * ENNReal.ofReal ((n+1 : ℝ)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    push_cast
    rw [mul_inv_cancel₀ (by positivity : (n : ℝ) + 1 ≠ 0)]
    simp
  rw [hc, one_mul]

/-- Actual Euclidean hemisphere area in graph coordinates. -/
def hemisphereParameterArea (n : ℕ) : Measure (coordBall n 1) :=
  (volume.comap Subtype.val).withDensity
    (fun y => ENNReal.ofReal (chord 1 (y : Fin n → ℝ))⁻¹)

lemma measurableSet_hemisphereRange {n : ℕ} (i : Fin (n+1)) :
    MeasurableSet (range (hemisphereParam i)) :=
  (hemisphereParam_measurableEmbedding i).measurableSet_range

/-- Full measure equality, sufficient for Bochner as well as nonnegative
integration. No sphere integration identity is a premise. -/
theorem measurePreserving_hemisphereParam {n : ℕ} (i : Fin (n+1)) :
    MeasurePreserving (hemisphereParam i) (hemisphereParameterArea n)
      ((volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere.restrict
        (range (hemisphereParam i))) := by
  refine ⟨(continuous_hemisphereParam i).measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (continuous_hemisphereParam i).measurable hs,
    hemisphereParameterArea, withDensity_apply _ ((continuous_hemisphereParam i).measurable hs),
    setLIntegral_subtype (measurableSet_coordBall n 1) _
      (fun y : Fin n → ℝ => ENNReal.ofReal (chord 1 y)⁻¹),
    Measure.restrict_apply hs]
  rw [← toSphere_hemisphereParam_image i ((continuous_hemisphereParam i).measurable hs),
    image_preimage_eq_inter_range]

end MahlerStokes

end

end OAI
