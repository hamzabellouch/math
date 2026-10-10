import OAI.Geometry.Immersion.ClosedSurface.PhaseMean
import OAI.Geometry.Immersion.ClosedSurface.ChartModel

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes Set Bundle Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

def coordinateInverse (p : M) : Base → M :=
  (extChartAt planeModel p).symm ∘ planeCoordinates.symm

lemma coordinateInverse_smoothOn (p : M) :
    ContMDiffOn 𝓘(ℝ, Base) planeModel ∞ (coordinateInverse p) (coordinateDomain p) := by
  exact (contMDiffOn_extChartAt_symm (I := planeModel) (n := (∞ : ℕ∞ω)) p).comp
    planeCoordinates.symm.contDiff.contMDiff.contMDiffOn (fun x hx => hx)

omit [IsManifold planeModel ∞ M] in
lemma coordinateInverse_center (p : M) : coordinateInverse p (coordinateCenter p) = p := by
  simp [coordinateInverse, coordinateCenter]

def metricPullback (g : SmoothMetric M) (φ : Base → M) (x v w : Base) : ℝ :=
  g.inner (φ x) (mfderiv 𝓘(ℝ, Base) planeModel φ x v)
    (mfderiv 𝓘(ℝ, Base) planeModel φ x w)

lemma metricPullback_continuousOn (g : SmoothMetric M) {φ : Base → M} {O : Set Base}
    (hO : IsOpen O) (hφ : ContMDiffOn 𝓘(ℝ, Base) planeModel ∞ φ O) (v w : Base) :
    ContinuousOn (fun x => metricPullback g φ x v w) O := by
  let : RiemannianBundle (fun p : M => TangentSpace planeModel p) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle Plane (fun p : M => TangentSpace planeModel p) :=
    ⟨⟨g.inner,g.contMDiff.continuous,fun _ _ _ => rfl⟩⟩
  have htm := hφ.continuousOn_tangentMapWithin (by simp) hO.uniqueMDiffOn
  have hs (v : Base) : Continuous (fun x : Base =>
      (⟨x,v⟩ : TangentBundle 𝓘(ℝ, Base) Base)) := by
    exact (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, Base)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hv (v : Base) : ContinuousOn (fun x : Base =>
      (⟨φ x,mfderiv 𝓘(ℝ, Base) planeModel φ x v⟩ : TangentBundle planeModel M)) O := by
    have hh := htm.comp (hs v).continuousOn (fun x hx => hx)
    apply hh.congr
    intro x hx
    simp only [Function.comp_apply, tangentMapWithin]
    rw [mfderivWithin_of_mem_nhds (hO.mem_nhds hx)]
  exact (hv v).inner_bundle (hv w)

lemma metricPullback_pos (g : SmoothMetric M) {φ : Base → M} {x : Base}
    (hi : Function.Injective (mfderiv 𝓘(ℝ, Base) planeModel φ x)) {v : Base} (hv : v ≠ 0) :
    0 < metricPullback g φ x v v := by
  apply g.pos
  intro hz
  apply hv
  apply hi
  exact hz.trans (map_zero _).symm

lemma mfderiv_coordinateInverse_center (p : M) :
    mfderiv 𝓘(ℝ, Base) planeModel (coordinateInverse p) (coordinateCenter p) =
      planeCoordinates.symm.toContinuousLinearMap := by
  have hcenter : planeCoordinates.symm (coordinateCenter p) = extChartAt planeModel p p := by
    simp [coordinateCenter]
  have hchart : MDifferentiableAt 𝓘(ℝ, Plane) planeModel
      (extChartAt planeModel p).symm (planeCoordinates.symm (coordinateCenter p)) := by
    rw [hcenter]
    simpa [planeModel, mdifferentiableWithinAt_univ] using
      (contMDiffWithinAt_extChartAt_symm_range_self (I := planeModel)
        (n := (∞ : ℕ∞ω)) p).mdifferentiableWithinAt (by simp)
  rw [coordinateInverse, mfderiv_comp _ hchart
    ((planeCoordinates.symm.contDiff (n := (∞ : ℕ∞ω))).contMDiff.mdifferentiable (by simp)).mdifferentiableAt]
  rw [hcenter]
  have hid : mfderiv 𝓘(ℝ, Plane) planeModel (extChartAt planeModel p).symm
      (extChartAt planeModel p p) = ContinuousLinearMap.id ℝ Plane := by
    simpa [planeModel] using! mfderivWithin_range_extChartAt_symm (I := planeModel) (x := p)
  rw [hid]
  ext v
  change mfderiv 𝓘(ℝ, Base) 𝓘(ℝ, Plane) planeCoordinates.symm (coordinateCenter p) v =
    planeCoordinates.symm v
  rw [mfderiv_eq_fderiv, planeCoordinates.symm.fderiv]
  rfl

def coordinateMetric (g : SmoothMetric M) (p : M) (x : Base) : PhaseMean.Tensor :=
  fun i => metricPullback g (coordinateInverse p) x
    (PhaseMean.firstDirection i) (PhaseMean.secondDirection i)

lemma coordinateMetric_continuousAt_center (g : SmoothMetric M) (p : M) :
    ContinuousAt (coordinateMetric g p) (coordinateCenter p) := by
  apply continuousAt_pi.mpr
  intro i
  exact (metricPullback_continuousOn g (coordinateDomain_open p)
    (coordinateInverse_smoothOn p) _ _).continuousAt
      ((coordinateDomain_open p).mem_nhds (coordinateCenter_mem p))

lemma coordinateMetric_evaluate (g : SmoothMetric M) (p : M) (x v w : Base) :
    PhaseMean.evaluate (coordinateMetric g p x) v w =
      metricPullback g (coordinateInverse p) x v w := by
  let D : Base →L[ℝ] TangentSpace planeModel (coordinateInverse p x) :=
    mfderiv 𝓘(ℝ, Base) planeModel (coordinateInverse p) x
  change PhaseMean.evaluate (fun i => g.inner (coordinateInverse p x)
      (D (PhaseMean.firstDirection i)) (D (PhaseMean.secondDirection i))) v w =
    g.inner (coordinateInverse p x) (D v) (D w)
  have he (v : Base) : v = v.1 • dx + v.2 • dy := by
    ext <;> simp [dx,dy]
  conv_rhs => rw [he v, he w]
  simp only [PhaseMean.evaluate,
    PhaseMean.firstDirection, PhaseMean.secondDirection, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecTail, Matrix.vecHead, Function.comp_apply,
    map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul]
  rw [g.symm _
    (D dy) (D dx)]
  dsimp
  ring

lemma tensor_positive_iff (H : PhaseMean.Tensor) :
    (∀ v : Base, v ≠ 0 → 0 < PhaseMean.evaluate H v v) ↔
      0 < H 0 ∧ 0 < H 0 * H 2 - (H 1)^2 := by
  constructor
  · intro h
    have h₀ : 0 < H 0 := by
      simpa [PhaseMean.evaluate] using h (1, 0) (by simp)
    have hv : (-H 1, H 0) ≠ (0 : Base) := by
      intro he
      have he' := congrArg Prod.snd he
      exact h₀.ne' he'
    have hh := h (-H 1, H 0) hv
    have he : PhaseMean.evaluate H (-H 1, H 0) (-H 1, H 0) = H 0 * (H 0 * H 2 - (H 1)^2) := by
      simp only [PhaseMean.evaluate]
      ring
    rw [he] at hh
    exact ⟨h₀, (mul_pos_iff_of_pos_left h₀).mp hh⟩
  · rintro ⟨h₀, hd⟩ v hv
    have he : H 0 * PhaseMean.evaluate H v v =
        (H 0 * v.1 + H 1 * v.2)^2 + (H 0 * H 2 - (H 1)^2) * v.2^2 := by
      simp only [PhaseMean.evaluate]
      ring
    apply (mul_pos_iff_of_pos_left h₀).mp
    rw [he]
    by_cases hv₂ : v.2 = 0
    · have hv₁ : v.1 ≠ 0 := by
        intro hz
        apply hv
        exact Prod.ext hz hv₂
      simp only [hv₂, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0)]
      exact sq_pos_of_ne_zero (mul_ne_zero h₀.ne' hv₁)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _)
        (mul_pos hd (sq_pos_of_ne_zero hv₂))


lemma coordinateMetric_positive_center (g : SmoothMetric M) (p : M) :
    0 < coordinateMetric g p (coordinateCenter p) 0 ∧
    0 < coordinateMetric g p (coordinateCenter p) 0 *
      coordinateMetric g p (coordinateCenter p) 2 -
      (coordinateMetric g p (coordinateCenter p) 1)^2 := by
  apply (tensor_positive_iff _).mp
  intro v hv
  rw [coordinateMetric_evaluate]
  apply metricPullback_pos g _ hv
  rw [mfderiv_coordinateInverse_center]
  exact planeCoordinates.symm.injective

end ClosedSurfaceR4

end

end OAI
