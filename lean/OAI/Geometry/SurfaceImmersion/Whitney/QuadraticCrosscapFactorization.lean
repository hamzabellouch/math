import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapLinearCoordinates

namespace OAI

/-! Every nondegenerate quadratic crosscap is a standard umbrella followed
by a target map whose derivative at the origin is invertible. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
local instance tripleNormed : NormedAddCommGroup (Base × ℝ) := inferInstance
local instance tripleSpace : NormedSpace ℝ (Base × ℝ) := inferInstance

/-- Standard umbrella, with the regular coordinate placed last. -/
def standardCrosscap (x : Base) : Base × ℝ := (![x 0*x 1,(x 1)^2],x 0)

lemma standardCrosscap_smooth : ContDiff ℝ ∞ standardCrosscap := by
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [standardCrosscap] <;> fun_prop
  · change ContDiff ℝ ∞ (fun x : Base => x 0)
    fun_prop

/-- A quadratic target shear with identity differential at the origin. -/
def crosscapTargetShear (β : Base × ℝ) (z : Base × ℝ) : Base × ℝ :=
  z + z.2^2 • β

lemma crosscapTargetShear_smooth (β : Base × ℝ) :
    ContDiff ℝ ∞ (crosscapTargetShear β) := by
  exact contDiff_id.add ((contDiff_snd.pow 2).smul contDiff_const)

lemma crosscapTargetShear_fderiv (β : Base × ℝ) :
    fderiv ℝ (crosscapTargetShear β) 0 = ContinuousLinearMap.id ℝ (Base × ℝ) := by
  have h := (hasFDerivAt_id (0 : Base × ℝ)).add
    (((hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : Base × ℝ))).pow 2).smul_const β)
  have he : (id + fun z : Base × ℝ => z.2^2 • β) = crosscapTargetShear β := by
    funext z
    rfl
  rw [he] at h
  simpa using h.fderiv

lemma quadratic_crosscap_factorization {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (a : Base) (b : Bool) (t : ℝ)
    (hz : surfaceDirection f b (a,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection f b) (a,t))) :
    ∃ (R : (Base × ℝ) ≃L[ℝ] ProjectionTarget 3) (β : Base × ℝ),
      ∀ x, centeredSurfaceTaylor f a (a+crosscapSourceEquiv b t x) =
        f a + R (crosscapTargetShear β (standardCrosscap x)) := by
  let H := fderiv ℝ (surfaceDirection f b) (a,t)
  let R : (Base × ℝ) ≃L[ℝ] ProjectionTarget 3 :=
    ContinuousLinearEquiv.ofBijective (H.comp (crosscapParameterLinear b t))
      (LinearMap.ker_eq_bot.mpr (hreg.comp (crosscapParameterLinear_bijective b t)).1)
      (LinearMap.range_eq_top.mpr (hreg.comp (crosscapParameterLinear_bijective b t)).2)
  let v := tangentRayVelocity b
  let k := tangentRay b t
  let B := fderiv ℝ (fderiv ℝ f) a
  let β := R.symm ((1/2 : ℝ) • B v v)
  have hsym : B k v = B v k := hf.contDiffAt.isSymmSndFDerivAt (by simp) k v
  have hker : fderiv ℝ f a k = 0 := hz
  refine ⟨R,β,?_⟩
  intro x
  have hR : R (standardCrosscap x) =
      x 0 • fderiv ℝ f a v + (x 0*x 1) • B v k + ((x 1)^2/2) • B k k := by
    change H (crosscapParameterLinear b t (standardCrosscap x)) = _
    rw [crosscapParameterLinear_apply]
    simp only [standardCrosscap,Matrix.cons_val_zero,Matrix.cons_val_one]
    dsimp only [H]
    rw [(surfaceDirection_hasFDerivAt hf b (a,t)).fderiv]
    change fderiv ℝ f a (x 0 • v) + B ((x 0*x 1) • v + ((x 1)^2/2) • k) k = _
    simp only [map_smul,map_add,add_apply,smul_apply]
    abel
  have hβ : R β = (1/2 : ℝ) • B v v := R.apply_symm_apply _
  rw [centeredSurfaceTaylor_value]
  change f a + fderiv ℝ f a (crosscapSourceLinear b t x) +
      (1/2 : ℝ) • B (crosscapSourceLinear b t x) (crosscapSourceLinear b t x) = _
  rw [crosscapSourceLinear_apply]
  change f a + fderiv ℝ f a (x 0 • v+x 1 • k) +
      (1/2 : ℝ) • B (x 0 • v+x 1 • k) (x 0 • v+x 1 • k) = _
  simp only [map_add,map_smul,smul_apply,add_apply,hker,smul_zero,add_zero,hsym]
  rw [crosscapTargetShear,map_add,map_smul,hR,hβ]
  simp only [standardCrosscap]
  module

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
