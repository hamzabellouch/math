import OAI.Geometry.SurfaceImmersion.Geometry.PreferredNormal
import OAI.Geometry.SurfaceImmersion.Geometry.VectorPlaneRestore
import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadDifferential
import OAI.Geometry.Immersion.ClosedSurface.NormalProjection
import OAI.Geometry.SurfaceImmersion.Primitive.VelocityFrame
import OAI.Geometry.SurfaceImmersion.Geometry.C1ImmersionJets
import OAI.Geometry.Immersion.ClosedSurface.SecondForms

namespace OAI

/-! Project a global ambient field to the normal bundle using the fixed
finite atlas. No orientation or global tangent frame is chosen. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes SmallModes NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def localizedNormalField (i : A.centers) (n : M → Space) : RField 4 :=
  spaceCoordinates ∘ localize (i : M) (A.weight i) n ∘ planeCoordinateIsometry.symm

def localProjectedNormal (i : A.centers) (F n : M → Space) : RField 4 := fun x =>
  realNormalPart
    (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
    (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
    (A.localizedNormalField i n x)

lemma localizedNormalField_smooth (i : A.centers) {n : M → Space}
    (hn : ContMDiff planeModel spaceModel ∞ n) :
    ContDiff ℝ ∞ (A.localizedNormalField i n) :=
  spaceCoordinates.contDiff.comp
    ((localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hn).comp
      planeCoordinateIsometry.symm.contDiff)

omit [CompactSpace M] in
lemma localizedNormalField_support (i : A.centers) (n : M → Space) :
    tsupport (A.localizedNormalField i n) ⊆ tsupport (A.planeWeight i) := by
  apply closure_mono
  intro x hx
  contrapose! hx
  apply not_not.mpr
  have hw : A.planeWeight i x = 0 := by
    simpa only [Function.mem_support,not_not] using hx
  clear hx
  have hx := hw
  dsimp [localizedNormalField]
  by_cases hxt : planeCoordinateIsometry.symm x ∈ (chart (i : M)).target
  · simp only [planeWeight,chartWeight,Function.comp_apply,indicator_of_mem hxt] at hx
    simp [localize,hxt,hx]
  · simp [localize,hxt]

lemma localProjectedNormal_smooth (i : A.centers) {F n : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hn : ContMDiff planeModel spaceModel ∞ n)
    (hD : ∀ x ∈ tsupport (A.planeWeight i),
      gramDet (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
        (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ≠ 0) :
    ContDiff ℝ ∞ (A.localProjectedNormal i F n) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport (A.planeWeight i)
  · exact contDiffAt_realNormalPart
      (contDiff_real_coordDeriv (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)) dx).contDiffAt
      (contDiff_real_coordDeriv (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)) dy).contDiffAt
      (A.localizedNormalField_smooth i hn).contDiffAt (hD x hx)
  · have hz : A.localizedNormalField i n =ᶠ[𝓝 x] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (fun hs => hx (A.localizedNormalField_support i n hs))
    apply (contDiffAt_const (c := (0 : RVec 4))).congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    simp [localProjectedNormal,hy,realNormalPart]

def projectedNormalField (F n : M → Space) : M → Space :=
  A.vectorPlaneRestore (fun i => spaceCoordinates.symm ∘ A.localProjectedNormal i F n)

lemma projectedNormalField_smooth {F n : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hn : ContMDiff planeModel spaceModel ∞ n)
    (hD : ∀ i x, x ∈ tsupport (A.planeWeight i) →
      gramDet (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
        (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ≠ 0) :
    ContMDiff planeModel spaceModel ∞ (A.projectedNormalField F n) :=
  A.vectorPlaneRestore_smooth _ (fun i => spaceCoordinates.symm.contDiff.comp
    (A.localProjectedNormal_smooth i hF hn (hD i)))

omit [CompactSpace M] in
lemma localProjectedNormal_zero (i : A.centers) (F n : M → Space) {x : SmallModes.Base}
    (hx : A.planeWeight i x = 0) : A.localProjectedNormal i F n x = 0 := by
  have hz : A.localizedNormalField i n x = 0 := by
    dsimp [localizedNormalField]
    by_cases hxt : planeCoordinateIsometry.symm x ∈ (chart (i : M)).target
    · simp only [planeWeight,chartWeight,Function.comp_apply,indicator_of_mem hxt] at hx
      simp [localize,hxt,hx]
    · simp [localize,hxt]
  simp [localProjectedNormal,hz,realNormalPart]

lemma vectorPlaneRead_fderiv_at_weight (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {p : M} (hp : p ∈ tsupport (A.weight i)) :
    fderiv ℝ (A.vectorPlaneRead i F) (planeCoordinateIsometry (chart (i : M) p)) =
      (mfderiv planeModel spaceModel F p).comp
        ((mfderiv 𝓘(ℝ,JetPolynomial.Base) planeModel (chart (i : M)).symm
          (chart (i : M) p)).comp planeCoordinateIsometry.symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
  have hs := A.weight_support i hp
  unfold vectorPlaneRead
  rw [fderiv_comp _ ((A.vectorChartRead_smooth i hF).differentiable (by simp) _)
    planeCoordinateIsometry.symm.differentiableAt]
  simp only [LinearIsometryEquiv.symm_apply_apply,planeCoordinateIsometry.symm.fderiv]
  rw [A.vectorChartRead_fderiv i hF ⟨p,hp,rfl⟩,
    fderiv_comp_chart_symm (hF.of_le (by simp)) (i : M) ((chart (i : M)).map_source hs),
    (chart (i : M)).left_inv hs]
  rfl

lemma vectorPlaneRead_normal (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (n : M → Space)
    (hn : ∀ p v, inner ℝ (show Space from mfderiv planeModel spaceModel F p v) (n p) = 0)
    {p : M} (hp : p ∈ tsupport (A.weight i)) (u : SmallModes.Base) :
    coordDeriv u (spaceCoordinates ∘ A.vectorPlaneRead i F)
      (planeCoordinateIsometry (chart (i : M) p)) ⬝ᵥ spaceCoordinates (n p) = 0 := by
  rw [coordDeriv,fderiv_comp _ spaceCoordinates.differentiableAt
    ((A.vectorPlaneRead_smooth i hF).differentiable (by simp) _),spaceCoordinates.fderiv,
    ContinuousLinearMap.comp_apply,A.vectorPlaneRead_fderiv_at_weight i hF hp]
  change spaceCoordinates (surfaceDifferential F p _) ⬝ᵥ spaceCoordinates (n p) = 0
  rw [spaceCoordinates_dot]
  exact hn p _

lemma localProjectedNormal_normal (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (n : M → Space)
    (p : M) (hp : p ∈ tsupport (A.weight i))
    (hD : gramDet
      (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p)))
      (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p))) ≠ 0)
    (v : TangentSpace planeModel p) :
    inner ℝ (show Space from mfderiv planeModel spaceModel F p v)
      (spaceCoordinates.symm (A.localProjectedNormal i F n
        (planeCoordinateIsometry (chart (i : M) p)))) = 0 := by
  let x := planeCoordinateIsometry (chart (i : M) p)
  let u := planeCoordinateIsometry (surfaceDifferential (chart (i : M)) p v)
  have hd := congrArg (fun L : TangentSpace planeModel p →L[ℝ] Space => L v)
    (A.vectorPlaneRead_differential i hF hp)
  simp only [ContinuousLinearMap.comp_apply] at hd
  have hc := fderiv_comp x spaceCoordinates.differentiableAt
    ((A.vectorPlaneRead_smooth i hF).differentiable (by simp) x)
  have hpj := realNormalPart_perp
    (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
    (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
    (A.localizedNormalField i n x) hD
  rw [← spaceCoordinates_dot,ContinuousLinearEquiv.apply_symm_apply]
  change spaceCoordinates (surfaceDifferential F p v) ⬝ᵥ _ = 0
  rw [hd]
  change spaceCoordinates (fderiv ℝ (A.vectorPlaneRead i F) x u) ⬝ᵥ
    A.localProjectedNormal i F n x = 0
  have heval : coordDeriv u (spaceCoordinates ∘ A.vectorPlaneRead i F) x =
      spaceCoordinates (fderiv ℝ (A.vectorPlaneRead i F) x u) := by
    rw [coordDeriv,hc,spaceCoordinates.fderiv]
    rfl
  rw [← heval,coordDeriv_eq_basis]
  simp only [add_dotProduct,smul_dotProduct,localProjectedNormal,hpj.1,hpj.2,
    smul_eq_mul,mul_zero,add_zero]

lemma projectedNormalField_normal {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (n : M → Space)
    (hD : ∀ i x, x ∈ tsupport (A.planeWeight i) →
      gramDet (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
        (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ≠ 0)
    (p : M) (v : TangentSpace planeModel p) :
    inner ℝ (show Space from mfderiv planeModel spaceModel F p v) (A.projectedNormalField F n p) = 0 := by
  classical
  change inner ℝ (surfaceDifferential F p v) (A.projectedNormalField F n p) = 0
  unfold projectedNormalField vectorPlaneRestore
  rw [Finset.sum_apply,inner_sum]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hz : A.weight i p = 0
  · by_cases hs : p ∈ (chart (i : M)).source
    · have hx : A.planeWeight i (planeCoordinateIsometry (chart (i : M) p)) = 0 := by
        simp [planeWeight,chartWeight,(chart (i : M)).map_source hs,
          (chart (i : M)).left_inv hs,hz]
      simp [restore,hs,A.localProjectedNormal_zero i F n hx]
    · simp [restore,hs]
  · have hp := subset_tsupport (A.weight i) hz
    have hs := A.weight_support i hp
    have hx : planeCoordinateIsometry (chart (i : M) p) ∈ tsupport (A.planeWeight i) := by
      apply subset_tsupport
      simpa [planeWeight,chartWeight,(chart (i : M)).map_source hs,
        (chart (i : M)).left_inv hs] using hz
    simp only [restore,indicator_of_mem hs,Function.comp_apply,real_inner_smul_right]
    have hn := A.localProjectedNormal_normal i hF n p hp (hD i _ hx) v
    change inner ℝ (surfaceDifferential F p v)
      (spaceCoordinates.symm (A.localProjectedNormal i F n
        (planeCoordinateIsometry (chart (i : M) p)))) = 0 at hn
    rw [hn,mul_zero]

lemma projectedNormalField_fixed {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (n : M → Space)
    (hn : ∀ p v, inner ℝ (show Space from mfderiv planeModel spaceModel F p v) (n p) = 0) :
    A.projectedNormalField F n = n := by
  funext p
  have he (i : A.centers) :
      restore (i : M) (A.outer i)
        ((spaceCoordinates.symm ∘ A.localProjectedNormal i F n) ∘ planeCoordinateIsometry) p =
        (A.weight i p)^2 • n p := by
    by_cases hs : p ∈ (chart (i : M)).source
    · simp only [restore,indicator_of_mem hs,Function.comp_apply]
      by_cases hz : A.weight i p = 0
      · have hx : A.planeWeight i (planeCoordinateIsometry (chart (i : M) p)) = 0 := by
          simp [planeWeight,chartWeight,(chart (i : M)).map_source hs,
            (chart (i : M)).left_inv hs,hz]
        simp [A.localProjectedNormal_zero i F n hx,hz]
      · have hp := subset_tsupport (A.weight i) hz
        rw [A.outer_one i p hp,one_smul]
        have hL : A.localizedNormalField i n (planeCoordinateIsometry (chart (i : M) p)) =
            (A.weight i p)^2 • spaceCoordinates (n p) := by
          simp [localizedNormalField,localize,(chart (i : M)).map_source hs,
            (chart (i : M)).left_inv hs]
        rw [localProjectedNormal,hL,(realNormalPart_linear _ _).map_smul,
          realNormalPart_of_perp _ _ _ (A.vectorPlaneRead_normal i hF n hn hp dx)
            (A.vectorPlaneRead_normal i hF n hn hp dy),map_smul,
          ContinuousLinearEquiv.symm_apply_apply]
    · have hz : A.weight i p = 0 := image_eq_zero_of_notMem_tsupport
        (fun hp => hs (A.weight_support i hp))
      simp [restore,hs,hz]
  simp only [projectedNormalField,vectorPlaneRestore,Finset.sum_apply,he,
    ← Finset.sum_smul,A.partition,one_smul]

/-- Normalize the actual global normal projection wherever it is nonzero. -/
def projectedPreferredNormal {F n : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hn : ContMDiff planeModel spaceModel ∞ n)
    (hD : ∀ i x, x ∈ tsupport (A.planeWeight i) →
      gramDet (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
        (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ≠ 0)
    (hne : ∀ p, A.projectedNormalField F n p ≠ 0) : PreferredNormal F where
  vector p := ‖A.projectedNormalField F n p‖⁻¹ • A.projectedNormalField F n p
  smooth := by
    have hP := A.projectedNormalField_smooth hF hn hD
    intro p
    have hi := ((contDiffAt_norm ℝ (n := (∞ : ℕ∞ω)) (hne p)).inv
      (norm_ne_zero_iff.mpr (hne p))).contMDiffAt.comp p (hP p)
    exact hi.smul (hP p)
  unit p := by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hne p))]
  normal p v := by
    rw [real_inner_smul_right,A.projectedNormalField_normal hF n hD p v,mul_zero]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
