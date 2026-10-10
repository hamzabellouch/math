import OAI.Analysis.LipschitzHilbert.Estimates.RestrictedStrongOperator

namespace OAI

/-! The scalar complex instance of the proved restricted-to-strong
estimate, transported through the one-dimensional orthonormal basis. -/
noncomputable section
open MeasureTheory Function Set
open scoped ENNReal
namespace LipschitzHilbert
variable {X : Type*} [MeasurableSpace X]

abbrev scalarCoordinate : ℂ ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 1) :=
  (OrthonormalBasis.singleton (Fin 1) ℂ).repr

def scalarLift (mu : Measure X) : Lp ℂ 2 mu →L[ℝ] HilbertLp (κ:=Fin 1) mu :=
  (scalarCoordinate.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).compLpL 2 mu

def scalarDrop (mu : Measure X) : HilbertLp (κ:=Fin 1) mu →L[ℝ] Lp ℂ 2 mu :=
  (scalarCoordinate.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).compLpL 2 mu

theorem scalarDrop_lift (mu : Measure X) (f : Lp ℂ 2 mu) : scalarDrop mu (scalarLift mu f)=f := by
  apply Lp.ext
  filter_upwards [(scalarCoordinate.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).coeFn_compLpL (scalarLift mu f),
    (scalarCoordinate.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).coeFn_compLpL f] with z hz hz'
  change (scalarDrop mu (scalarLift mu f)) z=scalarCoordinate.symm ((scalarLift mu f) z) at hz
  rw [hz]
  change (scalarLift mu f) z=scalarCoordinate (f z) at hz'
  rw [hz',scalarCoordinate.symm_apply_apply]

theorem scalarLift_norm (mu : Measure X) (f : Lp ℂ 2 mu) : ‖scalarLift mu f‖=‖f‖ := by
  rw [Lp.norm_def,Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.memLp _).aestronglyMeasurable (Lp.memLp _).aestronglyMeasurable
  filter_upwards [(scalarCoordinate.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).coeFn_compLpL f] with z hz
  change (scalarLift mu f) z=scalarCoordinate (f z) at hz
  rw [hz,scalarCoordinate.norm_map]

theorem scalarDrop_toLp (mu : Measure X) (f : X → EuclideanSpace ℂ (Fin 1)) (hf : MemLp f 2 mu) :
    scalarDrop mu (hf.toLp f)=
      ((scalarCoordinate.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp_memLp' hf).toLp
        ((scalarCoordinate.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ) ∘ f) := by
  apply Lp.ext
  filter_upwards [(scalarCoordinate.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).coeFn_compLpL (hf.toLp f),
    hf.coeFn_toLp,
    ((scalarCoordinate.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp_memLp' hf).coeFn_toLp]
    with z hz hfz hout
  change (scalarDrop mu (hf.toLp f)) z=scalarCoordinate.symm ((hf.toLp f) z) at hz
  rw [hz,hout,hfz]
  rfl

def HasScalarRestrictedLogBound (mu : Measure X)
    (B : Lp ℂ 2 mu →L[ℝ] Lp ℂ 2 mu →L[ℝ] ℂ) (C : ℝ) : Prop :=
  ∀ F G : Set X, MeasurableSet F → MeasurableSet G → mu F≠∞ → mu G≠∞ →
    0<mu.real F → 0<mu.real G →
    ∀ (u v : X → ℂ), Measurable u → Measurable v →
      (∀ x, ‖u x‖≤1) → (∀ x, ‖v x‖≤1) →
      (∀ x, x∉F → u x=0) → (∀ x, x∉G → v x=0) →
    ∀ (hu : MemLp u 2 mu) (hv : MemLp v 2 mu),
      ‖B (hu.toLp u) (hv.toLp v)‖≤C*((1+|Real.log (mu.real F/mu.real G)|)^3)⁻¹*
        Real.sqrt (mu.real F)*Real.sqrt (mu.real G)

theorem scalar_restricted_strong_norm (mu : Measure X)
    (B : Lp ℂ 2 mu →L[ℝ] Lp ℂ 2 mu →L[ℝ] ℂ)
    (C : ℝ) (hC : 0≤C) (hB : HasScalarRestrictedLogBound mu B C)
    (f g : Lp ℂ 2 mu) :
    ‖B f g‖≤4*C*restrictedStrongConstant*‖f‖*‖g‖ := by
  let B' := B.bilinearComp (scalarDrop mu) (scalarDrop mu)
  have hB' : HasRestrictedLogBound mu B' C := by
    intro F G hF hG hFfin hGfin hFpos hGpos u v hum hvm hu hv hus hvs hu2 hv2
    change ‖B (scalarDrop mu (hu2.toLp u)) (scalarDrop mu (hv2.toLp v))‖≤_
    rw [scalarDrop_toLp,scalarDrop_toLp]
    apply hB F G hF hG hFfin hGfin hFpos hGpos
    · exact scalarCoordinate.symm.continuous.measurable.comp hum
    · exact scalarCoordinate.symm.continuous.measurable.comp hvm
    · intro z
      change ‖scalarCoordinate.symm (u z)‖≤1
      simpa only [scalarCoordinate.symm.norm_map] using hu z
    · intro z
      change ‖scalarCoordinate.symm (v z)‖≤1
      simpa only [scalarCoordinate.symm.norm_map] using hv z
    · intro z hz; simp only [comp_apply,hus z hz,map_zero]
    · intro z hz; simp only [comp_apply,hvs z hz,map_zero]
  have h := restricted_strong_Lp_norm mu B' C hC hB' (scalarLift mu f) (scalarLift mu g)
  simpa only [B',ContinuousLinearMap.bilinearComp_apply,scalarDrop_lift,scalarLift_norm] using h

end LipschitzHilbert

end

end OAI
