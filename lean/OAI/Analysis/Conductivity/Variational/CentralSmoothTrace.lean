import Mathlib
import OAI.Analysis.Conductivity.Sobolev.CentralPoincare
import OAI.Analysis.Conductivity.Sobolev.CentralPhysicalTrace
import OAI.Analysis.Conductivity.Variational.CentralVariational

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory UnitAddTorus
open scoped ENNReal

def normalizedTorusVolume : Measure (UnitAddTorus (Fin 2)) :=
  Measure.pi (fun _ => AddCircle.haarAddCircle)

lemma unitTorus_volume_eq_normalized : (volume : Measure (UnitAddTorus (Fin 2)))=normalizedTorusVolume := by
  change Measure.pi (fun _ : Fin 2 => (volume : Measure UnitAddCircle))=_
  simp only [unitCircle_volume_eq_haar]
  rfl

lemma central_physical_trace_normalized {f : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (i : Fin 3) :
    (∫ x : UnitAddTorus (Fin 2),(f (centralBoundary i x))^2 ∂normalizedTorusVolume)≤
      centralTraceConstant*(∫ z in centralClosed,192*cubeEnergyDensity f z+2*(f z)^2) := by
  rw [←unitTorus_volume_eq_normalized]
  exact central_physical_trace hf i

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev TorusModes := Fin 2 → ℤ

def centralTraceFunction (f : centralSmoothFunctions) (i : Fin 3) :
    C(UnitAddTorus (Fin 2),ℂ) :=
  ⟨fun x => (f (centralBoundary i x):ℂ),
    Complex.continuous_ofReal.comp ((central_smooth f).continuous.comp (continuous_centralBoundary i))⟩

def centralTraceFourier (f : centralSmoothFunctions) (i : Fin 3) : SpectralL2 TorusModes :=
  ((mFourierBasis (d:=Fin 2)).repr.restrictScalars ℝ) (ContinuousMap.toLp 2 volume ℝ (centralTraceFunction f i))

lemma centralTraceFourier_apply (f : centralSmoothFunctions) (i : Fin 3) (h : TorusModes) :
    centralTraceFourier f i h=mFourierCoeff (fun x => (f (centralBoundary i x):ℂ)) h := by
  change (mFourierBasis (d:=Fin 2)).repr (ContinuousMap.toLp 2 volume ℂ (centralTraceFunction f i)) h=_
  rw [mFourierBasis_repr,mFourierCoeff_toLp]
  rfl

lemma centralTrace_summable (s : Fin 3 → ℝ) (f : centralSmoothFunctions) (i : Fin 3) :
    Summable (fun h => torusRate s h*‖centralTraceFourier f i h‖^2) := by
  simp only [centralTraceFourier_apply]
  have hf : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y : Fin 3 → ℝ => f (sourcePairCoordinates y)) :=
    (central_smooth f).comp sourcePairCLE.contDiff
  fin_cases i
  · simpa [centralBoundary] using
      (sourceAngularTrace_summable s centralThickness hf)
  · simpa [centralBoundary,Function.comp_def] using
      (sourceAngularTrace_summable s (-centralThickness) (hf.comp (sourceChildCoordinates_contDiff 1)))
  · simpa [centralBoundary,Function.comp_def] using
      (sourceAngularTrace_summable s (-centralThickness) (hf.comp (sourceChildCoordinates_contDiff (-1))))

def centralSmoothTrace (s : Fin 3 → ℝ) (f : centralSmoothFunctions) (i : Fin 3) :
    spectralTraceGraph (torusRate s) :=
  ((spectralTraceGraph_exists_iff (fun frequency => Real.sqrt_nonneg (torusQuadratic s frequency)) (centralTraceFourier f i)).mpr
    (centralTrace_summable s f i)).choose

lemma centralSmoothTrace_fst (s : Fin 3 → ℝ) (f : centralSmoothFunctions) (i : Fin 3) :
    (centralSmoothTrace s f i).val 0=centralTraceFourier f i :=
  ((spectralTraceGraph_exists_iff (fun frequency => Real.sqrt_nonneg (torusQuadratic s frequency)) (centralTraceFourier f i)).mpr
    (centralTrace_summable s f i)).choose_spec

lemma centralTraceFunction_add (f g : centralSmoothFunctions) (i : Fin 3) :
    centralTraceFunction (f+g) i=centralTraceFunction f i+centralTraceFunction g i := by
  ext x
  exact Complex.ofReal_add _ _

lemma centralTraceFunction_smul (c : ℝ) (f : centralSmoothFunctions) (i : Fin 3) :
    centralTraceFunction (c•f) i=c•centralTraceFunction f i := by
  ext x
  exact Complex.ofReal_mul _ _

def centralSmoothTraceL (s : Fin 3 → ℝ) (i : Fin 3) :
    centralSmoothFunctions →ₗ[ℝ] spectralTraceGraph (torusRate s) where
  toFun := fun f => centralSmoothTrace s f i
  map_add' := by
    intro f g
    apply spectralTraceGraph_fst_injective
    change (centralSmoothTrace s (f+g) i).val 0=(centralSmoothTrace s f i).val 0+(centralSmoothTrace s g i).val 0
    rw [centralSmoothTrace_fst,centralSmoothTrace_fst,centralSmoothTrace_fst]
    simp only [centralTraceFourier,centralTraceFunction_add,map_add]
  map_smul' := by
    intro c f
    apply spectralTraceGraph_fst_injective
    change (centralSmoothTrace s (c•f) i).val 0=c•(centralSmoothTrace s f i).val 0
    rw [centralSmoothTrace_fst,centralSmoothTrace_fst]
    simp only [centralTraceFourier,centralTraceFunction_smul,map_smul]

lemma centralTraceFourier_norm (f : centralSmoothFunctions) (i : Fin 3) :
    ‖centralTraceFourier f i‖^2=∫ x : UnitAddTorus (Fin 2),(f (centralBoundary i x))^2 := by
  change ‖(mFourierBasis (d:=Fin 2)).repr (ContinuousMap.toLp 2 volume ℂ (centralTraceFunction f i))‖^2=_
  rw [LinearIsometryEquiv.norm_map,←real_inner_self_eq_norm_sq]
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜:=ℂ) (p:=2) volume (centralTraceFunction f i)] with x hx
  rw [hx,real_inner_self_eq_norm_sq]
  simp [centralTraceFunction,Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma centralSmoothTrace_norm (s : Fin 3 → ℝ) (f : centralSmoothFunctions) (i : Fin 3) :
    ‖centralSmoothTrace s f i‖^2=‖centralTraceFourier f i‖^2+
      ‖spectralGraphWeight (torusRate s) (centralSmoothTrace s f i)‖^2 := by
  rw [←Submodule.norm_coe,PiLp.norm_sq_eq_of_L2,Fin.sum_univ_two,centralSmoothTrace_fst]
  rfl

end

open Set MeasureTheory UnitAddTorus
open scoped ENNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def centralSmoothOne : centralSmoothFunctions := ⟨fun _ => 1,by change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun _ : Box3 => (1 : ℝ)); exact contDiff_const⟩

lemma centralOne_gradient : centralJetD (centralSmoothJet centralSmoothOne)=0 := by
  apply PiLp.ext
  intro i
  apply Lp.ext
  filter_upwards [centralSmoothJet_ae centralSmoothOne i.succ,Lp.coeFn_zero ℝ 2 centralMeasure] with z hz h0
  change centralSmoothJet centralSmoothOne i.succ z=(0 : CentralL2) z
  rw [hz,h0]
  fin_cases i <;> simp [centralJetField,centralSmoothOne,cubePartial]

lemma centralOne_traceFunction (i : Fin 3) :
    centralTraceFunction centralSmoothOne i=mFourier (0 : TorusModes) := by
  ext x
  simp [centralTraceFunction,centralSmoothOne,mFourier_zero]

lemma centralOne_fourier (i : Fin 3) :
    centralTraceFourier centralSmoothOne i=lp.single 2 (0 : TorusModes) 1 := by
  change (mFourierBasis (d:=Fin 2)).repr (ContinuousMap.toLp 2 volume ℂ
    (centralTraceFunction centralSmoothOne i))=_
  rw [centralOne_traceFunction]
  simpa only [coe_mFourierBasis] using (mFourierBasis (d:=Fin 2)).repr_self 0

lemma centralOne_weight (s : Fin 3 → ℝ) (i : Fin 3) :
    spectralGraphWeight (torusRate s) (centralSmoothTrace s centralSmoothOne i)=0 := by
  ext h
  change ((centralSmoothTrace s centralSmoothOne i).val 1) h=0
  rw [(centralSmoothTrace s centralSmoothOne i).property h,centralSmoothTrace_fst,centralOne_fourier]
  by_cases hh : h=0
  · subst h
    simp [torusRate,torusQuadratic]
  · simp [lp.single_apply,Ne.symm hh]

lemma centralOne_mean (s : Fin 3 → ℝ) (i : Fin 3) :
    spectralGraphMean (torusRate s) (centralSmoothTrace s centralSmoothOne i)=1 := by
  change (((centralSmoothTrace s centralSmoothOne i).val 0) 0).re=1
  rw [centralSmoothTrace_fst,centralOne_fourier]
  simp [lp.single_apply]

lemma centralTrace_anchor_bound (f : centralSmoothFunctions) (i : Fin 3) :
    ‖centralTraceFourier f i‖^2≤
      centralTraceConstant*(192*‖centralJetD (centralSmoothJet f)‖^2+
        2*(∫ z in centralClosed,(f z)^2)) := by
  rw [centralTraceFourier_norm]
  have hh := central_physical_trace_normalized (central_smooth f) i
  have hE : IntegrableOn (cubeEnergyDensity f) centralClosed := (continuous_cubeEnergyDensity (central_smooth f)).continuousOn.integrableOn_compact centralClosed_compact
  have hf : IntegrableOn (fun z => (f z)^2) centralClosed := ((central_smooth f).continuous.pow 2).continuousOn.integrableOn_compact centralClosed_compact
  rw [integral_add (hE.const_mul 192) (hf.const_mul 2),integral_const_mul,integral_const_mul] at hh
  rw [centralSmoothJet_gradient_norm]
  exact hh

end ScalarConductivity

end

end OAI
