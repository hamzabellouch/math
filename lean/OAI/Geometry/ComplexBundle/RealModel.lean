import OAI.Geometry.ComplexBundle.DirectSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic

namespace OAI

noncomputable section

/-! Real models of complex bundles and smooth finite line sums. -/

section
open Bundle Topology
open scoped Manifold ContDiff
namespace Kaplansky

section
variable {B F J : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℂ F] (C : VectorBundleCore ℂ B F J)

/-- Restrict scalars while retaining the original complex transition maps
as functions, and hence the original bundle atlas and topology. -/
def complexCoreReal : VectorBundleCore ℝ B F J where
  baseSet := C.baseSet
  isOpen_baseSet := C.isOpen_baseSet
  indexAt := C.indexAt
  mem_baseSet_at := C.mem_baseSet_at
  coordChange i j x := (C.coordChange i j x).restrictScalars ℝ
  coordChange_self := C.coordChange_self
  continuousOn_coordChange i j :=
    (ContinuousLinearMap.restrictScalarsL ℂ F F ℝ ℝ).continuous.comp_continuousOn
      (C.continuousOn_coordChange i j)
  coordChange_comp := C.coordChange_comp

theorem complexCoreReal_toFiberBundleCore : (complexCoreReal C).toFiberBundleCore = C.toFiberBundleCore := rfl

instance complexCoreFiberRealModule (x : B) : Module ℝ (C.Fiber x) := inferInstanceAs (Module ℝ F)

instance complexCoreRealFiberComplexModule (x : B) : Module ℂ ((complexCoreReal C).Fiber x) :=
  inferInstanceAs (Module ℂ F)

instance complexCoreFiberRealVectorBundle : VectorBundle ℝ F C.Fiber :=
  inferInstanceAs (VectorBundle ℝ F (complexCoreReal C).Fiber)

instance complexCoreRealFiberComplexVectorBundle : VectorBundle ℂ F (complexCoreReal C).Fiber :=
  inferInstanceAs (VectorBundle ℂ F C.Fiber)

/-- Real-smooth complex transition functions produce an ordinary real-smooth
complex bundle, with no separate realization or atlas-compatibility assumption. -/
theorem complexCoreReal_isContMDiff
    {X H : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [TopologicalSpace H]
    (I : ModelWithCorners ℝ X H) [ChartedSpace H B]
    (hC : ∀ a b, ContMDiffOn I 𝓘(ℝ,F →L[ℂ] F) ∞ (C.coordChange a b)
      (C.baseSet a ∩ C.baseSet b)) : (complexCoreReal C).IsContMDiff I ∞ where
  contMDiffOn_coordChange a b := by
    intro x hx
    exact (ContinuousLinearMap.restrictScalarsL ℂ F F ℝ ℝ).contDiff.contDiffAt.contMDiffAt.comp_contMDiffWithinAt x
      (hC a b x hx)

theorem complexCore_contMDiffVectorBundle
    {X H : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [TopologicalSpace H]
    (I : ModelWithCorners ℝ X H) [ChartedSpace H B]
    (hC : ∀ a b, ContMDiffOn I 𝓘(ℝ,F →L[ℂ] F) ∞ (C.coordChange a b)
      (C.baseSet a ∩ C.baseSet b)) : ContMDiffVectorBundle ∞ F C.Fiber I := by
  let : (complexCoreReal C).IsContMDiff I ∞ := complexCoreReal_isContMDiff C I hC
  exact inferInstanceAs (ContMDiffVectorBundle ∞ F (complexCoreReal C).Fiber I)

end

variable {S : Type*} [Fintype S]

def lineDiagonal (c : S → ℂ) : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S :=
  (EuclideanSpace.equiv S ℂ).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi (fun s => c s • (ContinuousLinearMap.proj s : (S → ℂ) →L[ℂ] ℂ))).comp
      (EuclideanSpace.equiv S ℂ).toContinuousLinearMap)

def lineDiagonalLinear : (S → ℂ) →ₗ[ℂ] (EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) where
  toFun := lineDiagonal
  map_add' c d := by ext v s; change (c s+d s)*v s=c s*v s+d s*v s; ring
  map_smul' z c := by ext v s; change (z*c s)*v s=z*(c s*v s); ring

variable {B : Type*} [TopologicalSpace B] {J : S → Type*}
  (C : ∀ s, VectorBundleCore ℂ B ℂ (J s))

omit [Fintype S] in
theorem lineSumTransition_eq_diagonal (a b : ∀ s, J s) (x : B) :
    lineSumTransition C a b x = lineDiagonal (fun s => (C s).coordChange (a s) (b s) x 1) := by
  ext v s
  change (C s).coordChange (a s) (b s) x (v s) =
    ((C s).coordChange (a s) (b s) x 1)*(v s)
  have h := map_smul ((C s).coordChange (a s) (b s) x) (v s) (1 : ℂ)
  simpa only [smul_eq_mul,mul_one,one_mul,mul_comm] using h

theorem finiteLineSumCore_transition_smooth
    {X H : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [TopologicalSpace H]
    (I : ModelWithCorners ℝ X H) [ChartedSpace H B]
    (hC : ∀ s a b, ContMDiffOn I 𝓘(ℝ,ℂ →L[ℂ] ℂ) ∞ ((C s).coordChange a b)
      ((C s).baseSet a ∩ (C s).baseSet b)) (a b : ∀ s, J s) :
    ContMDiffOn I 𝓘(ℝ,EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) ∞
      ((finiteLineSumCore C).coordChange a b)
      ((finiteLineSumCore C).baseSet a ∩ (finiteLineSumCore C).baseSet b) := by
  have hc : ContMDiffOn I 𝓘(ℝ,S → ℂ) ∞
      (fun x s => (C s).coordChange (a s) (b s) x 1)
      ((finiteLineSumCore C).baseSet a ∩ (finiteLineSumCore C).baseSet b) := by
    apply contMDiffOn_pi_space.mpr
    intro s x hx
    exact ((ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).restrictScalars ℝ).contDiff.contDiffAt.contMDiffAt.comp_contMDiffWithinAt x
      ((hC s (a s) (b s)).mono (fun y (hy : y ∈ (finiteLineSumCore C).baseSet a ∩ (finiteLineSumCore C).baseSet b) => ⟨hy.1 s,hy.2 s⟩) x hx)
  let hd := (lineDiagonalLinear (S := S)).toContinuousLinearMap.restrictScalars ℝ
  intro x hx
  have h := hd.contDiff.contDiffAt.contMDiffAt.comp_contMDiffWithinAt x (hc x hx)
  exact h.congr (fun y _ => by simpa [hd, finiteLineSumCore, lineDiagonalLinear] using lineSumTransition_eq_diagonal C a b y) (by simpa [hd, finiteLineSumCore, lineDiagonalLinear] using lineSumTransition_eq_diagonal C a b x)

end Kaplansky

end

open Bundle Topology
open scoped Manifold ContDiff
namespace Kaplansky
variable {B F G J : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
  (C : VectorBundleCore ℂ B F J) (e : F ≃L[ℂ] G)

/-- A fixed linear change of model coordinates; the gluing is conjugated. -/
def changeModelCore : VectorBundleCore ℂ B G J where
  baseSet := C.baseSet
  isOpen_baseSet := C.isOpen_baseSet
  indexAt := C.indexAt
  mem_baseSet_at := C.mem_baseSet_at
  coordChange i j x := e.toContinuousLinearMap.comp ((C.coordChange i j x).comp e.symm.toContinuousLinearMap)
  coordChange_self i x hx v := by simp [C.coordChange_self i x hx]
  continuousOn_coordChange i j := continuousOn_const.clm_comp ((C.continuousOn_coordChange i j).clm_comp continuousOn_const)
  coordChange_comp i j k x hx v := by
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] using
      congrArg e (C.coordChange_comp i j k x hx (e.symm v))

/-- The coordinate change is a homeomorphism of actual total spaces. -/
def changeModelCoreTotalHomeomorph : TotalSpace F C.Fiber ≃ₜ TotalSpace G (changeModelCore C e).Fiber where
  toFun z := ⟨z.proj,e z.2⟩
  invFun z := ⟨z.proj,e.symm z.2⟩
  left_inv z := by
    obtain ⟨x, v⟩ := z
    exact congrArg (fun w => TotalSpace.mk' F x w) (e.symm_apply_apply v)
  right_inv z := by
    obtain ⟨x, v⟩ := z
    exact congrArg (fun w => TotalSpace.mk' G x w) (e.apply_symm_apply v)
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro z
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨(FiberBundle.continuous_proj F C.Fiber).continuousAt,?_⟩
    have h := ((C.localTriv (C.indexAt z.proj)).continuousAt
      ((C.localTriv _).mem_source.mpr (C.mem_baseSet_at z.proj))).snd
    change ContinuousAt (fun x : TotalSpace F C.Fiber =>
      e (C.coordChange (C.indexAt x.proj) (C.indexAt z.proj) x.proj (e.symm (e x.2)))) z
    change ContinuousAt (fun x : TotalSpace F C.Fiber =>
      C.coordChange (C.indexAt x.proj) (C.indexAt z.proj) x.proj x.2) z at h
    have he (x : TotalSpace F C.Fiber) : e.symm (e x.2) = x.2 := e.symm_apply_apply x.2
    simpa only [Function.comp_def, he] using e.continuous.continuousAt.comp h
  continuous_invFun := by
    apply continuous_iff_continuousAt.mpr
    intro z
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨(FiberBundle.continuous_proj G (changeModelCore C e).Fiber).continuousAt,?_⟩
    have h := (((changeModelCore C e).localTriv (C.indexAt z.proj)).continuousAt
      (((changeModelCore C e).localTriv _).mem_source.mpr (C.mem_baseSet_at z.proj))).snd
    change ContinuousAt (fun x : TotalSpace G (changeModelCore C e).Fiber =>
      C.coordChange (C.indexAt x.proj) (C.indexAt z.proj) x.proj (e.symm x.2)) z
    change ContinuousAt (fun x : TotalSpace G (changeModelCore C e).Fiber =>
      e (C.coordChange (C.indexAt x.proj) (C.indexAt z.proj) x.proj (e.symm x.2))) z at h
    simpa only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply] using e.symm.continuous.continuousAt.comp h

theorem changeModelCore_transition_smooth
    {X H : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [TopologicalSpace H]
    (I : ModelWithCorners ℝ X H) [ChartedSpace H B]
    (hC : ∀ a b, ContMDiffOn I 𝓘(ℝ,F →L[ℂ] F) ∞ (C.coordChange a b)
      (C.baseSet a ∩ C.baseSet b)) (a b : J) :
    ContMDiffOn I 𝓘(ℝ,G →L[ℂ] G) ∞ ((changeModelCore C e).coordChange a b)
      ((changeModelCore C e).baseSet a ∩ (changeModelCore C e).baseSet b) := by
  let L : (F →L[ℂ] F) →L[ℂ] (G →L[ℂ] G) :=
    (ContinuousLinearMap.compL ℂ G F G e.toContinuousLinearMap).comp
      ((ContinuousLinearMap.compL ℂ G F F).flip e.symm.toContinuousLinearMap)
  intro x hx
  exact (L.restrictScalars ℝ).contDiff.contDiffAt.contMDiffAt.comp_contMDiffWithinAt x (hC a b x hx)

instance changeModelFiberNorm (x : B) : NormedAddCommGroup ((changeModelCore C e).Fiber x) :=
  inferInstanceAs (NormedAddCommGroup G)
instance changeModelFiberNormedSpace (x : B) : NormedSpace ℂ ((changeModelCore C e).Fiber x) :=
  inferInstanceAs (NormedSpace ℂ G)

end Kaplansky

end

end OAI
