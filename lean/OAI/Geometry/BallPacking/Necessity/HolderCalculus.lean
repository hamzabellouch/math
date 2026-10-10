import Mathlib
import OAI.Geometry.BallPacking.Necessity.FrameFredholm

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal

open scoped ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

 def normalizedFrameCoefficient (B : E →L[ℝ] E) (J : E → E →L[ℝ] E)
    (u : ℂ → E) (z : ℂ) : E →L[ℝ] E :=
  (crFrame B J u z).inverse.comp (frameLowerOrder B J u z)

 theorem normalizedFrameCoefficient_smooth {η : E → E →L[ℝ] E →L[ℝ] ℝ}
    {B : E →L[ℝ] E} {J : E → E →L[ℝ] E} {u : ℂ → E}
    (hB : ∀ x, CompatibleWith (η x) B) (hJc : ∀ x, CompatibleWith (η x) (J x))
    (hJ : ContDiff ℝ ∞ J) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (normalizedFrameCoefficient B J u) := by
  have hA := crFrame_smooth (B := B) hJ hu
  have hi : ContDiff ℝ ∞ (fun z => (crFrame B J u z).inverse) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    exact (crFrame_invertible hB hJc u z).contDiffAt_map_inverse.comp z hA.contDiffAt
  have hDA : ContDiff ℝ ∞ (fderiv ℝ (crFrame B J u)) := hA.fderiv_right (by simp)
  have hDJ : ContDiff ℝ ∞ (fun z => fderiv ℝ J (u z)) :=
    (hJ.fderiv_right (by simp)).comp hu
  have hDu : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  unfold normalizedFrameCoefficient frameLowerOrder
  exact hi.clm_comp (((hDA.clm_apply contDiff_const).sub
    ((hJ.comp hu).clm_comp (hDA.clm_apply contDiff_const))).sub
    ((((ContinuousLinearMap.flipₗᵢ ℝ E E E).toContinuousLinearEquiv.contDiff.comp hDJ).clm_apply
      (hDu.clm_apply contDiff_const)).clm_comp hA))

omit [FiniteDimensional ℝ E] in
 theorem normalizedFrameCoefficient_compact {B : E →L[ℝ] E}
    {J : E → E →L[ℝ] E} (hB : ∀ v, B (B v) = -v)
    (hc : HasCompactSupport (fun x => J x-B)) {u : ℂ → E} (hup : IsProperMap u) :
    HasCompactSupport (normalizedFrameCoefficient B J u) := by
  have hh := frameLowerOrder_compact hB hc hup
  rw [hasCompactSupport_iff_eventuallyEq] at hh ⊢
  filter_upwards [hh] with z hz
  simp only [normalizedFrameCoefficient,show frameLowerOrder B J u z=0 from hz,
    ContinuousLinearMap.comp_zero,Pi.zero_apply]

 theorem linearizedCR_normalizedFrame {η : E → E →L[ℝ] E →L[ℝ] ℝ}
    {B : E →L[ℝ] E} {J : E → E →L[ℝ] E}
    (hB : ∀ x, CompatibleWith (η x) B) (hJ : ∀ x, CompatibleWith (η x) (J x))
    {u v : ℂ → E} (hA : Differentiable ℝ (crFrame B J u))
    (hv : Differentiable ℝ v) (z : ℂ) :
    linearizedCR J u (fun w => crFrame B J u w (v w)) z =
      crFrame B J u z (crOperator (fun _ => B) v z + normalizedFrameCoefficient B J u z (v z)) := by
  rw [linearizedCR_frame (hB (u z)).1 (fun x => (hJ x).1) hA hv z,map_add]
  congr 1
  exact ((crFrame_invertible hB hJ u z).self_apply_inverse _).symm

end HigherDimensionalBallPacking.Rigidity

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E]
local instance holderCalculusComplexNormedAddCommGroup :
    NormedAddCommGroup (HolderSpace ℂ E ((1:ℝ)/3)) := inferInstance
local instance holderCalculusComplexNormedSpace :
    NormedSpace ℝ (HolderSpace ℂ E ((1:ℝ)/3)) := inferInstance
local instance holderCalculusCompactNormedAddCommGroup (R : ℝ) :
    NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance holderCalculusCompactNormedSpace (R : ℝ) :
    NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

 

def framedMarkedVariation (J : E → E →L[ℝ] E) (u : ℂ → E) (R : ℝ)
    (g : CompactHolderSpace E R) (z : ℂ) : E :=
  crFrame ((ContinuousLinearMap.lsmul ℝ ℂ) Complex.I) J u z (markedCRInverse R g z)

omit [FiniteDimensional ℂ E] in
lemma markedCRInverse_differentiable (R : ℝ) (g : CompactHolderSpace E R) :
    Differentiable ℝ (markedCRInverse R g) := by
  exact (((compactCRInverse_contDiff R g).differentiable (by norm_num)).sub_const _).sub
    (differentiable_id.smul_const _)

omit [FiniteDimensional ℂ E] in
@[simp] lemma framedMarkedVariation_zero (J : E → E →L[ℝ] E) (u : ℂ → E)
    (R : ℝ) (g : CompactHolderSpace E R) : framedMarkedVariation J u R g 0=0 := by
  simp [framedMarkedVariation]

omit [FiniteDimensional ℂ E] in
@[simp] lemma framedMarkedVariation_one (J : E → E →L[ℝ] E) (u : ℂ → E)
    (R : ℝ) (g : CompactHolderSpace E R) : framedMarkedVariation J u R g 1=0 := by
  simp [framedMarkedVariation]

 

theorem exists_marked_fredholm_linearization
    {η : E → E →L[ℝ] E →L[ℝ] ℝ} {J : E → E →L[ℝ] E} {u : ℂ → E}
    (hB : ∀ x, CompatibleWith (η x) ((ContinuousLinearMap.lsmul ℝ ℂ) Complex.I))
    (hJc : ∀ x, CompatibleWith (η x) (J x)) (hJ : ContDiff ℝ ∞ J)
    (hc : HasCompactSupport (fun x => J x-(ContinuousLinearMap.lsmul ℝ ℂ) Complex.I))
    (hu : ContDiff ℝ ∞ u) (hup : IsProperMap u) :
    ∃ R : ℝ, 0 < R ∧ ∃ T : CompactHolderSpace E R →L[ℝ] CompactHolderSpace E R,
      T.IsFredholm ∧ ∀ g z, compactHolderValue R (T g) z =
        (crFrame ((ContinuousLinearMap.lsmul ℝ ℂ) Complex.I) J u z).inverse
          (linearizedCR J u (framedMarkedVariation J u R g) z) := by
  let B : E →L[ℝ] E := (ContinuousLinearMap.lsmul ℝ ℂ) Complex.I
  let M : ℂ → E →L[ℝ] E := normalizedFrameCoefficient B J u
  have hMs : ContDiff ℝ ∞ M := normalizedFrameCoefficient_smooth hB hJc hJ hu
  have hMc : HasCompactSupport M := normalizedFrameCoefficient_compact (hB 0).1 hc hup
  obtain ⟨S,hS⟩ := hMc.isBounded.subset_closedBall (0:ℂ)
  let R := max S 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right S 1)
  have hMR : ∀ z : ℂ, R < ‖z‖ → M z=0 := by
    intro z hz
    apply image_eq_zero_of_notMem_tsupport
    intro hh
    have hh' : ‖z‖ ≤ S := by simpa only [Metric.mem_closedBall,dist_zero_right] using hS hh
    exact (not_lt_of_ge (hh'.trans (le_max_left S 1))) hz
  refine ⟨R,hR,markedCRLinear R M hMs hMc hMR,markedCRLinear_fredholm R M hMs hMc hMR,?_⟩
  intro g z
  have he := linearizedCR_normalizedFrame hB hJc
    ((crFrame_smooth hJ hu).differentiable (by simp)) (markedCRInverse_differentiable R g) z
  change linearizedCR J u (framedMarkedVariation J u R g) z =
    crFrame B J u z (crOperator (fun _ => B) (markedCRInverse R g) z+M z (markedCRInverse R g z)) at he
  rw [he,(crFrame_invertible hB hJc u z).inverse_apply_self]
  exact markedCRLinear_differential R M hMs hMc hMR g z

end HigherDimensionalBallPacking.Rigidity

 

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
universe u v
variable {P : Type u} [TopologicalSpace P]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

abbrev UnitTime := Set.Icc (0:ℝ) 1

def unitExtend (f : C(UnitTime,F)) : C(ℝ,F) :=
  f.comp ⟨Set.projIcc 0 1 (by norm_num), continuous_projIcc⟩

omit [NormedSpace ℝ F] [CompleteSpace F] in
@[simp] theorem unitExtend_coe (f : C(UnitTime,F)) (t : UnitTime) :
    unitExtend f t = f t := by simp [unitExtend]

def unitMean : C(UnitTime,F) →L[ℝ] F :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ t in (0:ℝ)..1, unitExtend f t
      map_add' := by
        intro f g
        exact intervalIntegral.integral_add
          ((unitExtend f).continuous.intervalIntegrable _ _)
          ((unitExtend g).continuous.intervalIntegrable _ _)
      map_smul' := fun c f => intervalIntegral.integral_smul c _ }
    1 (by
      intro f
      change ‖∫ t in (0:ℝ)..1, unitExtend f t‖ ≤ 1*‖f‖
      simpa using intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0:ℝ)) (b := 1) (fun t _ => f.norm_coe_le_norm (Set.projIcc 0 1 (by norm_num) t)))

omit [CompleteSpace F] in
theorem unitMean_norm (f : C(UnitTime,F)) : ‖unitMean f‖ ≤ ‖f‖ := by
  change ‖∫ t in (0:ℝ)..1, unitExtend f t‖ ≤ ‖f‖
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (fun t _ => f.norm_coe_le_norm (Set.projIcc 0 1 (by norm_num) t))

def sectionMean (g : (P × UnitTime) →ᵇ F) : P →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => unitMean (g.toContinuousMap.curry p))
    (unitMean.continuous.comp g.toContinuousMap.curry.continuous)
    ‖g‖ (by
      intro p
      exact (unitMean_norm _).trans ((ContinuousMap.norm_le _ (norm_nonneg g)).mpr
        (fun t => g.norm_coe_le_norm (p,t))))

omit [CompleteSpace F] in
@[simp] theorem sectionMean_apply (g : (P × UnitTime) →ᵇ F) (p : P) :
    sectionMean g p = ∫ t in (0:ℝ)..1, g (p,Set.projIcc 0 1 (by norm_num) t) := rfl

omit [CompleteSpace F] in
theorem sectionMean_norm (g : (P × UnitTime) →ᵇ F) : ‖sectionMean g‖ ≤ ‖g‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg g)).mpr
  intro p
  exact (unitMean_norm _).trans ((ContinuousMap.norm_le _ (norm_nonneg g)).mpr
    (fun t => g.norm_coe_le_norm (p,t)))

def sectionMeanCLM : ((P × UnitTime) →ᵇ F) →L[ℝ] (P →ᵇ F) :=
  LinearMap.mkContinuous
    { toFun := sectionMean
      map_add' := by
        intro f g
        ext p
        change unitMean ((f+g).toContinuousMap.curry p) = _
        change unitMean (f.toContinuousMap.curry p+g.toContinuousMap.curry p) = _
        exact unitMean.map_add _ _
      map_smul' := by
        intro c f
        ext p
        change unitMean (c • f.toContinuousMap.curry p) = _
        exact unitMean.map_smul c _ }
    1 (fun g => by
      change ‖sectionMean g‖ ≤ 1*‖g‖
      simpa only [one_mul] using sectionMean_norm g)

omit [CompleteSpace F] in
@[simp] theorem sectionMeanCLM_apply (g : (P × UnitTime) →ᵇ F) (p : P) :
    sectionMeanCLM g p = ∫ t in (0:ℝ)..1, g (p,Set.projIcc 0 1 (by norm_num) t) := rfl

end HigherDimensionalBallPacking.Rigidity

namespace HigherDimensionalBallPacking.Rigidity
universe u v
variable {K : Type u} [MetricSpace K]
variable {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance holderCalculusNormedAddCommGroup
    (G : Type v) [NormedAddCommGroup G] [NormedSpace ℝ G] (α : ℝ) :
    NormedAddCommGroup (HolderSpace K G α) := inferInstance
local instance holderCalculusNormedSpace
    (G : Type v) [NormedAddCommGroup G] [NormedSpace ℝ G] (α : ℝ) :
    NormedSpace ℝ (HolderSpace K G α) := inferInstance

 

theorem compactCoefficient_lipschitz {f : E → F} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    LipschitzWith ‖compactCoefficient (fderiv ℝ f) (hf.continuous_fderiv (by simp)) (hc.fderiv ℝ)‖₊ f := by
  apply lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by simp))
  intro x
  exact_mod_cast (compactCoefficient (fderiv ℝ f) (hf.continuous_fderiv (by simp))
    (hc.fderiv ℝ)).norm_coe_le_norm x

def holderPost (α : ℝ) (hα : 0<α) (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (u : HolderSpace K E α) : HolderSpace K F α :=
  holderSpaceMk α (superposeBCF (compactCoefficient f hf.continuous hc) 0 (holderValue α u))
    (‖compactCoefficient (fderiv ℝ f) (hf.continuous_fderiv (by simp)) (hc.fderiv ℝ)‖*‖u‖)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by
      intro x y
      change ‖f (0+holderValue α u x)-f (0+holderValue α u y)‖ ≤ _
      simp only [zero_add]
      exact ((compactCoefficient_lipschitz hf hc).norm_sub_le _ _).trans
        ((mul_le_mul_of_nonneg_left (holderSpace_estimate α hα u x y) (norm_nonneg _)).trans_eq
          (by rw [mul_assoc])))

@[simp] theorem holderPost_apply (α : ℝ) (hα : 0<α) (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (u : HolderSpace K E α) (x : K) :
    holderValue α (holderPost α hα f hf hc u) x = f (holderValue α u x) := by
  change f (0+holderValue α u x) = _
  rw [zero_add]

theorem segmentSection_bound (u : K →ᵇ E) (p : OffDiagonal K × UnitTime) :
    ‖u p.1.val.2 + (p.2 : ℝ) • (u p.1.val.1-u p.1.val.2)‖ ≤ 3*‖u‖ := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg p.2.property.1]
  have hs : ‖u p.1.val.1-u p.1.val.2‖ ≤ 2*‖u‖ :=
    (norm_sub_le _ _).trans (by linarith [u.norm_coe_le_norm p.1.val.1,u.norm_coe_le_norm p.1.val.2])
  have ht := mul_le_mul p.2.property.2 hs (norm_nonneg _) (show (0:ℝ)≤1 by norm_num)
  linarith [u.norm_coe_le_norm p.1.val.2]

 

def segmentSection : (K →ᵇ E) →L[ℝ] ((OffDiagonal K × UnitTime) →ᵇ E) :=
  LinearMap.mkContinuous
    { toFun := fun u => BoundedContinuousFunction.ofNormedAddCommGroup
        (fun p => u p.1.val.2 + (p.2 : ℝ) • (u p.1.val.1-u p.1.val.2))
        (by fun_prop) (3*‖u‖) (segmentSection_bound u)
      map_add' := by
        intro u v
        apply BoundedContinuousFunction.ext
        intro p
        change (u p.1.val.2+v p.1.val.2)+(p.2:ℝ) •
            ((u p.1.val.1+v p.1.val.1)-(u p.1.val.2+v p.1.val.2)) =
          (u p.1.val.2+(p.2:ℝ) • (u p.1.val.1-u p.1.val.2))+
          (v p.1.val.2+(p.2:ℝ) • (v p.1.val.1-v p.1.val.2))
        simp only [smul_add,smul_sub]
        abel
      map_smul' := by
        intro c u
        apply BoundedContinuousFunction.ext
        intro p
        change c • u p.1.val.2+(p.2:ℝ) • (c • u p.1.val.1-c • u p.1.val.2) =
          c • (u p.1.val.2+(p.2:ℝ) • (u p.1.val.1-u p.1.val.2))
        module }
    3 (fun u => BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
      (by positivity) (segmentSection_bound u))

@[simp] theorem segmentSection_apply (u : K →ᵇ E) (p : OffDiagonal K × UnitTime) :
    segmentSection u p = u p.1.val.2 + (p.2 : ℝ) • (u p.1.val.1-u p.1.val.2) := rfl

def differencePull : (OffDiagonal K →ᵇ E) →L[ℝ] ((OffDiagonal K × UnitTime) →ᵇ E) :=
  BoundedContinuousFunction.compContinuousCLM E ℝ ⟨Prod.fst,continuous_fst⟩

@[simp] theorem differencePull_apply (v : OffDiagonal K →ᵇ E) (p : OffDiagonal K × UnitTime) :
    differencePull v p = v p.1 := rfl

variable [CompleteSpace F]

def holderPostDifference (α : ℝ) (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (u : HolderSpace K E α) : OffDiagonal K →ᵇ F :=
  sectionMeanCLM (sectionCLM
    (superposeBCF (compactCoefficient (fderiv ℝ f) (hf.continuous_fderiv (by simp)) (hc.fderiv ℝ))
      0 (segmentSection (holderValue α u))) (differencePull (holderDifference α u)))

theorem holderSegment_contDiff (α : ℝ) :
    ContDiff ℝ ∞ (fun u : HolderSpace K E α => segmentSection (holderValue α u)) :=
  (segmentSection (K := K) (E := E)).contDiff.comp (holderValue (K := K) (E := E) α).contDiff

omit [CompleteSpace F] in
theorem holderCoefficient_contDiff (α : ℝ) (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : ContDiff ℝ ∞ (fun u : HolderSpace K E α => superposeBCF
      (compactCoefficient (fderiv ℝ f) (hf.continuous_fderiv (by simp)) (hc.fderiv ℝ))
      0 (segmentSection (holderValue α u))) := by
  exact (compactSuperpose_contDiff (hf.fderiv_right (by simp)) (hc.fderiv ℝ)
    (0 : C(OffDiagonal K × UnitTime,E))).comp (holderSegment_contDiff α)

omit [CompleteSpace F] in
theorem holderCoefficientOperator_contDiff (α : ℝ) (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : ContDiff ℝ ∞ (fun u : HolderSpace K E α => sectionCLM (superposeBCF
      (compactCoefficient (fderiv ℝ f) (hf.continuous_fderiv (by simp)) (hc.fderiv ℝ))
      0 (segmentSection (holderValue α u)))) :=
  (sectionOperatorCLM (K := OffDiagonal K × UnitTime) (E := E) (F := F)).contDiff.comp
    (holderCoefficient_contDiff α f hf hc)

omit [CompleteSpace F] in
theorem holderPostIntegrand_contDiff (α : ℝ) (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : ContDiff ℝ ∞ (fun u : HolderSpace K E α => sectionCLM (superposeBCF
      (compactCoefficient (fderiv ℝ f) (hf.continuous_fderiv (by simp)) (hc.fderiv ℝ))
      0 (segmentSection (holderValue α u))) (differencePull (holderDifference α u))) :=
  (holderCoefficientOperator_contDiff α f hf hc).clm_apply
    ((differencePull (K := K) (E := E)).contDiff.comp (holderDifference (K := K) (E := E) α).contDiff)

omit [CompleteSpace F] in
theorem holderPostDifference_contDiff (α : ℝ) (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : ContDiff ℝ ∞ (holderPostDifference α f hf hc (K := K)) :=
  (sectionMeanCLM (P := OffDiagonal K) (F := F)).contDiff.comp
    (holderPostIntegrand_contDiff α f hf hc)

omit [CompleteSpace F] in
theorem holderPostDifference_integral (α : ℝ) (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (u : HolderSpace K E α) (p : OffDiagonal K) :
    holderPostDifference α f hf hc u p = ∫ t in (0:ℝ)..1,
      fderiv ℝ f (holderValue α u p.val.2 + t •
        (holderValue α u p.val.1 - holderValue α u p.val.2)) (holderDifference α u p) := by
  change (∫ t in (0:ℝ)..1, fderiv ℝ f (0+segmentSection (holderValue α u)
    (p,Set.projIcc 0 1 (by norm_num) t)) (holderDifference α u p)) = _
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0:ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using ht
  simp only [Set.projIcc_of_mem (by norm_num : (0:ℝ)≤1) ht',segmentSection_apply,zero_add]

 

theorem holderPostDifference_relation (α : ℝ) (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (u : HolderSpace K E α) (p : OffDiagonal K) :
    (dist p.val.1 p.val.2)^α • holderPostDifference α f hf hc u p =
      f (holderValue α u p.val.1)-f (holderValue α u p.val.2) := by
  let a := holderValue α u p.val.2
  let d := holderValue α u p.val.1-holderValue α u p.val.2
  have hder : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (a+t • d)) (fderiv ℝ f (a+t • d) d) t := by
    intro t
    exact ((hf.differentiable (by simp)) (a+t • d)).hasFDerivAt.comp_hasDerivAt t
      (by simpa only [one_smul, id_eq] using (((hasDerivAt_id t).smul_const d).const_add a))
  have hint : IntervalIntegrable (fun t : ℝ => fderiv ℝ f (a+t • d) d) MeasureTheory.volume 0 1 :=
    (((hf.continuous_fderiv (by simp)).comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
      continuous_const).intervalIntegrable _ _
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t) hint
  simp only [one_smul,zero_smul,add_zero] at hi
  rw [holderPostDifference_integral,← intervalIntegral.integral_smul]
  calc
    _ = ∫ t in (0:ℝ)..1, fderiv ℝ f (a+t • d) d := by
      apply intervalIntegral.integral_congr
      intro t _
      change (dist p.val.1 p.val.2)^α • (fderiv ℝ f (a+t • d)) (holderDifference α u p) = _
      rw [← map_smul]
      congr 1
      exact (u.property p).symm
    _ = f (holderValue α u p.val.1)-f (holderValue α u p.val.2) := by
      simpa only [a,d,add_sub_cancel] using hi

theorem holderPost_coe (α : ℝ) (hα : 0<α) (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (u : HolderSpace K E α) :
    (holderPost α hα f hf hc u).val =
      (superposeBCF (compactCoefficient f hf.continuous hc) 0 (holderValue α u),
       holderPostDifference α f hf hc u) := by
  apply Prod.ext
  · rfl
  · ext p
    have hw : (dist p.val.1 p.val.2)^α ≠ 0 :=
      (Real.rpow_pos_of_pos (dist_pos.mpr p.property) α).ne'
    apply smul_right_injective F hw
    change (dist p.val.1 p.val.2)^α • (holderPost α hα f hf hc u).val.2 p =
      (dist p.val.1 p.val.2)^α • holderPostDifference α f hf hc u p
    rw [← (holderPost α hα f hf hc u).property p,holderPostDifference_relation]
    simp only [← holderValue_apply,holderPost_apply]

theorem holderPost_ambient_contDiff (α : ℝ) (hα : 0<α) (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (fun u : HolderSpace K E α => (holderPost α hα f hf hc u).val) := by
  have he : (fun u : HolderSpace K E α => (holderPost α hα f hf hc u).val) =
      (fun u : HolderSpace K E α => (superposeBCF (compactCoefficient f hf.continuous hc) 0
        (holderValue α u),holderPostDifference α f hf hc u)) := funext (holderPost_coe α hα f hf hc)
  rw [he]
  apply ContDiff.prodMk
  · exact (compactSuperpose_contDiff hf hc (0 : C(K,E))).comp (holderValue (K := K) (E := E) α).contDiff
  · exact holderPostDifference_contDiff α f hf hc

 

omit [CompleteSpace F] in
theorem holder_hasFDerivAt_of_ambient
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (α : ℝ) (g : P → HolderSpace K F α) (g' : P →L[ℝ] HolderSpace K F α) (x : P)
    (hg : DifferentiableAt ℝ (fun y => (g y).val) x)
    (hv : HasFDerivAt (fun y => holderValue α (g y)) ((holderValue α).comp g') x) :
    HasFDerivAt g g' x := by
  let L := fderiv ℝ (fun y => (g y).val) x
  have hL : HasFDerivAt (fun y => (g y).val) L x := hg.hasFDerivAt
  have hmem : ∀ v, L v ∈ holderGraph K F α := by
    intro v p
    let C : ((K →ᵇ F) × (OffDiagonal K →ᵇ F)) →L[ℝ] F :=
      (BoundedContinuousFunction.evalCLM ℝ p.val.1).comp (ContinuousLinearMap.fst ℝ _ _) -
      (BoundedContinuousFunction.evalCLM ℝ p.val.2).comp (ContinuousLinearMap.fst ℝ _ _) -
      (dist p.val.1 p.val.2)^α •
        (BoundedContinuousFunction.evalCLM ℝ p).comp (ContinuousLinearMap.snd ℝ _ _)
    have hc : (fun y => C (g y).val) = fun _ : P => (0 : F) := by
      funext y
      change (g y).val.1 p.val.1-(g y).val.1 p.val.2 -
        (dist p.val.1 p.val.2)^α • (g y).val.2 p = 0
      exact sub_eq_zero.mpr ((g y).property p)
    have hd : HasFDerivAt (fun y => C (g y).val) (C.comp L) x :=
      C.hasFDerivAt.comp x hL
    rw [hc] at hd
    have he := congrArg (fun A : P →L[ℝ] F => A v) (hd.unique (hasFDerivAt_const (0:F) x))
    change (L v).1 p.val.1 - (L v).1 p.val.2 - (dist p.val.1 p.val.2)^α • (L v).2 p = 0 at he
    exact sub_eq_zero.mp he
  have hfst : (ContinuousLinearMap.fst ℝ (K →ᵇ F) (OffDiagonal K →ᵇ F)).comp L =
      (holderValue α).comp g' :=
    (((ContinuousLinearMap.fst ℝ (K →ᵇ F) (OffDiagonal K →ᵇ F)).hasFDerivAt).comp x hL).unique hv
  have heq : L = (holderGraph K F α).subtypeL.comp g' := by
    apply ContinuousLinearMap.ext
    intro v
    have he : holderValue α (⟨L v,hmem v⟩ : HolderSpace K F α) = holderValue α (g' v) :=
      congrArg (fun A : P →L[ℝ] (K →ᵇ F) => A v) hfst
    exact congrArg Subtype.val (holderValue_injective α he)
  rw [heq] at hL
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hL ⊢
  rw [← Asymptotics.isLittleO_norm_left]
  rw [← Asymptotics.isLittleO_norm_left] at hL
  exact hL

theorem holderPost_hasFDerivAt (α : ℝ) (hα : 0<α) (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (u : HolderSpace K E α) :
    HasFDerivAt (holderPost α hα f hf hc)
      (holderCLM α (holderPost α hα (fderiv ℝ f) (hf.fderiv_right (by simp)) (hc.fderiv ℝ) u)) u := by
  apply holder_hasFDerivAt_of_ambient
  · exact ((holderPost_ambient_contDiff α hα f hf hc).differentiable (by simp)) u
  · have hdf := hf.fderiv_right (show (∞ : WithTop ℕ∞) + 1 ≤ ∞ by simp)
    have hd := (superposeBCF_hasFDerivAt
      (compactCoefficient f hf.continuous hc)
      (compactCoefficient (fderiv ℝ f) hdf.continuous (hc.fderiv ℝ))
      (fun x => (hf.differentiable (by simp) x).hasFDerivAt)
      (hdf.continuous.uniformContinuous_of_tendsto_cocompact (hc.fderiv ℝ).is_zero_at_infty)
      (0 : C(K,E)) (holderValue α u)).comp u (holderValue α).hasFDerivAt
    convert hd using 1 <;> try rfl

 

theorem holderPost_contDiff_nat (m : ℕ) (α : ℝ) (hα : 0<α) (f : E → F)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ m (holderPost α hα f hf hc (K := K)) := by
  induction m generalizing F with
  | zero =>
    apply contDiff_zero.mpr
    exact continuous_induced_rng.mpr (holderPost_ambient_contDiff α hα f hf hc).continuous
  | succ m ih =>
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun u => holderCLM α (holderPost α hα (fderiv ℝ f)
      (hf.fderiv_right (by simp)) (hc.fderiv ℝ) u),?_,holderPost_hasFDerivAt α hα f hf hc⟩
    exact (holderOperatorCLM (K := K) (E := E) (F := F) α).contDiff.comp
      (ih (fderiv ℝ f) (hf.fderiv_right (by simp)) (hc.fderiv ℝ))

theorem holderPost_contDiff (α : ℝ) (hα : 0<α) (f : E → F)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (holderPost α hα f hf hc (K := K)) :=
  contDiff_infty.mpr (fun m => holderPost_contDiff_nat m α hα f hf hc)

end HigherDimensionalBallPacking.Rigidity

end

end OAI
