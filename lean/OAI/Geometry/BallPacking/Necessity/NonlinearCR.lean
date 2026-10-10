import Mathlib
import OAI.Geometry.BallPacking.Necessity.HolderCalculus

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
open scoped ContDiff Topology BoundedContinuousFunction

namespace HigherDimensionalBallPacking.Rigidity
open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
universe u v
variable {K : Type u} [MetricSpace K]
variable {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance (G : Type v) [NormedAddCommGroup G] [NormedSpace ℝ G] (α : ℝ) :
    NormedAddCommGroup (HolderSpace K G α) := inferInstance
local instance (G : Type v) [NormedAddCommGroup G] [NormedSpace ℝ G] (α : ℝ) :
    NormedSpace ℝ (HolderSpace K G α) := inferInstance

def scalarSectionCLM (w : K →ᵇ ℝ) : (K →ᵇ E) →L[ℝ] (K →ᵇ E) :=
  LinearMap.mkContinuous
    { toFun := fun u => w • u
      map_add' := fun u v => smul_add w u v
      map_smul' := by
        intro c u
        ext x
        change w x • (c • u x) = c • (w x • u x)
        exact smul_comm _ _ _ }
    ‖w‖ (norm_smul_le w)

@[simp] theorem scalarSectionCLM_apply (w : K →ᵇ ℝ) (u : K →ᵇ E) (x : K) :
    scalarSectionCLM w u x = w x • u x := rfl

def pairDistance : C(OffDiagonal K,ℝ) :=
  ⟨fun p => dist p.val.1 p.val.2,
    (continuous_fst.comp continuous_subtype_val).dist (continuous_snd.comp continuous_subtype_val)⟩

@[simp] theorem pairDistance_apply (p : OffDiagonal K) :
    pairDistance p = dist p.val.1 p.val.2 := rfl

theorem pairDistance_pos (p : OffDiagonal K) : 0<pairDistance p := dist_pos.mpr p.property

def holderNearWeight : OffDiagonal K →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => (1+pairDistance p)⁻¹)
    ((show Continuous (fun p : OffDiagonal K => (1:ℝ)+pairDistance p) from continuous_const.add pairDistance.continuous).inv₀ (fun p => by have hd := pairDistance_pos p; positivity))
    1 (fun p => by
      have hd := pairDistance_pos p
      rw [Real.norm_of_nonneg (by positivity)]
      exact inv_le_one_of_one_le₀ (by linarith [pairDistance_pos p]))

@[simp] theorem holderNearWeight_apply (p : OffDiagonal K) :
    holderNearWeight p = (1+pairDistance p)⁻¹ := rfl

theorem divided_rpow_le_one {d α : ℝ} (hd : 0<d) (hα₀ : 0≤α) (hα₁ : α≤1) :
    d^(1-α)/(1+d) ≤ 1 := by
  apply (div_le_one (by positivity : 0<1+d)).mpr
  by_cases h : d≤1
  · exact (Real.rpow_le_one hd.le h (by linarith)).trans (by linarith)
  · have hh := Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤d) (show 1-α≤1 by linarith)
    rw [Real.rpow_one] at hh
    exact hh.trans (by linarith)

def holderFarWeight (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1) : OffDiagonal K →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => (pairDistance p)^(1-α)/(1+pairDistance p))
    ((pairDistance.continuous.rpow_const (fun p => Or.inl (pairDistance_pos p).ne')).div
      (continuous_const.add pairDistance.continuous) (fun p => by have hd := pairDistance_pos p; positivity))
    1 (fun p => by
      have hd := pairDistance_pos p
      rw [Real.norm_of_nonneg (by positivity)]
      exact divided_rpow_le_one (pairDistance_pos p) hα₀ hα₁)

@[simp] theorem holderFarWeight_apply (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1) (p : OffDiagonal K) :
    holderFarWeight α hα₀ hα₁ p = (pairDistance p)^(1-α)/(1+pairDistance p) := rfl

theorem holderFarWeight_relation (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1) (p : OffDiagonal K) :
    (pairDistance p)^α * holderFarWeight α hα₀ hα₁ p = 1-holderNearWeight p := by
  rw [holderFarWeight_apply,holderNearWeight_apply,← mul_div_assoc,
    ← Real.rpow_add (pairDistance_pos p)]
  rw [show α+(1-α)=1 by ring,Real.rpow_one]
  have hd := pairDistance_pos p
  field_simp [show (1+pairDistance p)≠0 by positivity]
  ring

def holderBaseDifference (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base) : OffDiagonal K →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => ((1+pairDistance p)⁻¹ * (pairDistance p)^(-α)) • (base p.val.1-base p.val.2))
    (by
      apply Continuous.smul
      · exact ((show Continuous (fun p : OffDiagonal K => (1:ℝ)+pairDistance p) from continuous_const.add pairDistance.continuous).inv₀ (fun p => by have hd := pairDistance_pos p; positivity)).mul
          (pairDistance.continuous.rpow_const (fun p => Or.inl (pairDistance_pos p).ne'))
      · exact (base.continuous.comp (continuous_fst.comp continuous_subtype_val)).sub
          (base.continuous.comp (continuous_snd.comp continuous_subtype_val)))
    L (fun p => by
      have hd := pairDistance_pos p
      rw [norm_smul,Real.norm_of_nonneg (by positivity)]
      have hh : ‖base p.val.1-base p.val.2‖ ≤ L*pairDistance p := by
        simpa only [dist_eq_norm,pairDistance_apply] using hb.dist_le_mul p.val.1 p.val.2
      refine (mul_le_mul_of_nonneg_left hh (by positivity)).trans ?_
      have he : (pairDistance p)^(-α)*pairDistance p = (pairDistance p)^(1-α) := by
        calc
          _ = (pairDistance p)^(-α)*(pairDistance p)^1 := by rw [Real.rpow_one]
          _ = (pairDistance p)^(-α+1) := (Real.rpow_add (pairDistance_pos p) (-α) 1).symm
          _ = _ := by congr 1; ring
      calc
        _ = L*((pairDistance p)^(1-α)/(1+pairDistance p)) := by rw [← he]; ring
        _ ≤ L*1 := mul_le_mul_of_nonneg_left
          (divided_rpow_le_one (pairDistance_pos p) hα₀ hα₁) L.property
        _ = L := mul_one _)

@[simp] theorem holderBaseDifference_apply (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base) (p : OffDiagonal K) :
    holderBaseDifference α hα₀ hα₁ base hb p =
      ((1+pairDistance p)⁻¹*(pairDistance p)^(-α)) • (base p.val.1-base p.val.2) := rfl

theorem holderBaseDifference_relation (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base) (p : OffDiagonal K) :
    (pairDistance p)^α • holderBaseDifference α hα₀ hα₁ base hb p =
      holderNearWeight p • (base p.val.1-base p.val.2) := by
  rw [holderBaseDifference_apply,holderNearWeight_apply,smul_smul]
  congr 1
  rw [mul_left_comm,← Real.rpow_add (pairDistance_pos p),add_neg_cancel,Real.rpow_zero,mul_one]

def baseSegment (base : C(K,E)) : C(OffDiagonal K × UnitTime,E) :=
  ⟨fun p => base p.1.val.2+(p.2:ℝ) • (base p.1.val.1-base p.1.val.2),by fun_prop⟩

@[simp] theorem baseSegment_apply (base : C(K,E)) (p : OffDiagonal K × UnitTime) :
    baseSegment base p = base p.1.val.2+(p.2:ℝ) • (base p.1.val.1-base p.1.val.2) := rfl

variable [CompleteSpace F]

def profileWeightedDifference (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (u : HolderSpace K E α) : OffDiagonal K →ᵇ E :=
  holderBaseDifference α hα₀ hα₁ base hb + scalarSectionCLM holderNearWeight (holderDifference α u)

theorem profileWeightedDifference_relation (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (u : HolderSpace K E α) (p : OffDiagonal K) :
    (pairDistance p)^α • profileWeightedDifference α hα₀ hα₁ base hb u p =
      holderNearWeight p • ((base p.val.1+holderValue α u p.val.1)-
        (base p.val.2+holderValue α u p.val.2)) := by
  change (pairDistance p)^α • (holderBaseDifference α hα₀ hα₁ base hb p +
    holderNearWeight p • holderDifference α u p) = _
  rw [smul_add,holderBaseDifference_relation,smul_comm ((pairDistance p)^α) (holderNearWeight p),
    ← show holderValue α u p.val.1-holderValue α u p.val.2 =
      (pairDistance p)^α • holderDifference α u p from u.property p]
  module

def profilePostDifference (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (u : HolderSpace K E α) : OffDiagonal K →ᵇ F :=
  sectionMeanCLM (sectionCLM (superposeBCF
    (compactCoefficient (fderiv ℝ f) (hf.continuous_fderiv (by simp)) (hc.fderiv ℝ))
    (baseSegment base) (segmentSection (holderValue α u)))
    (differencePull (profileWeightedDifference α hα₀ hα₁ base hb u))) +
  scalarSectionCLM (holderFarWeight α hα₀ hα₁)
    (pairLeft F (superposeBCF (compactCoefficient f hf.continuous hc) base (holderValue α u)) -
      pairRight F (superposeBCF (compactCoefficient f hf.continuous hc) base (holderValue α u)))

theorem segment_fderiv_integral (f : E → F) (hf : ContDiff ℝ ∞ f) (a b : E) :
    (∫ t in (0:ℝ)..1, fderiv ℝ f (a+t • (b-a)) (b-a)) = f b-f a := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => f (a+t • (b-a)))
      (fderiv ℝ f (a+t • (b-a)) (b-a)) t :=
    ((hf.differentiable (by simp)) (a+t • (b-a))).hasFDerivAt.comp_hasDerivAt t
      (by simpa only [one_smul,id_eq] using ((hasDerivAt_id t).smul_const (b-a)).const_add a)
  have hi : IntervalIntegrable (fun t : ℝ => fderiv ℝ f (a+t • (b-a)) (b-a))
      MeasureTheory.volume 0 1 :=
    (((hf.continuous_fderiv (by simp)).comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
      continuous_const).intervalIntegrable _ _
  simpa only [one_smul,zero_smul,add_zero,add_sub_cancel] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi

omit [CompleteSpace F] in
theorem profilePostDifference_integral (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (u : HolderSpace K E α) (p : OffDiagonal K) :
    profilePostDifference α hα₀ hα₁ base hb f hf hc u p =
      (∫ t in (0:ℝ)..1,
        fderiv ℝ f (base p.val.2+holderValue α u p.val.2 +
          t • ((base p.val.1+holderValue α u p.val.1)-(base p.val.2+holderValue α u p.val.2)))
          (profileWeightedDifference α hα₀ hα₁ base hb u p)) +
      holderFarWeight α hα₀ hα₁ p • (f (base p.val.1+holderValue α u p.val.1)-
        f (base p.val.2+holderValue α u p.val.2)) := by
  change (∫ t in (0:ℝ)..1, (fderiv ℝ f)
    (baseSegment base (p,Set.projIcc 0 1 (by norm_num) t) +
      segmentSection (holderValue α u) (p,Set.projIcc 0 1 (by norm_num) t))
    (profileWeightedDifference α hα₀ hα₁ base hb u p)) + _ = _
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0:ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using ht
  dsimp only
  rw [Set.projIcc_of_mem (by norm_num : (0:ℝ)≤1) ht']
  congr 2
  simp only [baseSegment_apply,segmentSection_apply]
  module

theorem profilePostDifference_relation (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (u : HolderSpace K E α) (p : OffDiagonal K) :
    (pairDistance p)^α • profilePostDifference α hα₀ hα₁ base hb f hf hc u p =
      f (base p.val.1+holderValue α u p.val.1)-f (base p.val.2+holderValue α u p.val.2) := by
  let a := base p.val.2+holderValue α u p.val.2
  let b := base p.val.1+holderValue α u p.val.1
  rw [profilePostDifference_integral,smul_add,smul_smul,holderFarWeight_relation,
    ← intervalIntegral.integral_smul]
  change (∫ t in (0:ℝ)..1, (pairDistance p)^α •
    fderiv ℝ f (a+t • (b-a)) (profileWeightedDifference α hα₀ hα₁ base hb u p)) +
      (1-holderNearWeight p) • (f b-f a) = f b-f a
  have he : (∫ t in (0:ℝ)..1, (pairDistance p)^α •
      fderiv ℝ f (a+t • (b-a)) (profileWeightedDifference α hα₀ hα₁ base hb u p)) =
        holderNearWeight p • (f b-f a) := by
    rw [← segment_fderiv_integral f hf a b,← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [← map_smul,profileWeightedDifference_relation,map_smul]
  rw [he]
  module

def holderProfilePost (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (u : HolderSpace K E α) : HolderSpace K F α :=
  ⟨(superposeBCF (compactCoefficient f hf.continuous hc) base (holderValue α u),
    profilePostDifference α hα₀ hα₁ base hb f hf hc u),
    fun p => (profilePostDifference_relation α hα₀ hα₁ base hb f hf hc u p).symm⟩

@[simp] theorem holderProfilePost_apply (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (u : HolderSpace K E α) (x : K) :
    holderValue α (holderProfilePost α hα₀ hα₁ base hb f hf hc u) x =
      f (base x+holderValue α u x) := rfl

end HigherDimensionalBallPacking.Rigidity

namespace HigherDimensionalBallPacking.Rigidity
open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
universe u v
variable {K : Type u} [MetricSpace K]
variable {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
local instance (G : Type v) [NormedAddCommGroup G] [NormedSpace ℝ G] (α : ℝ) :
    NormedAddCommGroup (HolderSpace K G α) := inferInstance
local instance (G : Type v) [NormedAddCommGroup G] [NormedSpace ℝ G] (α : ℝ) :
    NormedSpace ℝ (HolderSpace K G α) := inferInstance

theorem profileWeightedDifference_contDiff (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base) :
    ContDiff ℝ ∞ (profileWeightedDifference α hα₀ hα₁ base hb) :=
  contDiff_const.add ((scalarSectionCLM (E := E) (holderNearWeight (K := K))).contDiff.comp
    (holderDifference (K := K) (E := E) α).contDiff)

omit [CompleteSpace F] in
theorem profileCoefficient_contDiff (α : ℝ) (base : C(K,E)) (f : E → F)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (fun u : HolderSpace K E α => superposeBCF
      (compactCoefficient (fderiv ℝ f) (hf.continuous_fderiv (by simp)) (hc.fderiv ℝ))
      (baseSegment base) (segmentSection (holderValue α u))) :=
  (compactSuperpose_contDiff (hf.fderiv_right (by simp)) (hc.fderiv ℝ)
    (baseSegment base)).comp (holderSegment_contDiff α)

omit [CompleteSpace F] in
theorem profileCoefficientOperator_contDiff (α : ℝ) (base : C(K,E)) (f : E → F)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (fun u : HolderSpace K E α => sectionCLM (superposeBCF
      (compactCoefficient (fderiv ℝ f) (hf.continuous_fderiv (by simp)) (hc.fderiv ℝ))
      (baseSegment base) (segmentSection (holderValue α u)))) := by
  simpa only [Function.comp_def, sectionOperatorCLM_apply] using
    (sectionOperatorCLM (K := OffDiagonal K × UnitTime) (E := E) (F := F)).contDiff.comp
      (profileCoefficient_contDiff α base f hf hc)

omit [CompleteSpace F] in
theorem profilePostNear_contDiff (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (fun u : HolderSpace K E α => sectionMeanCLM (sectionCLM (superposeBCF
      (compactCoefficient (fderiv ℝ f) (hf.continuous_fderiv (by simp)) (hc.fderiv ℝ))
      (baseSegment base) (segmentSection (holderValue α u)))
      (differencePull (profileWeightedDifference α hα₀ hα₁ base hb u)))) :=
  (sectionMeanCLM (P := OffDiagonal K) (F := F)).contDiff.comp
    ((profileCoefficientOperator_contDiff α base f hf hc).clm_apply
      ((differencePull (K := K) (E := E)).contDiff.comp
        (profileWeightedDifference_contDiff α hα₀ hα₁ base hb)))

omit [CompleteSpace F] in
theorem profileValue_contDiff (α : ℝ) (base : C(K,E)) (f : E → F)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (fun u : HolderSpace K E α =>
      superposeBCF (compactCoefficient f hf.continuous hc) base (holderValue α u)) :=
  (compactSuperpose_contDiff hf hc base).comp (holderValue (K := K) (E := E) α).contDiff

omit [CompleteSpace F] in
theorem profilePostDifference_contDiff (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (profilePostDifference α hα₀ hα₁ base hb f hf hc) :=
  (profilePostNear_contDiff α hα₀ hα₁ base hb f hf hc).add
    ((scalarSectionCLM (E := F) (holderFarWeight α hα₀ hα₁ (K := K))).contDiff.comp
      (((pairLeft (K := K) F).contDiff.comp (profileValue_contDiff α base f hf hc)).sub
        ((pairRight (K := K) F).contDiff.comp (profileValue_contDiff α base f hf hc))))

theorem holderProfilePost_ambient_contDiff (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (fun u : HolderSpace K E α =>
      (holderProfilePost α hα₀ hα₁ base hb f hf hc u).val) :=
  (profileValue_contDiff α base f hf hc).prodMk
    (profilePostDifference_contDiff α hα₀ hα₁ base hb f hf hc)

theorem holderProfilePost_hasFDerivAt (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (u : HolderSpace K E α) :
    HasFDerivAt (holderProfilePost α hα₀ hα₁ base hb f hf hc)
      (holderCLM α (holderProfilePost α hα₀ hα₁ base hb (fderiv ℝ f)
        (hf.fderiv_right (by simp)) (hc.fderiv ℝ) u)) u := by
  apply holder_hasFDerivAt_of_ambient
  · exact ((holderProfilePost_ambient_contDiff α hα₀ hα₁ base hb f hf hc).differentiable (by simp)) u
  · have hdf := hf.fderiv_right (show (∞ : WithTop ℕ∞)+1≤∞ by simp)
    have hd := (superposeBCF_hasFDerivAt
      (compactCoefficient f hf.continuous hc)
      (compactCoefficient (fderiv ℝ f) hdf.continuous (hc.fderiv ℝ))
      (fun x => (hf.differentiable (by simp) x).hasFDerivAt)
      (hdf.continuous.uniformContinuous_of_tendsto_cocompact (hc.fderiv ℝ).is_zero_at_infty)
      base (holderValue α u)).comp u (holderValue α).hasFDerivAt
    convert hd using 1 <;> try rfl

theorem holderProfilePost_contDiff_nat (m : ℕ) (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ m (holderProfilePost α hα₀ hα₁ base hb f hf hc) := by
  induction m generalizing F with
  | zero =>
    apply contDiff_zero.mpr
    exact continuous_induced_rng.mpr
      (holderProfilePost_ambient_contDiff α hα₀ hα₁ base hb f hf hc).continuous
  | succ m ih =>
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun u => holderCLM α (holderProfilePost α hα₀ hα₁ base hb (fderiv ℝ f)
      (hf.fderiv_right (by simp)) (hc.fderiv ℝ) u),?_,
        holderProfilePost_hasFDerivAt α hα₀ hα₁ base hb f hf hc⟩
    exact (holderOperatorCLM (K := K) (E := E) (F := F) α).contDiff.comp
      (ih (fderiv ℝ f) (hf.fderiv_right (by simp)) (hc.fderiv ℝ))

 

theorem holderProfilePost_contDiff (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (holderProfilePost α hα₀ hα₁ base hb f hf hc) :=
  contDiff_infty.mpr (fun m => holderProfilePost_contDiff_nat m α hα₀ hα₁ base hb f hf hc)

end HigherDimensionalBallPacking.Rigidity

 

namespace HigherDimensionalBallPacking.Rigidity
open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
universe u v
variable {K : Type u} [MetricSpace K]
variable {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance (G : Type v) [NormedAddCommGroup G] [NormedSpace ℝ G] (α : ℝ) :
    NormedAddCommGroup (HolderSpace K G α) := inferInstance
local instance (G : Type v) [NormedAddCommGroup G] [NormedSpace ℝ G] (α : ℝ) :
    NormedSpace ℝ (HolderSpace K G α) := inferInstance

def holderConst (α : ℝ) (c : E) : HolderSpace K E α :=
  ⟨(BoundedContinuousFunction.const K c,0),by intro p; simp⟩

@[simp] theorem holderConst_apply (α : ℝ) (c : E) (z : K) :
    holderValue α (holderConst α c) z = c := rfl

def holderLinearPost (α : ℝ) (T : E →L[ℝ] F) : HolderSpace K E α →L[ℝ] HolderSpace K F α :=
  holderCLM α (holderConst α T)

@[simp] theorem holderLinearPost_apply (α : ℝ) (T : E →L[ℝ] F) (u : HolderSpace K E α) (z : K) :
    holderValue α (holderLinearPost α T u) z = T (holderValue α u z) := rfl

variable [CompleteSpace E]

def holderJSection (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (J : E → E →L[ℝ] E) (J₀ : E →L[ℝ] E) (hJ : ContDiff ℝ ∞ J)
    (hc : HasCompactSupport (fun x => J x-J₀))
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (u : HolderSpace K E α) : HolderSpace K (E →L[ℝ] E) α :=
  holderConst α J₀ + holderProfilePost α hα₀ hα₁ base hb (fun x => J x-J₀) (hJ.sub contDiff_const) hc u

@[simp] theorem holderJSection_apply (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (J : E → E →L[ℝ] E) (J₀ : E →L[ℝ] E) (hJ : ContDiff ℝ ∞ J)
    (hc : HasCompactSupport (fun x => J x-J₀))
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (u : HolderSpace K E α) (z : K) :
    holderValue α (holderJSection α hα₀ hα₁ J J₀ hJ hc base hb u) z =
      J (base z+holderValue α u z) := by
  change J₀+(J (base z+holderValue α u z)-J₀) = _
  abel

theorem holderJSection_contDiff (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (J : E → E →L[ℝ] E) (J₀ : E →L[ℝ] E) (hJ : ContDiff ℝ ∞ J)
    (hc : HasCompactSupport (fun x => J x-J₀))
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base) :
    ContDiff ℝ ∞ (holderJSection α hα₀ hα₁ J J₀ hJ hc base hb) :=
  contDiff_const.add (holderProfilePost_contDiff α hα₀ hα₁ base hb (fun x => J x-J₀)
    (hJ.sub contDiff_const) hc)

def holderJetEval (α : ℝ) (w : ℂ) :
    HolderSpace K (ℂ →L[ℝ] E) α →L[ℝ] HolderSpace K E α :=
  holderLinearPost α ((ContinuousLinearMap.apply ℝ E) w)

omit [CompleteSpace E] in
@[simp] theorem holderJetEval_apply (α : ℝ) (w : ℂ)
    (A : HolderSpace K (ℂ →L[ℝ] E) α) (z : K) :
    holderValue α (holderJetEval α w A) z = holderValue α A z w := rfl

def holderCRJet (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (J : E → E →L[ℝ] E) (J₀ : E →L[ℝ] E) (hJ : ContDiff ℝ ∞ J)
    (hc : HasCompactSupport (fun x => J x-J₀))
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (p : HolderSpace K E α × HolderSpace K (ℂ →L[ℝ] E) α) : HolderSpace K E α :=
  holderJetEval α Complex.I p.2 -
    holderCLM α (holderJSection α hα₀ hα₁ J J₀ hJ hc base hb p.1) (holderJetEval α 1 p.2)

@[simp] theorem holderCRJet_apply (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (J : E → E →L[ℝ] E) (J₀ : E →L[ℝ] E) (hJ : ContDiff ℝ ∞ J)
    (hc : HasCompactSupport (fun x => J x-J₀))
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (p : HolderSpace K E α × HolderSpace K (ℂ →L[ℝ] E) α) (z : K) :
    holderValue α (holderCRJet α hα₀ hα₁ J J₀ hJ hc base hb p) z =
      holderValue α p.2 z Complex.I - J (base z+holderValue α p.1 z) (holderValue α p.2 z 1) := by
  change holderValue α p.2 z Complex.I -
    holderValue α (holderJSection α hα₀ hα₁ J J₀ hJ hc base hb p.1) z (holderValue α p.2 z 1) = _
  rw [holderJSection_apply]

theorem holderCRJet_contDiff (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (J : E → E →L[ℝ] E) (J₀ : E →L[ℝ] E) (hJ : ContDiff ℝ ∞ J)
    (hc : HasCompactSupport (fun x => J x-J₀))
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base) :
    ContDiff ℝ ∞ (holderCRJet α hα₀ hα₁ J J₀ hJ hc base hb) := by
  have hop : ContDiff ℝ ∞ (fun u : HolderSpace K E α =>
      holderCLM α (holderJSection α hα₀ hα₁ J J₀ hJ hc base hb u)) :=
    (holderOperatorCLM (K := K) (E := E) (F := E) α).contDiff.comp
      (holderJSection_contDiff α hα₀ hα₁ J J₀ hJ hc base hb)
  exact ((holderJetEval (K := K) (E := E) α Complex.I).contDiff.comp contDiff_snd).sub
    ((hop.comp contDiff_fst).clm_apply ((holderJetEval (K := K) (E := E) α 1).contDiff.comp contDiff_snd))

 
def realAffineProfile (c : E) (A : ℂ →L[ℝ] E) : C(ℂ,E) :=
  ⟨fun z => c+A z,continuous_const.add A.continuous⟩

omit [CompleteSpace E] in
@[simp] theorem realAffineProfile_apply (c : E) (A : ℂ →L[ℝ] E) (z : ℂ) :
    realAffineProfile c A z = c+A z := rfl

omit [CompleteSpace E] in
theorem realAffineProfile_lipschitz (c : E) (A : ℂ →L[ℝ] E) :
    LipschitzWith ‖A‖₊ (realAffineProfile c A) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (c+A x) (c+A y) ≤ ‖A‖*dist x y
  rw [dist_add_left,dist_eq_norm,← map_sub,dist_eq_norm]
  exact A.le_opNorm (x-y)

local instance (α : ℝ) : NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance (α : ℝ) : NormedSpace ℝ (C1HolderSpace E α) := inferInstance

def c1HolderAffineJet (α : ℝ) (A : ℂ →L[ℝ] E) (u : C1HolderSpace E α) :
    HolderSpace ℂ E α × HolderSpace ℂ (ℂ →L[ℝ] E) α :=
  (c1HolderValue α u,holderConst α A+c1HolderDeriv α u)

theorem c1HolderAffineJet_contDiff (α : ℝ) (A : ℂ →L[ℝ] E) :
    ContDiff ℝ ∞ (c1HolderAffineJet α A) :=
  (c1HolderValue (E := E) α).contDiff.prodMk
    (contDiff_const.add (c1HolderDeriv (E := E) α).contDiff)

def c1HolderAffineCurve (α : ℝ) (c : E) (A : ℂ →L[ℝ] E) (u : C1HolderSpace E α) : ℂ → E :=
  fun z => c+A z+holderValue α (c1HolderValue α u) z

theorem c1HolderAffineCurve_hasFDerivAt (α : ℝ) (c : E) (A : ℂ →L[ℝ] E)
    (u : C1HolderSpace E α) (z : ℂ) :
    HasFDerivAt (c1HolderAffineCurve α c A u) (A+holderValue α (c1HolderDeriv α u) z) z :=
  (A.hasFDerivAt.const_add c).add (c1Holder_hasFDerivAt α u z)

@[simp] theorem c1HolderAffineCurve_fderiv (α : ℝ) (c : E) (A : ℂ →L[ℝ] E)
    (u : C1HolderSpace E α) (z : ℂ) :
    fderiv ℝ (c1HolderAffineCurve α c A u) z = A+holderValue α (c1HolderDeriv α u) z :=
  (c1HolderAffineCurve_hasFDerivAt α c A u z).fderiv

def c1HolderCR (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (J : E → E →L[ℝ] E) (J₀ : E →L[ℝ] E) (hJ : ContDiff ℝ ∞ J)
    (hc : HasCompactSupport (fun x => J x-J₀)) (c : E) (A : ℂ →L[ℝ] E)
    (u : C1HolderSpace E α) : HolderSpace ℂ E α :=
  holderCRJet α hα₀ hα₁ J J₀ hJ hc (realAffineProfile c A) (realAffineProfile_lipschitz c A)
    (c1HolderAffineJet α A u)

theorem c1HolderCR_contDiff (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (J : E → E →L[ℝ] E) (J₀ : E →L[ℝ] E) (hJ : ContDiff ℝ ∞ J)
    (hc : HasCompactSupport (fun x => J x-J₀)) (c : E) (A : ℂ →L[ℝ] E) :
    ContDiff ℝ ∞ (c1HolderCR α hα₀ hα₁ J J₀ hJ hc c A) :=
  (holderCRJet_contDiff α hα₀ hα₁ J J₀ hJ hc (realAffineProfile c A)
    (realAffineProfile_lipschitz c A)).comp (c1HolderAffineJet_contDiff α A)

 

theorem c1HolderCR_apply (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (J : E → E →L[ℝ] E) (J₀ : E →L[ℝ] E) (hJ : ContDiff ℝ ∞ J)
    (hc : HasCompactSupport (fun x => J x-J₀)) (c : E) (A : ℂ →L[ℝ] E)
    (u : C1HolderSpace E α) (z : ℂ) :
    holderValue α (c1HolderCR α hα₀ hα₁ J J₀ hJ hc c A u) z =
      fderiv ℝ (c1HolderAffineCurve α c A u) z Complex.I -
        J (c1HolderAffineCurve α c A u z) (fderiv ℝ (c1HolderAffineCurve α c A u) z 1) := by
  rw [c1HolderAffineCurve_fderiv]
  exact holderCRJet_apply α hα₀ hα₁ J J₀ hJ hc (realAffineProfile c A)
    (realAffineProfile_lipschitz c A) (c1HolderAffineJet α A u) z

end HigherDimensionalBallPacking.Rigidity

end

end OAI
