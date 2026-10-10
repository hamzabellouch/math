import Mathlib
import OAI.Geometry.BallPacking.Necessity.DensityResidual
import OAI.Geometry.BallPacking.Necessity.OrbitRegularity

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
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap _root_.OAI.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity FramedCR
local instance densityRegularHGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance densityRegularHSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance
local instance densityRegularCGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) :
    NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance densityRegularCSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) :
    NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance densityRegularCompactGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance densityRegularCompactSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

 theorem densityCurve_deriv_one {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) (z : ℂ) :
    fderiv ℝ (densityCurve p q R g) z 1=densitySlope p q R g+
      holderValue ((1:ℝ)/3) (c1HolderDeriv ((1:ℝ)/3) (compactCRInverse R g)) z 1 := by
  rw [densityCurve_eq_profile,c1HolderAffineCurve_fderiv]
  change (1:ℂ) • densitySlope p q R g+_=_
  rw [one_smul]
  rfl

 theorem densityCurve_C1_curl {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) (J : Phase n → End n)
    (hCR : ∀ z, PseudoHolomorphicAt J (densityCurve p q R g) z) (z : ℂ) :
    holderValue ((1:ℝ)/3) (c1StandardCurl (compactCRInverse R g)) z=
      (J (densityCurve p q R g z)-standardJ n)
        (densitySlope p q R g+holderValue ((1:ℝ)/3) (c1HolderDeriv ((1:ℝ)/3) (compactCRInverse R g)) z 1) := by
  have hv : holderValue ((1:ℝ)/3) (c1StandardCurl (compactCRInverse R g)) z=compactHolderValue R g z := by
    rw [c1StandardCurl_value]
    exact compactCRInverse_rightInverse R g z
  rw [hv,←densityCurve_deriv_one p q R g z,←densityCurve_curl p q R g z]
  have he := (hCR z).2 (1:ℂ)
  simp only [mul_one] at he
  unfold standardCurl
  rw [he]
  rfl

 theorem densityCurve_regular {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) (ha : densitySlope p q R g≠0)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x)) (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hCR : ∀ z, PseudoHolomorphicAt J (densityCurve p q R g) z) :
    ContDiff ℝ ∞ (densityCurve p q R g) := by
  let v := compactCRInverse R g
  let c := p-compactCRInverseValue R g 0
  let a := densitySlope p q R g
  have he : densityCurve p q R g=c1HolderAffineCurve ((1:ℝ)/3) c (affineSlope a) v :=
    densityCurve_eq_profile p q R g
  have hcurl (z : ℂ) : holderValue ((1:ℝ)/3) (c1StandardCurl v) z=
      (J (c1HolderAffineCurve ((1:ℝ)/3) c (affineSlope a) v z)-standardJ n)
        (a+holderValue ((1:ℝ)/3) (c1HolderDeriv ((1:ℝ)/3) v) z 1) := by
    rw [←he]
    exact densityCurve_C1_curl p q R g J hCR z
  have hv := affine_c1_regular (fun x => J x-standardJ n) (hJs.sub contDiff_const) hc
    (fun x => by rw [add_comm,sub_add_cancel]; exact hJ x) c a ha v hcurl
    (compactCRInverse_tendsto_zero R g)
  rw [he]
  exact (contDiff_const.add (affineSlope a).contDiff).add hv

 theorem densityCurve_affineLine {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) (ha : densitySlope p q R g≠0)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x)) (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hCR : ∀ z, PseudoHolomorphicAt J (densityCurve p q R g) z) :
    AffineLineCurve J p q (densityCurve p q R g) :=
  ⟨densityCurve_regular p q R g ha J hJs hJ hc hCR,hCR,densityCurve_zero p q R g,
    densityCurve_one p q R g,densitySlope p q R g,ha,densityCurve_leading p q R g⟩

 theorem densityResidual_zero_affineLine {n : ℕ} (p q : Phase n) (R : ℝ)
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x)) (hJc : HasCompactSupport (fun x => J x-standardJ n))
    (he : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, A (t,x)=lineHomotopy J t x-standardJ n)
    (y : ℝ × CompactHolderSpace (Phase n) R) (hy : y.1∈Icc (0:ℝ) 1)
    (ha : densitySlope p q R y.2≠0) (hz : densityResidual p q R A hA hc y=0) :
    AffineLineCurve (lineHomotopy J y.1) p q (densityCurve p q R y.2) := by
  apply densityCurve_affineLine p q R y.2 ha
  · rw [contDiff_iff_contDiffAt]
    intro x
    exact (lineHomotopy_contDiffAt hJs hJ (y := (y.1,x)) hy).comp x
      (contDiffAt_const.prodMk contDiffAt_id)
  · exact lineHomotopy_compatible hJ hy
  · exact lineHomotopy_compact hJc hy
  · exact (densityResidual_zero_iff p q R A hA hc J hJ he y hy).mp hz

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
local instance densityExteriorGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) : NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance densityExteriorSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) : NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

 theorem densityCurve_lower_bound {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) (z : ℂ) :
    ‖z‖*‖densitySlope p q R g‖ ≤ ‖densityCurve p q R g z‖+densityAffineSize p R g := by
  have he : z • densitySlope p q R g=densityCurve p q R g z-(p-compactCRInverseValue R g 0)-compactCRInverseValue R g z := by
    rw [densityCurve_eq_profile]
    change z • densitySlope p q R g=((p-compactCRInverseValue R g 0)+z • densitySlope p q R g+compactCRInverseValue R g z)-(p-compactCRInverseValue R g 0)-compactCRInverseValue R g z
    abel
  have hn : ‖z • densitySlope p q R g‖≤‖densityCurve p q R g z‖+‖p-compactCRInverseValue R g 0‖+‖compactCRInverseValue R g z‖ := by
    rw [he]
    have h1 := norm_sub_le (densityCurve p q R g z-(p-compactCRInverseValue R g 0)) (compactCRInverseValue R g z)
    have h2 := norm_sub_le (densityCurve p q R g z) (p-compactCRInverseValue R g 0)
    linarith
  rw [norm_smul] at hn
  have hb := (compactCRInverseValue R g).norm_coe_le_norm z
  unfold densityAffineSize
  linarith

 def goodDensities {n : ℕ} (p q : Phase n) (R m M : ℝ) : Set (CompactHolderSpace (Phase n) R) :=
  {g | m < ‖densitySlope p q R g‖ ∧ densityAffineSize p R g < M}

 theorem goodDensities_isOpen {n : ℕ} (p q : Phase n) (R m M : ℝ) : IsOpen (goodDensities p q R m M) :=
  (isOpen_lt continuous_const (densitySlope_continuous p q R).norm).inter
    (isOpen_lt (densityAffineSize_continuous p R) continuous_const)

 theorem goodDensities_slope_ne {n : ℕ} (p q : Phase n) (R m M : ℝ) (hm : 0 < m)
    (g : CompactHolderSpace (Phase n) R) (hg : g∈goodDensities p q R m M) : densitySlope p q R g≠0 :=
  norm_pos_iff.mp (hm.trans hg.1)

 theorem goodDensities_exterior {n : ℕ} (p q : Phase n) (R m M C S : ℝ) (hm : 0 < m)
    (hS : 0 < S) (hSC : M+C≤S*m)
    (A : ℝ × Phase n → End n) (hAc : ∀ y∈tsupport A, ‖y‖≤C)
    (t : ℝ) (g : CompactHolderSpace (Phase n) R) (hg : g∈goodDensities p q R m M)
    (z : ℂ) (hz : S<‖z‖) : A (t,densityCurve p q R g z)=0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hy
  have hb : ‖densityCurve p q R g z‖≤C := (_root_.norm_snd_le _).trans (hAc _ hy)
  have hl := densityCurve_lower_bound p q R g z
  have hmul : S*m<‖z‖*‖densitySlope p q R g‖ :=
    mul_lt_mul hz hg.1.le hm (le_of_lt (hS.trans hz))
  linarith [hg.2]

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
local instance compactMapHGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) : NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance compactMapHSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) : NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance
local instance compactMapCGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) : NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance compactMapCSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) : NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance compactMapCompactGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) : NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance compactMapCompactSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) : NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

 def cutoffValues {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b : ContDiffBump (0:ℂ)) : C1HolderSpace E ((1:ℝ)/3) →L[ℝ] HolderSpace ℂ E ((1:ℝ)/3) :=
  c1LowerOrderCLM (holderLinearPost ((1:ℝ)/3) (ContinuousLinearMap.lsmul ℝ ℝ)
    (holderSourceCutoff ((1:ℝ)/3) (by norm_num) (by norm_num) b))

 theorem cutoffValues_value {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b : ContDiffBump (0:ℂ)) (v : C1HolderSpace E ((1:ℝ)/3)) (z : ℂ) :
    holderValue ((1:ℝ)/3) (cutoffValues b v) z=b z • holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) v) z := rfl

 theorem cutoffValues_compact {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] (b : ContDiffBump (0:ℂ)) : IsCompactOperator (cutoffValues (E := E) b) := by
  apply c1LowerOrderCLM_compact_holder b.rOut
  intro z hz
  change b z • (ContinuousLinearMap.id ℝ E)=0
  rw [b.zero_of_le_dist (by simpa using hz.le),zero_smul]

 abbrev ResponseCoords (n : ℕ) := (ℝ × Phase n × Phase n) × HolderSpace ℂ (Phase n) ((1:ℝ)/3)

 def responseCoords {n : ℕ} (B : ContDiffBump (0:ℂ)) (p q : Phase n) (R : ℝ)
    (y : ℝ × CompactHolderSpace (Phase n) R) : ResponseCoords n :=
  ((y.1,p-compactCRInverseValue R y.2 0,densitySlope p q R y.2),cutoffValues B (compactCRInverse R y.2))

 theorem responseCoords_contDiff {n : ℕ} (B : ContDiffBump (0:ℂ)) (p q : Phase n) (R : ℝ) :
    ContDiff ℝ ∞ (responseCoords B p q R) := by
  have h0 : ContDiff ℝ ∞ (fun y : ℝ × CompactHolderSpace (Phase n) R => compactCRInverseValue R y.2 0) :=
    (((c1HolderEval ((1:ℝ)/3) 0).comp (compactCRInverse (E := Phase n) R)).contDiff).comp contDiff_snd
  have ha : ContDiff ℝ ∞ (fun y : ℝ × CompactHolderSpace (Phase n) R => densitySlope p q R y.2) :=
    (densitySlope_contDiff p q R).comp contDiff_snd
  exact (contDiff_fst.prodMk ((contDiff_const.sub h0).prodMk ha)).prodMk
    (((cutoffValues B).comp (compactCRInverse (E := Phase n) R)).contDiff.comp contDiff_snd)

 def responseProfile {n : ℕ} (B : ContDiffBump (0:ℂ)) (x : ResponseCoords n) :
    HolderSpace ℂ (ℝ × Phase n) ((1:ℝ)/3) :=
  holderConstantCLM ((1:ℝ)/3) (x.1.1,0)+holderLinearPost ((1:ℝ)/3) (ContinuousLinearMap.inr ℝ ℝ (Phase n))
    (holderCutoffAffine ((1:ℝ)/3) (by norm_num) (by norm_num) B (x.1.2.1,affineSlope x.1.2.2)+x.2)

 theorem responseProfile_contDiff {n : ℕ} (B : ContDiffBump (0:ℂ)) :
    ContDiff ℝ ∞ (responseProfile (n := n) B) := by
  have hc := (holderConstantCLM (E := ℝ × Phase n) ((1:ℝ)/3)).contDiff.comp
    ((contDiff_fst.fst : ContDiff ℝ ∞ (fun x : ResponseCoords n => x.1.1)).prodMk (contDiff_const (c := (0:Phase n))))
  have ha : ContDiff ℝ ∞ (fun x : ResponseCoords n => affineSlope x.1.2.2) :=
    ((ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] Phase n →L[ℝ] Phase n).flip).contDiff.comp contDiff_fst.snd.snd
  have ht := (holderCutoffAffine_contDiff ((1:ℝ)/3) (by norm_num) (by norm_num) B).comp
    ((contDiff_fst.snd.fst : ContDiff ℝ ∞ (fun x : ResponseCoords n => x.1.2.1)).prodMk ha)
  let L : HolderSpace ℂ (Phase n) ((1:ℝ)/3) →L[ℝ] HolderSpace ℂ (ℝ × Phase n) ((1:ℝ)/3) :=
    holderLinearPost ((1:ℝ)/3) (ContinuousLinearMap.inr ℝ ℝ (Phase n))
  exact hc.add (L.contDiff.comp (ht.add contDiff_snd))

 def responseCoefficient {n : ℕ} (b B : ContDiffBump (0:ℂ))
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (x : ResponseCoords n) : HolderSpace ℂ (End n) ((1:ℝ)/3) :=
  (cutoffCompact b (holderPost ((1:ℝ)/3) (by norm_num) A hA hc (responseProfile B x))).1

 theorem responseCoefficient_contDiff {n : ℕ} (b B : ContDiffBump (0:ℂ))
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) :
    ContDiff ℝ ∞ (responseCoefficient b B A hA hc) := by
  exact ((compactHolderSubmodule (E := End n) b.rOut).subtypeL.comp (cutoffCompact b)).contDiff.comp
    ((holderPost_contDiff ((1:ℝ)/3) (by norm_num) A hA hc).comp (responseProfile_contDiff B))

 theorem responseCoefficient_value {n : ℕ} (b B : ContDiffBump (0:ℂ)) (hbB : b.rOut≤B.rIn)
    (p q : Phase n) (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (y : ℝ × CompactHolderSpace (Phase n) b.rOut) (z : ℂ) :
    holderValue ((1:ℝ)/3) (responseCoefficient b B A hA hc (responseCoords B p q b.rOut y)) z=
      b z • A (y.1,densityCurve p q b.rOut y.2 z) := by
  change b z • holderValue ((1:ℝ)/3) (holderPost ((1:ℝ)/3) (by norm_num) A hA hc _) z=_
  rw [holderPost_apply]
  by_cases hz : b z=0
  · rw [hz]
    ext v
    simp
  have hzz : ‖z‖≤b.rOut := by
    by_contra hn
    exact hz (b.zero_of_le_dist (by simpa using (le_of_not_ge hn)))
  have hB : B z=1 := B.one_of_mem_closedBall (by simpa using hzz.trans hbB)
  congr 2
  rw [responseProfile,map_add,BoundedContinuousFunction.add_apply,holderConstantCLM_value,
    holderLinearPost_apply, map_add, BoundedContinuousFunction.add_apply, holderCutoffAffine_apply]
  change (y.1,0)+(ContinuousLinearMap.inr ℝ ℝ (Phase n))
    (B z • ((p-compactCRInverseValue b.rOut y.2 0)+affineSlope (densitySlope p q b.rOut y.2) z)+
      B z • compactCRInverseValue b.rOut y.2 z)=_
  rw [hB,one_smul,one_smul]
  apply Prod.ext
  · simp
  · simp only [Prod.snd_add, ContinuousLinearMap.inr_apply, zero_add]
    rw [densityCurve_eq_profile]
    rfl

end HigherDimensionalBallPacking.Rigidity

end

end OAI
