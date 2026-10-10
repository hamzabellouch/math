import Mathlib
import OAI.Geometry.BallPacking.Necessity.CompactContinuation
import OAI.Geometry.BallPacking.Necessity.DensityMaps

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

open scoped ContDiff Topology
open Set Filter Function
namespace TwoPointContinuation
 theorem LocallyPrecompact.comp_contDiffAt {X Y Z : Type*} [TopologicalSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : X → Y} {x : X} (hf : LocallyPrecompact f x) (hfc : ContinuousAt f x)
    (g : Y → Z) (hg : ContDiffAt ℝ ∞ g (f x)) : LocallyPrecompact (g∘f) x := by
  obtain ⟨U,hU,hgU⟩ := contDiffAt_zero.mp (hg.of_le (by simp : (0:ℕ∞ω)≤∞))
  obtain ⟨V,hVU,hVo,hxV⟩ := mem_nhds_iff.mp hU
  exact hf.comp hfc g V hVo (hgU.mono hVU) hxV
end TwoPointContinuation
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity TwoPointContinuation
local instance responseLocalGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) : NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance responseLocalSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) : NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance
local instance responseLocalCompactGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) : NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance responseLocalCompactSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) : NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

 theorem responseCoords_locallyPrecompact {n : ℕ} (B : ContDiffBump (0:ℂ)) (p q : Phase n) (R : ℝ)
    (y : ℝ × CompactHolderSpace (Phase n) R) : LocallyPrecompact (responseCoords B p q R) y := by
  let L := (cutoffValues (E := Phase n) B).comp ((compactCRInverse R).comp (ContinuousLinearMap.snd ℝ ℝ _))
  have hL : IsCompactOperator L := (cutoffValues_compact B).comp_clm _
  have hf := locallyPrecompact_finite (fun y : ℝ × CompactHolderSpace (Phase n) R => (responseCoords B p q R y).1) y
    (responseCoords_contDiff B p q R).continuous.continuousAt.fst
  exact hf.prod (locallyPrecompact_compactLinear L hL y)

 def responseFactor {n : ℕ} (b B : ContDiffBump (0:ℂ))
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (x : ResponseCoords n) : CompactHolderSpace (Phase n) b.rOut :=
  frozenResponse b (responseCoefficient b B A hA hc x,x.1.2.2)

 def densityResponse {n : ℕ} (b B : ContDiffBump (0:ℂ)) (p q : Phase n)
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (y : ℝ × CompactHolderSpace (Phase n) b.rOut) : CompactHolderSpace (Phase n) b.rOut :=
  responseFactor b B A hA hc (responseCoords B p q b.rOut y)

 theorem responseFactor_contDiffAt {n : ℕ} (b B : ContDiffBump (0:ℂ))
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (x : ResponseCoords n) (hi : (cutoffFrozen b (responseCoefficient b B A hA hc x)).IsInvertible) :
    ContDiffAt ℝ ∞ (responseFactor b B A hA hc) x := by
  have hp : ContDiffAt ℝ ∞ (fun y : ResponseCoords n => (responseCoefficient b B A hA hc y,y.1.2.2)) x :=
    (responseCoefficient_contDiff b B A hA hc).contDiffAt.prodMk contDiffAt_fst.snd.snd
  exact (frozenResponse_contDiffAt (E := Phase n) b (responseCoefficient b B A hA hc x,x.1.2.2) hi).comp x hp

 theorem densityResponse_contDiffAt {n : ℕ} (b B : ContDiffBump (0:ℂ)) (p q : Phase n)
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (y : ℝ × CompactHolderSpace (Phase n) b.rOut)
    (hi : (cutoffFrozen b (responseCoefficient b B A hA hc (responseCoords B p q b.rOut y))).IsInvertible) :
    ContDiffAt ℝ ∞ (densityResponse b B p q A hA hc) y :=
  (responseFactor_contDiffAt b B A hA hc _ hi).comp y (responseCoords_contDiff B p q b.rOut).contDiffAt

 theorem densityResponse_locallyPrecompact {n : ℕ} (b B : ContDiffBump (0:ℂ)) (p q : Phase n)
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (y : ℝ × CompactHolderSpace (Phase n) b.rOut)
    (hi : (cutoffFrozen b (responseCoefficient b B A hA hc (responseCoords B p q b.rOut y))).IsInvertible) :
    LocallyPrecompact (densityResponse b B p q A hA hc) y :=
  (responseCoords_locallyPrecompact B p q b.rOut y).comp_contDiffAt
    (responseCoords_contDiff B p q b.rOut).continuous.continuousAt _
    (responseFactor_contDiffAt b B A hA hc _ hi)

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
local instance fixedDensityHGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) : NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance fixedDensityHSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) : NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance
local instance fixedDensityCGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) : NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance fixedDensityCSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) : NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance fixedDensityGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) : NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance fixedDensitySpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) : NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

 theorem responseCoefficient_uncut {n : ℕ} (b B : ContDiffBump (0:ℂ)) (hbB : b.rOut≤B.rIn)
    (p q : Phase n) (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (y : ℝ × CompactHolderSpace (Phase n) b.rOut)
    (hs : ∀ z : ℂ, b.rIn<‖z‖ → A (y.1,densityCurve p q b.rOut y.2 z)=0) (z : ℂ) :
    holderValue ((1:ℝ)/3) (responseCoefficient b B A hA hc (responseCoords B p q b.rOut y)) z=
      A (y.1,densityCurve p q b.rOut y.2 z) := by
  rw [responseCoefficient_value b B hbB p q A hA hc y z]
  by_cases hz : ‖z‖≤b.rIn
  · rw [b.one_of_mem_closedBall (by simpa using hz),one_smul]
  · rw [hs z (lt_of_not_ge hz)]
    ext v
    simp

 theorem responseCoefficient_invertible {n : ℕ} (b B : ContDiffBump (0:ℂ)) (hbB : b.rOut≤B.rIn)
    (p q : Phase n) (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (he : ∀ t∈Icc (0:ℝ) 1, ∀ x, A (t,x)=lineHomotopy J t x-standardJ n)
    (y : ℝ × CompactHolderSpace (Phase n) b.rOut) (hy : y.1∈Icc (0:ℝ) 1)
    (hs : ∀ z : ℂ, b.rIn<‖z‖ → A (y.1,densityCurve p q b.rOut y.2 z)=0) :
    (cutoffFrozen b (responseCoefficient b B A hA hAc (responseCoords B p q b.rOut y))).IsInvertible := by
  have hts : ContDiff ℝ ∞ (fun x => lineHomotopy J y.1 x-standardJ n) := by
    apply ContDiff.sub _ contDiff_const
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (lineHomotopy_contDiffAt hJs hJ (y := (y.1,x)) hy).comp x (contDiffAt_const.prodMk contDiffAt_id)
  let H := c1HolderAffineCompose ((1:ℝ)/3) (by norm_num) (by norm_num)
    (fun x => lineHomotopy J y.1 x-standardJ n) hts (lineHomotopy_compact hc hy)
    (p-compactCRInverseValue b.rOut y.2 0) (affineSlope (densitySlope p q b.rOut y.2)) (compactCRInverse b.rOut y.2)
  have hH (z : ℂ) : holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) H) z=
      A (y.1,densityCurve p q b.rOut y.2 z) := by
    rw [he _ hy,densityCurve_eq_profile]
    exact c1HolderAffineCompose_value _ _ _ _ _ _ _ _ _ z
  have hHeq : c1HolderValue ((1:ℝ)/3) H=responseCoefficient b B A hA hAc (responseCoords B p q b.rOut y) := by
    apply holderValue_injective
    apply BoundedContinuousFunction.ext
    intro z
    rw [hH,responseCoefficient_uncut b B hbB p q A hA hAc y hs]
  rw [←hHeq]
  apply cutoffFrozen_invertible b H
  · intro z hz
    rw [hH,hs z hz]
  · intro z
    rw [hH,he _ hy,add_comm,sub_add_cancel]
    exact lineHomotopy_compatible hJ hy _

 theorem densityFixedPoint_residual_zero {n : ℕ} (b B : ContDiffBump (0:ℂ)) (hbB : b.rOut≤B.rIn)
    (p q : Phase n) (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (y : ℝ × CompactHolderSpace (Phase n) b.rOut)
    (hs : ∀ z : ℂ, b.rIn<‖z‖ → A (y.1,densityCurve p q b.rOut y.2 z)=0)
    (hi : (cutoffFrozen b (responseCoefficient b B A hA hc (responseCoords B p q b.rOut y))).IsInvertible)
    (hfix : densityResponse b B p q A hA hc y=y.2) : densityResidual p q b.rOut A hA hc y=0 := by
  let H := responseCoefficient b B A hA hc (responseCoords B p q b.rOut y)
  have he : cutoffFrozen b H y.2=cutoffCompact b (holderCLM ((1:ℝ)/3) H (holderConstantCLM ((1:ℝ)/3) (densitySlope p q b.rOut y.2))) := by
    change (cutoffFrozen b H).inverse _=y.2 at hfix
    exact (hi.inverse_apply_eq.mp hfix).symm
  have hpoint (z : ℂ) : compactHolderValue b.rOut y.2 z=
      A (y.1,densityCurve p q b.rOut y.2 z) (fderiv ℝ (densityCurve p q b.rOut y.2) z 1) := by
    have hez := congrArg (fun g => compactHolderValue b.rOut g z) he
    rw [cutoffFrozen_value,cutoffCompact_value,holderCLM_apply,holderConstantCLM_value] at hez
    change compactHolderValue b.rOut y.2 z-b z • holderValue ((1:ℝ)/3) H z _=b z • holderValue ((1:ℝ)/3) H z _ at hez
    have hH := responseCoefficient_uncut b B hbB p q A hA hc y hs z
    change holderValue ((1:ℝ)/3) H z=_ at hH
    rw [hH] at hez
    by_cases hz : ‖z‖≤b.rIn
    · rw [b.one_of_mem_closedBall (by simpa using hz),one_smul,one_smul] at hez
      rw [densityCurve_deriv_one,map_add]
      have hd := (c1Holder_hasFDerivAt ((1:ℝ)/3) (compactCRInverse (E := Phase n) b.rOut y.2) z).fderiv
      change fderiv ℝ (compactCRInverseValue b.rOut y.2) z=_ at hd
      rw [hd] at hez
      exact sub_eq_iff_eq_add.mp hez
    · rw [hs z (lt_of_not_ge hz)] at hez ⊢
      simpa using hez
  apply holderValue_injective
  apply BoundedContinuousFunction.ext
  intro z
  change compactHolderValue b.rOut y.2 z-holderValue ((1:ℝ)/3)
    (holderCLM ((1:ℝ)/3) (densityCoefficient p q b.rOut A hA hc y)
      (holderJetEval ((1:ℝ)/3) 1 (densityJet p q b.rOut y.2))) z=0
  rw [holderCLM_apply,densityCoefficient_value,holderJetEval_apply,densityJet_value,hpoint]
  exact sub_self _

 theorem densityResponse_zero_time {n : ℕ} (b B : ContDiffBump (0:ℂ)) (hbB : b.rOut≤B.rIn)
    (p q : Phase n) (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (hzero : ∀ x, A (0,x)=0) (g : CompactHolderSpace (Phase n) b.rOut) :
    densityResponse b B p q A hA hc (0,g)=0 := by
  have hH : responseCoefficient b B A hA hc (responseCoords B p q b.rOut (0,g))=0 := by
    apply holderValue_injective
    apply BoundedContinuousFunction.ext
    intro z
    rw [responseCoefficient_value b B hbB p q A hA hc (0,g) z,hzero]
    change b z • (0 : End n)=0
    ext v
    simp
  unfold densityResponse responseFactor frozenResponse
  rw [hH]
  have hv (a : Phase n) : holderCLM ((1:ℝ)/3) (0:HolderSpace ℂ (End n) ((1:ℝ)/3)) (holderConstantCLM ((1:ℝ)/3) a)=0 := by
    apply holderValue_injective
    apply BoundedContinuousFunction.ext
    intro z
    change (0:End n) a=0
    rfl
  rw [hv,map_zero,map_zero]

end HigherDimensionalBallPacking.Rigidity

 

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity TwoPointContinuation
local instance actualDensityGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) : NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance actualDensitySpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) : NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

 theorem actual_affine_line_exists (n : ℕ) (hn : 3≤n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (hpq : p≠q) :
    ∃ u : ℂ → Phase n, AffineLineCurve J p q u := by
  obtain ⟨R₀,hR₀,hRc⟩ := homotopy_density_common_support n hn J hJs hJ hc hs p q hpq
  obtain ⟨m,M,hm,hM,hbounds⟩ := uniform_density_bounds n hn J hJs hJ hc hs p q hpq
  obtain ⟨A,hA,hAc,hAe⟩ := homotopy_coefficient_extension hJs hJ hc
  obtain ⟨C,hC⟩ := hAc.isBounded.exists_norm_le
  let S : ℝ := max R₀ ((M+C)/m)+1
  have hS₀ : R₀<S := lt_add_of_le_of_pos (le_max_left _ _) zero_lt_one
  have hS : 0<S := hR₀.trans hS₀
  have hSC : M+C≤S*m := by
    have hh : (M+C)/m≤S := (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
    exact (div_le_iff₀ hm).mp hh
  let b : ContDiffBump (0:ℂ) := ⟨S,S+1,hS,lt_add_one _⟩
  let B : ContDiffBump (0:ℂ) := ⟨S+2,S+3,by linarith,by linarith⟩
  have hbB : b.rOut≤B.rIn := by dsimp [b,B]; linarith
  let V := goodDensities p q b.rOut m M
  let K := Prod.snd '' affineHolderModuli J p q b.rOut
  let T := densityResponse b B p q A hA hAc
  have hV : IsOpen V := goodDensities_isOpen p q b.rOut m M
  have hK : IsCompact K := by
    apply IsCompact.image _ continuous_snd
    apply affineHolderModuli_isCompact n hn J hJs hJ hc hs p q hpq b.rOut
    intro t ht u hu z hz
    apply hRc t ht u hu z
    exact hS₀.trans (lt_trans (by dsimp [b]; exact lt_add_one _) hz)
  have hKV : K⊆V := by
    rintro g ⟨y,hy,rfl⟩
    exact hbounds b.rOut y hy
  have h0 : 0∈K := ⟨(0,0),zero_mem_affineHolderModuli J hJ p q hpq b.rOut,rfl⟩
  have houtside (t : ℝ) (g : CompactHolderSpace (Phase n) b.rOut) (hg : g∈V) :
      ∀ z : ℂ, b.rIn<‖z‖ → A (t,densityCurve p q b.rOut g z)=0 :=
    goodDensities_exterior p q b.rOut m M C S hm hS hSC A hC t g hg
  have hinv (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (g : CompactHolderSpace (Phase n) b.rOut) (hg : g∈V) :
      (cutoffFrozen b (responseCoefficient b B A hA hAc (responseCoords B p q b.rOut (t,g)))).IsInvertible :=
    responseCoefficient_invertible b B hbB p q A hA hAc J hJs hJ hc hAe (t,g) ht (houtside t g hg)
  have hline (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (g : CompactHolderSpace (Phase n) b.rOut)
      (hg : g∈V) (he : T (t,g)=g) : AffineLineCurve (lineHomotopy J t) p q (densityCurve p q b.rOut g) := by
    apply densityResidual_zero_affineLine p q b.rOut A hA hAc J hJs hJ hc hAe (t,g) ht
      (goodDensities_slope_ne p q b.rOut m M hm g hg)
    exact densityFixedPoint_residual_zero b B hbB p q A hA hAc (t,g) (houtside t g hg) (hinv t ht g hg) he
  obtain ⟨g,hg,hfix⟩ := local_degree_continuation T V hV
    (fun t ht g hg => (densityResponse_contDiffAt b B p q A hA hAc (t,g) (hinv t ht g hg)).continuousAt)
    (fun g _ => densityResponse_zero_time b B hbB p q A hA hAc (by
      intro x
      rw [hAe 0 (by norm_num) x,lineHomotopy_zero hJ,sub_self]) g)
    K hK hKV h0
    (by
      intro t ht g hg he
      refine ⟨(t,g),?_,rfl⟩
      rw [affineHolderModuli_iff]
      exact ⟨ht,hline t ht g hg he⟩)
    (fun t ht g hg => densityResponse_locallyPrecompact b B p q A hA hAc (t,g) (hinv t ht g (hKV hg)))
  refine ⟨densityCurve p q b.rOut g,?_⟩
  convert hline 1 (by norm_num) g hg hfix using 1
  funext x
  exact (lineHomotopy_one hJ x).symm

end HigherDimensionalBallPacking.Rigidity

end

end OAI
