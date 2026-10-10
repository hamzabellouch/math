import Mathlib
import OAI.Geometry.BallPacking.Necessity.DensityBounds

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
namespace HigherDimensionalBallPacking.Rigidity

 theorem contDiffAt_interpolateJ_of_invertible
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {J : E → End n} {t : E → ℝ} {x : E}
    (hJs : ContDiffAt ℝ ∞ J x) (hts : ContDiffAt ℝ ∞ t x)
    (hQi : (cayleyP (J x) (1-t x) (1+t x)).IsInvertible) :
    ContDiffAt ℝ ∞ (fun y => interpolateJ (J y) (t y)) x := by
  have hA : ContDiffAt ℝ ∞ (fun y => relativeOperator (J y)) x :=
    (contDiffAt_const.clm_comp hJs).neg
  have ha : ContDiffAt ℝ ∞ (fun y => 1+t y) x := contDiffAt_const.add hts
  have hb : ContDiffAt ℝ ∞ (fun y => 1-t y) x := contDiffAt_const.sub hts
  have hP : ContDiffAt ℝ ∞ (fun y => cayleyP (J y) (1+t y) (1-t y)) x :=
    (ha.smul hA).add (hb.smul contDiffAt_const)
  have hQ : ContDiffAt ℝ ∞ (fun y => cayleyP (J y) (1-t y) (1+t y)) x :=
    (hb.smul hA).add (ha.smul contDiffAt_const)
  have hI : ContDiffAt ℝ ∞ (fun y => (cayleyP (J y) (1-t y) (1+t y)).inverse) x :=
    ContDiffAt.comp x (g := ContinuousLinearMap.inverse)
      (ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse (n := ∞) hQi) hQ
  exact contDiffAt_const.clm_comp (hP.clm_comp hI)

 theorem homotopy_coefficient_extension {n : ℕ} {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n)) :
    ∃ A : ℝ × Phase n → End n, ContDiff ℝ ∞ A ∧ HasCompactSupport A ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∀ x, A (t,x)=lineHomotopy J t x-standardJ n := by
  let Q : ℝ × Phase n → End n := fun y => cayleyP (J y.2) (1-y.1) (1+y.1)
  have hQs : ContDiff ℝ ∞ Q := by
    exact ((contDiff_const.sub contDiff_fst).smul
      (contDiff_const.clm_comp (hJs.comp contDiff_snd)).neg).add
        ((contDiff_const.add contDiff_fst).smul contDiff_const)
  let K : Set (ℝ × Phase n) := Icc (0:ℝ) 1 ×ˢ tsupport (fun x => J x-standardJ n)
  let U : Set (ℝ × Phase n) := {y | IsUnit (Q y)}
  have hKo : IsCompact K := isCompact_Icc.prod hc
  have hUo : IsOpen U := Units.isOpen.preimage hQs.continuous
  have hKU : K ⊆ U := by
    intro y hy
    obtain ⟨e,he⟩ := cayleyP_invertible (hJ y.2)
      (show 0 < 1+y.1 by linarith [hy.1.1]) (show 0 ≤ 1-y.1 by linarith [hy.1.2])
    apply ContinuousLinearMap.isUnit_iff_bijective.mpr
    change Bijective (cayleyP (J y.2) (1-y.1) (1+y.1))
    rw [←he]
    exact e.bijective
  obtain ⟨χ,hχs,hχc,hχU,hχ1,hχrange⟩ := exists_smooth_cutoff hKo hUo hKU
  let A : ℝ × Phase n → End n := fun y => χ y • (lineHomotopy J y.1 y.2-standardJ n)
  have hAs : ContDiff ℝ ∞ A := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ U
    · obtain ⟨e,he⟩ := hy
      have hQi : (Q y).IsInvertible := ⟨ContinuousLinearEquiv.ofUnit e,by exact he⟩
      exact hχs.contDiffAt.smul ((contDiffAt_interpolateJ_of_invertible
        (hJs.contDiffAt.comp y contDiffAt_snd) contDiffAt_fst hQi).sub contDiffAt_const)
    · apply (contDiffAt_const (c := (0 : End n))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp (show y ∉ tsupport χ from fun h => hy (hχU h))] with z hz
      apply ContinuousLinearMap.ext
      intro v
      simp [A,hz]
  refine ⟨A,hAs,?_,?_⟩
  · apply hχc.of_isClosed_subset (isClosed_tsupport A)
    apply closure_mono
    intro y hy
    by_contra h
    apply hy
    simp only [mem_support,ne_eq,not_not] at h
    apply ContinuousLinearMap.ext
    intro v
    simp [A,h]
  · intro t ht x
    by_cases hx : x ∈ tsupport (fun x => J x-standardJ n)
    · have he : χ (t,x)=1 := (hχ1.self_of_nhdsSet) (t,x) ⟨ht,hx⟩
      simp only [A,he,one_smul]
    · have he : J x=standardJ n := sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun x => J x-standardJ n) hx)
      have hstd : lineHomotopy J t x=standardJ n := by
        change interpolateJ (J x) t=standardJ n
        rw [he,interpolateJ_standard ht]
      simp only [A,hstd,sub_self,smul_zero]


 

 

 

open scoped ContDiff Topology
open Set Filter Function
open HigherDimensionalBallPacking.Rigidity
local instance (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance
local instance (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) :
    NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) :
    NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

 def densityLinearSlope {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) : ℂ →L[ℝ] Phase n :=
  ((ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] Phase n →L[ℝ] Phase n).flip)
    (densitySlope p q R g)

 @[simp] theorem densityLinearSlope_apply {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) (z : ℂ) :
    densityLinearSlope p q R g z=z • densitySlope p q R g := rfl

 theorem densitySlope_contDiff {n : ℕ} (p q : Phase n) (R : ℝ) :
    ContDiff ℝ ∞ (densitySlope p q R) := by
  let C := compactCRInverse (E := Phase n) R
  have h0 : ContDiff ℝ ∞ (fun g : CompactHolderSpace (Phase n) R => compactCRInverseValue R g 0) := ((c1HolderEval ((1:ℝ)/3) (0:ℂ)).comp C).contDiff
  have h1 : ContDiff ℝ ∞ (fun g : CompactHolderSpace (Phase n) R => compactCRInverseValue R g 1) := ((c1HolderEval ((1:ℝ)/3) (1:ℂ)).comp C).contDiff
  exact contDiff_const.sub (h1.sub h0)

 theorem densityLinearSlope_contDiff {n : ℕ} (p q : Phase n) (R : ℝ) :
    ContDiff ℝ ∞ (densityLinearSlope p q R) :=
  ((ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] Phase n →L[ℝ] Phase n).flip).contDiff.comp
    (densitySlope_contDiff p q R)

 def timeDensityProfile {n : ℕ} (p q : Phase n) (R : ℝ)
    (y : ℝ × CompactHolderSpace (Phase n) R) :
    ((ℝ × Phase n) × (ℂ →L[ℝ] ℝ × Phase n)) × HolderSpace ℂ (ℝ × Phase n) ((1:ℝ)/3) :=
  (((y.1,p-compactCRInverseValue R y.2 0),
      (0 : ℂ →L[ℝ] ℝ).prod (densityLinearSlope p q R y.2)),
    holderLinearPost ((1:ℝ)/3) (ContinuousLinearMap.inr ℝ ℝ (Phase n))
      (c1HolderValue ((1:ℝ)/3) (compactCRInverse R y.2)))

 theorem timeDensityProfile_contDiff {n : ℕ} (p q : Phase n) (R : ℝ) :
    ContDiff ℝ ∞ (timeDensityProfile p q R) := by
  have h0 : ContDiff ℝ ∞ (fun y : ℝ × CompactHolderSpace (Phase n) R =>
      compactCRInverseValue R y.2 0) := (((c1HolderEval ((1:ℝ)/3) (0:ℂ)).comp
    (compactCRInverse (E := Phase n) R)).contDiff.comp contDiff_snd)
  have hv : ContDiff ℝ ∞ (fun y : ℝ × CompactHolderSpace (Phase n) R =>
      (timeDensityProfile p q R y).2) := ((holderLinearPost ((1:ℝ)/3) (ContinuousLinearMap.inr ℝ ℝ (Phase n))).comp
    ((c1HolderValue ((1:ℝ)/3)).comp (compactCRInverse (E := Phase n) R))).contDiff.comp contDiff_snd
  have hs : ContDiff ℝ ∞ (fun y : ℝ × CompactHolderSpace (Phase n) R =>
      densityLinearSlope p q R y.2) := (densityLinearSlope_contDiff p q R).comp contDiff_snd
  have hA : ContDiff ℝ ∞ (fun y : ℝ × CompactHolderSpace (Phase n) R =>
      (0 : ℂ →L[ℝ] ℝ).prod (densityLinearSlope p q R y.2)) :=
    by
      convert (contDiff_const (c := ContinuousLinearMap.inr ℝ ℝ (Phase n))).clm_comp hs using 1
      funext y
      ext z <;> rfl
  exact ((contDiff_fst.prodMk (contDiff_const.sub h0)).prodMk hA).prodMk hv

 theorem timeDensityProfile_value {n : ℕ} (p q : Phase n) (R : ℝ)
    (y : ℝ × CompactHolderSpace (Phase n) R) (z : ℂ) :
    (timeDensityProfile p q R y).1.1+(timeDensityProfile p q R y).1.2 z+
      holderValue ((1:ℝ)/3) (timeDensityProfile p q R y).2 z=(y.1,densityCurve p q R y.2 z) := by
  apply Prod.ext
  · change y.1+0+(holderValue ((1:ℝ)/3) (holderLinearPost ((1:ℝ)/3)
      (ContinuousLinearMap.inr ℝ ℝ (Phase n))
      (c1HolderValue ((1:ℝ)/3) (compactCRInverse R y.2))) z).1=y.1
    rw [holderLinearPost_apply]
    simp
  · change p-compactCRInverseValue R y.2 0+z • densitySlope p q R y.2+
      compactCRInverseValue R y.2 z=p+z • (q-p)+markedCRInverse R y.2 z
    simp only [densitySlope,markedCRInverse,smul_sub]
    abel

 def densityCoefficient {n : ℕ} (p q : Phase n) (R : ℝ)
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (y : ℝ × CompactHolderSpace (Phase n) R) : HolderSpace ℂ (End n) ((1:ℝ)/3) :=
  holderAffineFamily ((1:ℝ)/3) (by norm_num) (by norm_num) A hA hc (timeDensityProfile p q R y)

 theorem densityCoefficient_value {n : ℕ} (p q : Phase n) (R : ℝ)
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (y : ℝ × CompactHolderSpace (Phase n) R) (z : ℂ) :
    holderValue ((1:ℝ)/3) (densityCoefficient p q R A hA hc y) z=A (y.1,densityCurve p q R y.2 z) := by
  rw [densityCoefficient,holderAffineFamily_apply,timeDensityProfile_value]

 theorem densityCoefficient_contDiffAt {n : ℕ} (p q : Phase n) (R : ℝ)
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (y : ℝ × CompactHolderSpace (Phase n) R) (hy : densitySlope p q R y.2 ≠ 0) :
    ContDiffAt ℝ ∞ (densityCoefficient p q R A hA hc) y := by
  apply (holderAffineFamily_contDiffAt ((1:ℝ)/3) (by norm_num) (by norm_num) A hA hc
    (timeDensityProfile p q R y) ‖densitySlope p q R y.2‖ (norm_pos_iff.mpr hy) ?_).comp y
      (timeDensityProfile_contDiff p q R).contDiffAt
  intro z
  change ‖densitySlope p q R y.2‖*‖z‖ ≤ ‖((0:ℝ),z • densitySlope p q R y.2)‖
  simp only [Prod.norm_def,norm_zero,norm_smul,max_eq_right (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact (mul_comm _ _).le

 def densityJet {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) : HolderSpace ℂ (ℂ →L[ℝ] Phase n) ((1:ℝ)/3) :=
  holderConst ((1:ℝ)/3) (densityLinearSlope p q R g)+
    c1HolderDeriv ((1:ℝ)/3) (compactCRInverse R g)

 theorem densityJet_contDiff {n : ℕ} (p q : Phase n) (R : ℝ) :
    ContDiff ℝ ∞ (densityJet p q R) :=
  ((holderConstCLM (K := ℂ) (E := ℂ →L[ℝ] Phase n) ((1:ℝ)/3)).contDiff.comp
    (densityLinearSlope_contDiff p q R)).add
    (((c1HolderDeriv ((1:ℝ)/3)).comp (compactCRInverse (E := Phase n) R)).contDiff)

 def densityResidual {n : ℕ} (p q : Phase n) (R : ℝ)
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (y : ℝ × CompactHolderSpace (Phase n) R) : HolderSpace ℂ (Phase n) ((1:ℝ)/3) :=
  y.2.1-holderCLM ((1:ℝ)/3) (densityCoefficient p q R A hA hc y)
    (holderJetEval ((1:ℝ)/3) 1 (densityJet p q R y.2))

 theorem holderApply_contDiffAt {X E F : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (α : ℝ) {M : X → HolderSpace ℂ (E →L[ℝ] F) α} {v : X → HolderSpace ℂ E α}
    {x : X} (hM : ContDiffAt ℝ ∞ M x) (hv : ContDiffAt ℝ ∞ v x) :
    ContDiffAt ℝ ∞ (fun y => holderCLM α (M y) (v y)) x := by
  have hL : ContDiff ℝ ∞ (holderOperatorCLM (K := ℂ) (E := E) (F := F) α) :=
    ContinuousLinearMap.contDiff _
  exact (hL.contDiffAt.comp x hM).clm_apply hv

 theorem densityDerivativeOne_contDiff {n : ℕ} (p q : Phase n) (R : ℝ) :
    ContDiff ℝ ∞ (fun y : ℝ × CompactHolderSpace (Phase n) R =>
      holderJetEval ((1:ℝ)/3) 1 (densityJet p q R y.2)) := by
  have hL : ContDiff ℝ ∞ (holderJetEval (K := ℂ) (E := Phase n) ((1:ℝ)/3) 1) :=
    ContinuousLinearMap.contDiff _
  exact hL.comp ((densityJet_contDiff p q R).comp contDiff_snd)

 theorem compactDensity_smooth (n : ℕ) (R : ℝ) :
    ContDiff ℝ ∞ (fun y : ℝ × CompactHolderSpace (Phase n) R => y.2.1) := by
  have hL : ContDiff ℝ ∞ (compactHolderSubmodule (E := Phase n) R).subtypeL :=
    ContinuousLinearMap.contDiff _
  exact hL.comp contDiff_snd

 theorem densityResidual_contDiffAt {n : ℕ} (p q : Phase n) (R : ℝ)
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (y : ℝ × CompactHolderSpace (Phase n) R) (hy : densitySlope p q R y.2 ≠ 0) :
    ContDiffAt ℝ ∞ (densityResidual p q R A hA hc) y := by
  exact (compactDensity_smooth n R).contDiffAt.sub
    (holderApply_contDiffAt ((1:ℝ)/3) (densityCoefficient_contDiffAt p q R A hA hc y hy)
      (densityDerivativeOne_contDiff p q R).contDiffAt)

 theorem densityCurve_eq_profile {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) :
    densityCurve p q R g=c1HolderAffineCurve ((1:ℝ)/3)
      (p-compactCRInverseValue R g 0) (densityLinearSlope p q R g) (compactCRInverse R g) := by
  funext z
  change p+z • (q-p)+(compactCRInverseValue R g z-compactCRInverseValue R g 0-
    z • (compactCRInverseValue R g 1-compactCRInverseValue R g 0))=
    p-compactCRInverseValue R g 0+z • densitySlope p q R g+compactCRInverseValue R g z
  simp only [densitySlope,smul_sub]
  abel

 theorem densityJet_value {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) (z : ℂ) :
    holderValue ((1:ℝ)/3) (densityJet p q R g) z=fderiv ℝ (densityCurve p q R g) z := by
  rw [densityCurve_eq_profile,c1HolderAffineCurve_fderiv]
  change holderValue ((1:ℝ)/3) (holderConst ((1:ℝ)/3) (densityLinearSlope p q R g)) z+
    holderValue ((1:ℝ)/3) (c1HolderDeriv ((1:ℝ)/3) (compactCRInverse R g)) z=_
  rw [holderConst_apply]

 theorem densityResidual_value {n : ℕ} (p q : Phase n) (R : ℝ)
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (y : ℝ × CompactHolderSpace (Phase n) R) (z : ℂ) :
    holderValue ((1:ℝ)/3) (densityResidual p q R A hA hc y) z=
      fderiv ℝ (densityCurve p q R y.2) z Complex.I-
        (standardJ n+A (y.1,densityCurve p q R y.2 z))
          (fderiv ℝ (densityCurve p q R y.2) z 1) := by
  change compactHolderValue R y.2 z-
    holderValue ((1:ℝ)/3) (holderCLM ((1:ℝ)/3) (densityCoefficient p q R A hA hc y)
      (holderJetEval ((1:ℝ)/3) 1 (densityJet p q R y.2))) z=_
  rw [holderCLM_apply,densityCoefficient_value,holderJetEval_apply,densityJet_value,
    ←densityCurve_curl p q R y.2 z]
  change (fderiv ℝ (densityCurve p q R y.2) z Complex.I-standardJ n (fderiv ℝ (densityCurve p q R y.2) z 1))-A _ _=
    fderiv ℝ (densityCurve p q R y.2) z Complex.I-(standardJ n (fderiv ℝ (densityCurve p q R y.2) z 1)+A _ _)
  abel

 theorem pseudoHolomorphicAt_of_scalarCR {n : ℕ} {J : Phase n → End n}
    {u : ℂ → Phase n} {z : ℂ} (hu : DifferentiableAt ℝ u z)
    (hJ : ∀ v, J (u z) (J (u z) v)=-v)
    (hCR : fderiv ℝ u z Complex.I=J (u z) (fderiv ℝ u z 1)) :
    PseudoHolomorphicAt J u z := by
  refine ⟨hu,?_⟩
  intro w
  have hw : w=w.re • (1:ℂ)+w.im • Complex.I := by apply Complex.ext <;> simp
  have hiw : Complex.I*w=(-w.im) • (1:ℂ)+w.re • Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  conv_rhs => rw [hw]
  rw [hiw]
  simp only [map_add,map_smul,hCR,hJ]
  rw [smul_neg,neg_smul]
  abel

 theorem densityResidual_zero_iff {n : ℕ} (p q : Phase n) (R : ℝ)
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (J : Phase n → End n) (hJ : ∀ x, Compatible (J x))
    (he : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, A (t,x)=lineHomotopy J t x-standardJ n)
    (y : ℝ × CompactHolderSpace (Phase n) R) (hy : y.1 ∈ Icc (0:ℝ) 1) :
    densityResidual p q R A hA hc y=0 ↔
      ∀ z, PseudoHolomorphicAt (lineHomotopy J y.1) (densityCurve p q R y.2) z := by
  have hv (z : ℂ) : holderValue ((1:ℝ)/3) (densityResidual p q R A hA hc y) z=
      fderiv ℝ (densityCurve p q R y.2) z Complex.I-
        lineHomotopy J y.1 (densityCurve p q R y.2 z) (fderiv ℝ (densityCurve p q R y.2) z 1) := by
    rw [densityResidual_value,he _ hy]
    congr 2
    abel
  constructor
  · intro h z
    apply pseudoHolomorphicAt_of_scalarCR ((densityCurve_contDiff p q R y.2).differentiable (by simp) z)
      (lineHomotopy_compatible hJ hy _).1
    apply sub_eq_zero.mp
    rw [←hv,h]
    rfl
  · intro h
    apply holderValue_injective ((1:ℝ)/3)
    apply DFunLike.ext
    intro z
    rw [hv]
    have hz := (h z).2 (1:ℂ)
    change _-_=(0 : Phase n)
    simpa only [mul_one] using sub_eq_zero.mpr hz

 theorem densityResidual_at_zero_time {n : ℕ} (p q : Phase n) (R : ℝ)
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (J : Phase n → End n) (hJ : ∀ x, Compatible (J x))
    (he : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, A (t,x)=lineHomotopy J t x-standardJ n)
    (g : CompactHolderSpace (Phase n) R) :
    densityResidual p q R A hA hc (0,g)=g.1 := by
  apply holderValue_injective ((1:ℝ)/3)
  apply DFunLike.ext
  intro z
  rw [densityResidual_value,he 0 (by constructor <;> norm_num),lineHomotopy_zero hJ]
  simp only [sub_self,add_zero]
  exact densityCurve_curl p q R g z

end HigherDimensionalBallPacking.Rigidity

end

end OAI
