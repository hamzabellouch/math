import OAI.NumberTheory.DirichletL.Eisenstein.CorrespondenceAdjoint

namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise Manifold ContDiff ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O

lemma kernelTestField_comp_contDiffAt (f : kernelSmoothTests) (g : SL(2,ℂ))
    (p : EuclideanSpatial) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (kernelTestField f ∘ euclideanAction g) p := by
  have hd := ((((f.2.1.comp kernelProjection_contMDiff).comp (hyperbolicAction_contMDiff g))
    (euclideanToHyperbolic p)).comp p (euclideanToHyperbolic_contMDiffAt p hp)).contDiffAt
  simpa only [Function.comp_def,kernelTestField,euclideanAction,euclideanToHyperbolic_coordinates] using hd

lemma coverGradientAt_lift_continuous (F : EuclideanSpatial→ℂ)
    (hF : ∀p,0<p 2→ContDiffAt ℝ ∞ F p) :
    Continuous (fun w : HyperbolicSpace=>coverGradientAt F (hyperbolicEuclideanCoordinates w)) := by
  apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3=>ℂ)).symm.continuous.comp
  apply continuous_pi
  intro j
  apply (Complex.continuous_ofReal.comp hyperbolicHeight_continuous).mul
  rw [continuous_iff_continuousAt]
  intro w
  exact (((hF _ (hyperbolicHeight_pos w)).continuousAt_fderiv (by simp)).clm_apply
    continuousAt_const).comp hyperbolicEuclideanCoordinates_continuous.continuousAt

def kernelCorrespondencePairLift (g : SL(2,ℂ)) (f h : kernelSmoothTests)
    (w : HyperbolicSpace) : ℂ :=
  coverDirichletPair (kernelTestField f) (kernelTestField h ∘ euclideanAction g)
    (hyperbolicEuclideanCoordinates w)

lemma kernelCorrespondencePairLift_continuous (g : SL(2,ℂ)) (f h : kernelSmoothTests) :
    Continuous (kernelCorrespondencePairLift g f h) :=
  (coverGradientAt_lift_continuous _ (kernelTestField_contDiffAt f)).inner
    (coverGradientAt_lift_continuous _ (kernelTestField_comp_contDiffAt h g))

variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)

include hHK hJK he in
omit [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondencePairLift_invariant (f h : kernelSmoothTests)
    (k : H) (w : HyperbolicSpace) :
    kernelCorrespondencePairLift g f h (k•w)=kernelCorrespondencePairLift g f h w := by
  let A := integralComplexMatrix (k:SL(2,ActualEisensteinCubic.O))
  let B := integralComplexMatrix (e k:SL(2,ActualEisensteinCubic.O))
  have hfi : kernelTestField f ∘ euclideanAction A=kernelTestField f :=
    funext (kernelTestField_invariant f ⟨(k:SL(2,ActualEisensteinCubic.O)),hHK k.property⟩)
  have hhi : (kernelTestField h ∘ euclideanAction g) ∘ euclideanAction A=
      kernelTestField h ∘ euclideanAction g := by
    rw [Function.comp_assoc,←euclideanAction_mul,he k,euclideanAction_mul,←Function.comp_assoc]
    have hh : kernelTestField h ∘ euclideanAction B=kernelTestField h :=
      funext (kernelTestField_invariant h ⟨(e k:SL(2,ActualEisensteinCubic.O)),hJK (e k).property⟩)
    rw [hh]
  have hp := hyperbolicHeight_pos w
  have hh := coverDirichletPair_comp A (kernelTestField f) (kernelTestField h ∘ euclideanAction g)
    (hyperbolicEuclideanCoordinates w) hp
    ((kernelTestField_contDiffAt f _ (euclideanAction_positive A _)).differentiableAt (by simp))
    ((kernelTestField_comp_contDiffAt h g _ (euclideanAction_positive A _)).differentiableAt (by simp))
  rw [hfi,hhi] at hh
  change _=coverDirichletPair (kernelTestField f) (kernelTestField h ∘ euclideanAction g)
    (hyperbolicEuclideanCoordinates w)
  rw [integralSubgroup_smul]
  simpa only [kernelCorrespondencePairLift,A,euclideanAction,euclideanToHyperbolic_coordinates] using hh.symm

def kernelCorrespondencePair (f h : kernelSmoothTests) : IntegralOrbitQuotient H→ℂ :=
  Quotient.lift (kernelCorrespondencePairLift g f h) (by
    rintro w v ⟨k,rfl⟩
    exact (kernelCorrespondencePairLift_invariant hHK hJK e g he f h k w).symm)

omit [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondencePair_projection (f h : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelCorrespondencePair hHK hJK e g he f h (integralOrbitProjection H w)=
      kernelCorrespondencePairLift g f h w := rfl

omit [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondencePair_measurable (f h : kernelSmoothTests) :
    Measurable (kernelCorrespondencePair hHK hJK e g he f h) :=
  measurable_from_quotient.mpr (kernelCorrespondencePairLift_continuous g f h).measurable

omit [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondencePair_norm_le (f h : kernelSmoothTests) (q : IntegralOrbitQuotient H) :
    ‖kernelCorrespondencePair hHK hJK e g he f h q‖≤
      (kernelQuotientEnergyDensity f (integralCoverMap hHK q)+
        kernelQuotientEnergyDensity h (integralCoverMap hJK (integralConjugateMap e g he q)))/2 := by
  induction q using Quotient.inductionOn with
  | _ w =>
    have hf := (kernelTestField_contDiffAt f (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)).differentiableAt (by simp)
    have hh := (kernelTestField_comp_contDiffAt h g (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)).differentiableAt (by simp)
    have hb := coverDirichletPair_norm_le (kernelTestField f) (kernelTestField h ∘ euclideanAction g)
      (hyperbolicEuclideanCoordinates w) hf hh
    rw [coverEnergyDensity_comp g _ _ (hyperbolicHeight_pos w)
      ((kernelTestField_contDiffAt h _ (euclideanAction_positive g _)).differentiableAt (by simp))] at hb
    change ‖kernelCorrespondencePairLift g f h w‖≤
      (kernelTestEnergyDensity f w+kernelTestEnergyDensity h (g•w))/2
    simpa only [kernelCorrespondencePairLift,kernelTestEnergyDensity_eq_cover,euclideanAction,
      euclideanToHyperbolic_coordinates] using hb

lemma kernelCorrespondencePair_integrable (f h : kernelSmoothTests) :
    Integrable (kernelCorrespondencePair hHK hJK e g he f h) (integralQuotientVolume H) := by
  have hf := (integralCoverMap_measurePreserving hHK globalKubotaKernel_le_levelThree).integrable_comp_of_integrable
    ((kernelQuotientEnergyDensity_integrable f).smul_measure
      (c:=(H.relIndex globalKubotaKernel:ℝ≥0∞)) (by simp))
  have hh := (integralCoverMap_measurePreserving hJK globalKubotaKernel_le_levelThree).integrable_comp_of_integrable
    ((kernelQuotientEnergyDensity_integrable h).smul_measure
      (c:=(J.relIndex globalKubotaKernel:ℝ≥0∞)) (by simp))
  have hhh := (integralConjugateMap_measurePreserving e g he
    (hHK.trans globalKubotaKernel_le_levelThree) (hJK.trans globalKubotaKernel_le_levelThree)).integrable_comp_of_integrable hh
  apply ((hf.add hhh).div_const 2).mono' (kernelCorrespondencePair_measurable hHK hJK e g he f h).aestronglyMeasurable
  exact Filter.Eventually.of_forall (kernelCorrespondencePair_norm_le hHK hJK e g he f h)

end

local notation "O" => ActualEisensteinCubic.O

lemma kernelCorrespondencePairLift_kernel (g : SL(2,ℂ)) (f h : kernelSmoothTests)
    (r : globalKubotaKernel) (w : HyperbolicSpace) :
    kernelCorrespondencePairLift g f h (r•w)=
      coverDirichletPair (kernelTestField f)
        (kernelTestField h ∘ euclideanAction (g*integralComplexMatrix (r:SL(2,ActualEisensteinCubic.O))))
        (hyperbolicEuclideanCoordinates w) := by
  have hf := (kernelTestField_contDiffAt f _ (euclideanAction_positive (integralComplexMatrix r) (hyperbolicEuclideanCoordinates w))).differentiableAt (by simp)
  have hh := (kernelTestField_comp_contDiffAt h g _ (euclideanAction_positive (integralComplexMatrix r) (hyperbolicEuclideanCoordinates w))).differentiableAt (by simp)
  have hp := coverDirichletPair_comp (integralComplexMatrix r) (kernelTestField f)
    (kernelTestField h ∘ euclideanAction g) (hyperbolicEuclideanCoordinates w)
    (hyperbolicHeight_pos w) hf hh
  have hfi : kernelTestField f ∘ euclideanAction (integralComplexMatrix r)=kernelTestField f :=
    funext (kernelTestField_invariant f r)
  rw [hfi,Function.comp_assoc,←euclideanAction_mul] at hp
  simpa only [kernelCorrespondencePairLift,integralSubgroup_smul,euclideanAction,
    euclideanToHyperbolic_coordinates] using hp.symm

lemma kernelTestField_comp_inverse (f : kernelSmoothTests) (g : SL(2,ℂ)) :
    (kernelTestField f ∘ euclideanAction g⁻¹) ∘ euclideanAction g=kernelTestField f := by
  funext p
  simp only [Function.comp_def,kernelTestField,euclideanAction,euclideanToHyperbolic_coordinates,
    inv_smul_smul]

variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)

lemma kernelCorrespondencePair_trace (f h : kernelSmoothTests) (q : KernelQuotient) :
    kernelDirichletPairDensity f (kernelCorrespondenceTest hHK hJK e g he h) q=
      integralCoverTraceFunction H globalKubotaKernel
        (kernelCorrespondencePair hHK hJK e g he f h) q := by
  let : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
  induction q using Quotient.inductionOn with
  | _ w =>
    change kernelDirichletPairDensity f (kernelCorrespondenceTest hHK hJK e g he h)
      (integralOrbitProjection globalKubotaKernel w)=_
    rw [kernelDirichletPairDensity_eq_cover]
    have hfield := funext (kernelCorrespondenceTest_field hHK hJK e g he h)
    rw [hfield]
    have hd (r : IntegralCoverCosets H globalKubotaKernel) :
        DifferentiableAt ℝ (kernelTestField h ∘ euclideanAction (kernelCorrespondenceMatrix g r))
          (hyperbolicEuclideanCoordinates w) :=
      (kernelTestField_comp_contDiffAt h _ _ (hyperbolicHeight_pos w)).differentiableAt (by simp)
    have hsum := coverDirichletPair_sum_right Finset.univ (kernelTestField f)
      (fun r=>kernelTestField h ∘ euclideanAction (kernelCorrespondenceMatrix g r))
      (hyperbolicEuclideanCoordinates w) (fun r _=>hd r)
    simp only [Function.comp_apply] at hsum
    rw [hsum]
    change (∑r : IntegralCoverCosets H globalKubotaKernel,_)=
      ∑r : IntegralCoverCosets H globalKubotaKernel,
        kernelCorrespondencePair hHK hJK e g he f h (integralCoverFiberPoint H globalKubotaKernel r w)
    apply Finset.sum_congr rfl
    intro r _
    rw [integralCoverFiberPoint_rep,kernelCorrespondencePair_projection,
      kernelCorrespondencePairLift_kernel]
    rfl

lemma kernelCorrespondenceForm_integral (f h : kernelSmoothTests) :
    kernelDirichletForm f (kernelCorrespondenceTest hHK hJK e g he h)=
      ∫q,kernelCorrespondencePair hHK hJK e g he f h q∂integralQuotientVolume H := by
  unfold kernelDirichletForm
  simp_rw [kernelCorrespondencePair_trace]
  exact integralCoverTraceFunction_integral hHK globalKubotaKernel_le_levelThree _
    (kernelCorrespondencePair_measurable hHK hJK e g he f h)
    (kernelCorrespondencePair_integrable hHK hJK e g he f h)

omit [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondencePair_conjugate (f h : kernelSmoothTests) (q : IntegralOrbitQuotient H) :
    kernelCorrespondencePair hHK hJK e g he f h q=
      star (kernelCorrespondencePair hJK hHK e.symm g⁻¹
        (integralCoverIntertwines_inverse e g he) h f (integralConjugateMap e g he q)) := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change kernelCorrespondencePairLift g f h w=
      star (kernelCorrespondencePairLift g⁻¹ h f (g•w))
    have hf := (kernelTestField_contDiffAt h _ (euclideanAction_positive g (hyperbolicEuclideanCoordinates w))).differentiableAt (by simp)
    have hh := (kernelTestField_comp_contDiffAt f g⁻¹ _ (euclideanAction_positive g (hyperbolicEuclideanCoordinates w))).differentiableAt (by simp)
    have hc := coverDirichletPair_comp g (kernelTestField h) (kernelTestField f ∘ euclideanAction g⁻¹)
      (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w) hf hh
    rw [kernelTestField_comp_inverse] at hc
    have hs := congrArg star hc
    have hswap : star (inner ℂ
        (coverGradientAt (kernelTestField h ∘ euclideanAction g) (hyperbolicEuclideanCoordinates w))
        (coverGradientAt (kernelTestField f) (hyperbolicEuclideanCoordinates w)))=
        inner ℂ (coverGradientAt (kernelTestField f) (hyperbolicEuclideanCoordinates w))
          (coverGradientAt (kernelTestField h ∘ euclideanAction g) (hyperbolicEuclideanCoordinates w)) :=
      inner_conj_symm _ _
    rw [coverDirichletPair,hswap] at hs
    simpa only [kernelCorrespondencePairLift,coverDirichletPair,euclideanAction,
      euclideanToHyperbolic_coordinates] using hs

theorem kernelCorrespondenceForm_adjoint (f h : kernelSmoothTests) :
    kernelDirichletForm f (kernelCorrespondenceTest hHK hJK e g he h)=
      kernelDirichletForm (kernelCorrespondenceTest hJK hHK e.symm g⁻¹
        (integralCoverIntertwines_inverse e g he) f) h := by
  let opposite := kernelCorrespondencePair hJK hHK e.symm g⁻¹
    (integralCoverIntertwines_inverse e g he) h f
  have hom := kernelCorrespondencePair_measurable hJK hHK e.symm g⁻¹
    (integralCoverIntertwines_inverse e g he) h f
  have hm := integralConjugateMap_measurePreserving e g he
    (hHK.trans globalKubotaKernel_le_levelThree) (hJK.trans globalKubotaKernel_le_levelThree)
  rw [kernelCorrespondenceForm_integral]
  calc
    _ = ∫q,star (opposite (integralConjugateMap e g he q))∂integralQuotientVolume H := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (kernelCorrespondencePair_conjugate hHK hJK e g he f h)
    _ = ∫q,star (opposite q)∂integralQuotientVolume J := by
      have hh := integral_map («μ»:=integralQuotientVolume H) hm.measurable.aemeasurable
        (continuous_star.measurable.comp hom).aestronglyMeasurable
      rw [hm.map_eq] at hh
      exact hh.symm
    _ = star (∫q,opposite q∂integralQuotientVolume J) := by
      simp only [Complex.star_def]
      exact integral_conj
    _ = _ := by
      rw [←kernelCorrespondenceForm_integral hJK hHK e.symm g⁻¹
        (integralCoverIntertwines_inverse e g he),kernelDirichletForm_conj]

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)

lemma kernelCorrespondenceEnergy_pairing_core (f h : kernelSmoothTests) :
    inner ℂ (kernelEnergyGraphCore f)
      (kernelCorrespondenceEnergy hHK hJK e g he (kernelEnergyGraphCore h))=
    inner ℂ (kernelCorrespondenceEnergy hJK hHK e.symm g⁻¹
      (integralCoverIntertwines_inverse e g he) (kernelEnergyGraphCore f)) (kernelEnergyGraphCore h) := by
  rw [kernelCorrespondenceEnergy_core,kernelCorrespondenceEnergy_core,
    kernelEnergyGraph_inner,kernelEnergyGraph_inner]
  simp only [kernelEnergyMass_core,kernelEnergyGradient_core,kernelGradientToL2_inner]
  rw [kernelCorrespondenceTest_mass,kernelCorrespondenceTest_mass,
    kernelCorrespondenceL2_pairing,kernelCorrespondenceForm_adjoint]

theorem kernelCorrespondenceEnergy_pairing (u v : KernelEnergyGraph) :
    inner ℂ u (kernelCorrespondenceEnergy hHK hJK e g he v)=
      inner ℂ (kernelCorrespondenceEnergy hJK hHK e.symm g⁻¹
        (integralCoverIntertwines_inverse e g he) u) v := by
  apply congrFun (kernelEnergyGraphCore_dense.equalizer
    (continuous_id.inner continuous_const)
    ((kernelCorrespondenceEnergy hJK hHK e.symm g⁻¹
      (integralCoverIntertwines_inverse e g he)).continuous.inner continuous_const) ?_) u
  funext f
  apply congrFun (kernelEnergyGraphCore_dense.equalizer
    (continuous_const.inner (kernelCorrespondenceEnergy hHK hJK e g he).continuous)
    (continuous_const.inner continuous_id) ?_) v
  funext h
  exact kernelCorrespondenceEnergy_pairing_core hHK hJK e g he f h

lemma kernelCorrespondenceEnergy_pairing_left (u v : KernelEnergyGraph) :
    inner ℂ (kernelCorrespondenceEnergy hHK hJK e g he u) v=
      inner ℂ u (kernelCorrespondenceEnergy hJK hHK e.symm g⁻¹
        (integralCoverIntertwines_inverse e g he) v) := by
  have hh := congrArg star (kernelCorrespondenceEnergy_pairing hHK hJK e g he v u)
  simpa only [←starRingEnd_apply,inner_conj_symm] using hh

lemma kernelCorrespondenceL2_pairing_left (F G : KernelQuotientL2) :
    inner ℂ (kernelCorrespondenceL2 hHK hJK e g he F) G=
      inner ℂ F (kernelCorrespondenceL2 hJK hHK e.symm g⁻¹
        (integralCoverIntertwines_inverse e g he) G) := by
  have hh := congrArg star (kernelCorrespondenceL2_pairing hHK hJK e g he G F)
  simpa only [←starRingEnd_apply,inner_conj_symm] using hh

theorem kernelCorrespondence_variationalSolution (F : KernelQuotientL2) :
    kernelCorrespondenceEnergy hHK hJK e g he (kernelVariationalSolution F)=
      kernelVariationalSolution (kernelCorrespondenceL2 hHK hJK e g he F) := by
  apply kernelVariationalSolution_unique
  intro v
  rw [←kernelEnergyGraph_inner,kernelCorrespondenceEnergy_pairing_left,
    kernelEnergyGraph_inner,kernelVariationalSolution_equation,
    kernelCorrespondenceEnergy_mass]
  exact (kernelCorrespondenceL2_pairing_left hHK hJK e g he F (kernelEnergyMass v)).symm

theorem kernelCorrespondence_variationalResolvent (F : KernelQuotientL2) :
    kernelVariationalResolvent (kernelCorrespondenceL2 hHK hJK e g he F)=
      kernelCorrespondenceL2 hHK hJK e g he (kernelVariationalResolvent F) := by
  change kernelEnergyMass (kernelVariationalSolution (kernelCorrespondenceL2 hHK hJK e g he F))=_
  rw [←kernelCorrespondence_variationalSolution,kernelCorrespondenceEnergy_mass]
  rfl

theorem kernelCorrespondence_operatorGraph (F G : KernelQuotientL2)
    (hFG : (F,G)∈kernelEnergyLaplacian.graph) :
    (kernelCorrespondenceL2 hHK hJK e g he F,
      kernelCorrespondenceL2 hHK hJK e g he G)∈kernelEnergyLaplacian.graph := by
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph] at hFG ⊢
  rw [←map_add,kernelCorrespondence_variationalResolvent,hFG]

theorem kernelCorrespondence_eigenvector (F : KernelQuotientL2) (eigenvalue : ℂ)
    (hF : (F,eigenvalue • F)∈kernelEnergyLaplacian.graph) :
    (kernelCorrespondenceL2 hHK hJK e g he F,
      eigenvalue • kernelCorrespondenceL2 hHK hJK e g he F)∈kernelEnergyLaplacian.graph := by
  simpa only [map_smul] using kernelCorrespondence_operatorGraph hHK hJK e g he F (eigenvalue • F) hF

end

section

open MeasureTheory
open scoped Classical MatrixGroups BigOperators

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma cuspFrequency_mul_right (h c:Eis) : cuspFrequency (h*c)=cuspFrequency h*eisEmbedding c := by
  unfold cuspFrequency
  rw [map_mul]
  ring

lemma cusp_character_continuous (h:Eis) :
    Continuous (fun z:ℂ=>ShortDraftTrace.breveE (-cuspFrequency h*z)) := by
  change Continuous (fun z:ℂ=>Complex.exp (2*Real.pi*Complex.I*
    ((-cuspFrequency h*z)+starRingEnd ℂ (-cuspFrequency h*z))))
  fun_prop

lemma cusp_character_fractional_period (c:Eis) (hc:c≠0) (h q:Eis) (z:ℂ) :
    ShortDraftTrace.breveE (-cuspFrequency (h*c)*(z+3*eisEmbedding q/eisEmbedding c))=
      ShortDraftTrace.breveE (-cuspFrequency (h*c)*z) := by
  rw [mul_add,AddChar.map_add_eq_mul]
  have he:-cuspFrequency (h*c)*(3*eisEmbedding q/eisEmbedding c)=
      -cuspFrequency h*(3*eisEmbedding q):=by
    rw [cuspFrequency_mul_right]
    field_simp [eisEmbedding_ne_zero hc]
  rw [he]
  have hz:ShortDraftTrace.breveE (-cuspFrequency h*(3*eisEmbedding q))=1:=by
    simpa only [zero_add,mul_zero,AddChar.map_zero_eq_one] using cuspFrequency_negative_period h q 0
  rw [hz,mul_one]

lemma period_fourier_fractional_translation (f:ℂ→ℂ)
    (hf:∀n:Eis,∀z:ℂ,f (z+3*eisEmbedding n)=f z)
    (c:Eis) (hc:c≠0) (h q:Eis) :
    (∫z in periodDomain,f (z+3*eisEmbedding q/eisEmbedding c)*
      ShortDraftTrace.breveE (-cuspFrequency (h*c)*z))=
    ∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency (h*c)*z) := by
  let g:ℂ→ℂ:=fun z=>f z*ShortDraftTrace.breveE (-cuspFrequency (h*c)*z)
  have hg (n:Eis) (z:ℂ):g (z+3*eisEmbedding n)=g z:=by
    dsimp [g]
    rw [hf,cuspFrequency_negative_period]
  have hi:=period_integral_translation g hg (3*eisEmbedding q/eisEmbedding c)
  have hp (z:ℂ):g (3*eisEmbedding q/eisEmbedding c+z)=
      f (z+3*eisEmbedding q/eisEmbedding c)*ShortDraftTrace.breveE (-cuspFrequency (h*c)*z):=by
    dsimp [g]
    rw [add_comm (3*eisEmbedding q/eisEmbedding c) z,cusp_character_fractional_period c hc]
  simpa only [hp,g] using hi

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma cube_upperPoint_continuous (v:ℝ) (hv:0<v) : Continuous (fun z:ℂ=>upperPoint z v hv) := by
  let c:ℂ→UpperCoordinates:=fun z=>⟨(z,v),hv⟩
  have hc:Continuous c:=by
    apply Continuous.subtype_mk
    exact continuous_id.prodMk continuous_const
  simpa only [Function.comp_def,c] using continuous_upperCoordinates.comp hc

theorem cubeAverage_fourier (p:Eis) (hp:p≠0) (F:HyperbolicSpace→ℂ) (hF:Continuous F)
    (hperiod:∀n:Eis,∀w:HyperbolicSpace,F (complexTranslation (3*eisEmbedding n) • w)=F w)
    (h:Eis) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubeAverage p hp F (upperPoint z v hv)*ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ∫z in periodDomain,F (upperPoint z (v/‖eisEmbedding p‖^3)
        (div_pos hv (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hp)) 3)))*
        ShortDraftTrace.breveE (-cuspFrequency (h*p^3)*z) := by
  let V:=v/‖eisEmbedding p‖^3
  have hV:0<V:=div_pos hv (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hp)) 3)
  let f:ℂ→ℂ:=fun z=>F (upperPoint z V hV)
  let H:ℂ→ℂ:=fun z=>cubeAverage p hp F (upperPoint z v hv)*ShortDraftTrace.breveE (-cuspFrequency h*z)
  have hf:Continuous f:=hF.comp (cube_upperPoint_continuous V hV)
  have hfperiod (n:Eis) (z:ℂ):f (z+3*eisEmbedding n)=f z:=by
    dsimp [f]
    rw [←complexTranslation_action]
    exact hperiod n _
  have hH:Continuous H:=
    ((cubeAverage_continuous p hp F hF).comp (cube_upperPoint_continuous v hv)).mul (cusp_character_continuous h)
  have hHperiod (n:Eis) (z:ℂ):H (z+3*eisEmbedding n)=H z:=by
    dsimp [H]
    rw [←complexTranslation_action,cubeAverage_period_three p hp F hperiod,cuspFrequency_negative_period]
  let term (r:Eis⧸Ideal.span {p^3}) (z:ℂ):=
    f (z+3*eisEmbedding (GaussianShiftedPartition.representative (p^3) r)/eisEmbedding (p^3))*
      ShortDraftTrace.breveE (-cuspFrequency (h*p^3)*z)
  have hpoint (z:ℂ):H (eisEmbedding (p^3)*z)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3*(∑' r:Eis⧸Ideal.span {p^3},term r z):=by
    have hphase:ShortDraftTrace.breveE (-cuspFrequency h*(eisEmbedding (p^3)*z))=
        ShortDraftTrace.breveE (-cuspFrequency (h*p^3)*z):=by
      rw [cuspFrequency_mul_right]
      congr 1
      ring
    dsimp only [H,cubeAverage]
    rw [hphase]
    rw [mul_assoc,←tsum_mul_right]
    congr 1
    apply tsum_congr
    intro r
    dsimp only [term,f]
    rw [cubeAverageMatrix_action]
    congr 2
    apply upperPoint_congr
    · rw [map_pow]
      field_simp [eisEmbedding_ne_zero hp]
    · rfl
  let:Finite (Eis⧸Ideal.span {p^3}):=finite_quotient_span (pow_ne_zero 3 hp)
  let:Fintype (Eis⧸Ideal.span {p^3}):=Fintype.ofFinite _
  have hi (r:Eis⧸Ideal.span {p^3}):IntegrableOn (term r) periodDomain:=by
    apply periodDomain_integrable_of_continuous
    exact (hf.comp (continuous_id.add continuous_const)).mul (cusp_character_continuous (h*p^3))
  have hint:(∫z in periodDomain,∑' r:Eis⧸Ideal.span {p^3},term r z)=
      ∑' r:Eis⧸Ideal.span {p^3},∫z in periodDomain,term r z:=by
    simp only [tsum_fintype]
    exact integral_finsetSum _ (fun r _=>hi r)
  have hterm (r:Eis⧸Ideal.span {p^3}):
      (∫z in periodDomain,term r z)=∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency (h*p^3)*z):=
    period_fourier_fractional_translation f hfperiod (p^3) (pow_ne_zero 3 hp) h _
  have hcard:(Nat.card (Eis⧸Ideal.span {p^3}):ℂ)=(Ideal.absNorm (Ideal.span {p}):ℂ)^3:=by
    change (Ideal.absNorm (Ideal.span {p^3}):ℂ)=_
    rw [←Ideal.span_singleton_pow,map_pow,Nat.cast_pow]
  have hqN:Ideal.absNorm (Ideal.span {p})≠0:=
    (Ideal.absNorm_ne_zero_iff _).mpr (finite_quotient_span hp)
  have hq:(Ideal.absNorm (Ideal.span {p}):ℂ)≠0:=by exact_mod_cast hqN
  change (∫z in periodDomain,H z)=∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency (h*p^3)*z)
  calc
    _=∫z in periodDomain,H (eisEmbedding (p^3)*z):=
      (period_integral_eisenstein_mul H hH.measurable hHperiod (p^3) (pow_ne_zero 3 hp)).symm
    _=(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3*
        (∑' r:Eis⧸Ideal.span {p^3},∫z in periodDomain,term r z):=by
      simp_rw [hpoint]
      rw [integral_const_mul,hint]
    _=(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3*
        (∑' (_:Eis⧸Ideal.span {p^3}),∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency (h*p^3)*z)):=by
      congr 1
      exact tsum_congr hterm
    _=_:=by rw [tsum_const,nsmul_eq_mul,hcard];field_simp

end

open MeasureTheory
open scoped Classical MatrixGroups BigOperators
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

theorem cubeSource_fourier (p:Eis) (hp:p≠0) (h:Eis) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubeAverage p hp cubicSourceResidualFunction (upperPoint z v hv)*
      ShortDraftTrace.breveE (-cuspFrequency h*z))=
    ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceResidualFullModeAmplitude (v/‖eisEmbedding p‖^3) (h*p^3) := by
  rw [cubeAverage_fourier p hp cubicSourceResidualFunction cubicSourceResidualFunction_continuous
    cubicSource_period_three h v hv]
  simp_rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselFunction_fourier _ (div_pos hv (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hp)) 3)) _

lemma cubeSource_amplitude_of_eigenrelation (p:Eis) (hp:p≠0)
    (hU:∀w:HyperbolicSpace,cubeAverage p hp cubicSourceResidualFunction w=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction w)
    (h:Eis) (v:ℝ) (hv:0<v) :
    sourceResidualFullModeAmplitude (v/‖eisEmbedding p‖^3) (h*p^3)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceResidualFullModeAmplitude v h := by
  have hc:((9*Real.sqrt 3/2:ℝ):ℂ)≠0:=Complex.ofReal_ne_zero.mpr (by positivity)
  apply mul_left_cancel₀ hc
  calc
    _=∫z in periodDomain,cubeAverage p hp cubicSourceResidualFunction (upperPoint z v hv)*
      ShortDraftTrace.breveE (-cuspFrequency h*z):=(cubeSource_fourier p hp h v hv).symm
    _=(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*
      (∫z in periodDomain,cubicSourceResidualFunction (upperPoint z v hv)*
        ShortDraftTrace.breveE (-cuspFrequency h*z)):=by
      simp_rw [hU,mul_assoc]
      exact integral_const_mul _ _
    _=(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*
      (((9*Real.sqrt 3/2:ℝ):ℂ)*sourceResidualFullModeAmplitude v h):=by
      simp_rw [cubicSourceResidualFunction_eq_bessel]
      rw [sourceBesselFunction_fourier]
    _=_:=by ring

lemma schlafliBesselK_cubic_ne_zero (x:ℝ) (hx:0<x) : schlafliBesselK (1/3:ℂ) x≠0 := by
  have hp:0<(schlafliBesselK (1/3:ℂ) x).re:=
    lt_of_lt_of_le (mul_pos cubicBesselLowerConstant_pos (Real.exp_pos _)) (schlafliBesselK_cubic_lower x hx)
  intro he
  rw [he,Complex.zero_re] at hp
  exact (lt_irrefl 0) hp

theorem sourceResidualFourierCoefficient_cube_of_eigenrelation (p:Eis) (hp:p≠0)
    (hU:∀w:HyperbolicSpace,cubeAverage p hp cubicSourceResidualFunction w=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction w)
    (h:Eis) (hh:h≠0) :
    sourceResidualFourierCoefficient (h*p^3)=(‖eisEmbedding p‖:ℂ)*sourceResidualFourierCoefficient h := by
  have hhp:h*p^3≠0:=mul_ne_zero hh (pow_ne_zero 3 hp)
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp)
  have hrC:(‖eisEmbedding p‖:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hr.ne'
  have hf:‖cuspFrequency (h*p^3)‖=‖cuspFrequency h‖*‖eisEmbedding p‖^3:=by
    rw [cuspFrequency_mul_right,norm_mul,map_pow,norm_pow]
  have hx:0<4*Real.pi*‖cuspFrequency h‖:=by
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (norm_pos_iff.mpr (cuspFrequency_ne_zero h hh))
  have hK:=schlafliBesselK_cubic_ne_zero _ hx
  have he:=cubeSource_amplitude_of_eigenrelation p hp hU h 1 (by norm_num)
  simp only [sourceResidualFullModeAmplitude,ite_eq_right hhp,ite_eq_right hh,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_pow,mul_one,hf] at he
  have harg:4*Real.pi*(‖cuspFrequency h‖*‖eisEmbedding p‖^3)*(1/‖eisEmbedding p‖^3)=
      4*Real.pi*‖cuspFrequency h‖:=by field_simp
  rw [harg] at he
  have he':sourceResidualFourierCoefficient (h*p^3)/(‖eisEmbedding p‖:ℂ)^3=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceResidualFourierCoefficient h:=by
    apply mul_right_cancel₀ hK
    simpa only [div_eq_mul_inv,one_mul,mul_assoc] using he
  have hn:(Ideal.absNorm (Ideal.span {p}):ℂ)=(‖eisEmbedding p‖:ℂ)^2:=by
    exact_mod_cast (eisEmbedding_norm_sq_eq_absNorm_span p).symm
  rw [hn] at he'
  have he'' :=(div_eq_iff (pow_ne_zero 3 hrC)).mp he'
  rw [he'']
  field_simp

end CubicEisenstein

end

end OAI
