import OAI.NumberTheory.DirichletL.Eisenstein.FredholmAlternative

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

open scoped Topology

lemma kernelSpectralFormOperator_analyticAt (z : ℂ) :
    AnalyticAt ℂ kernelSpectralFormOperator z := by
  let S : KernelEnergyGraph→L[ℂ]KernelEnergyGraph := kernelEnergyMass.adjoint.comp kernelEnergyMass
  have hc : AnalyticAt ℂ (fun w : ℂ => w • S) (z+1) := by
    simpa only [ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply] using!
      (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := ℂ)
        (F := KernelEnergyGraph→L[ℂ]KernelEnergyGraph)
        (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) S) (z+1))
  have hz : AnalyticAt ℂ (fun w : ℂ => w+1) z := analyticAt_id.add analyticAt_const
  exact analyticAt_const.sub (hc.comp_of_eq hz rfl)

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

def kernelMassGram : KernelEnergyGraph→L[ℂ]KernelEnergyGraph :=
  kernelEnergyMass.adjoint.comp kernelEnergyMass

private lemma selfAdjoint_adjoint_comp {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] F) : IsSelfAdjoint (A.adjoint.comp A) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]

lemma kernelMassGram_selfAdjoint : IsSelfAdjoint kernelMassGram :=
  selfAdjoint_adjoint_comp kernelEnergyMass

def kernelThetaNull : Submodule ℂ KernelEnergyGraph :=
  (kernelSpectralFormOperator (8/9:ℂ)).ker

def kernelThetaRegular : Submodule ℂ KernelEnergyGraph := kernelThetaNullᗮ

instance kernelThetaNull_complete : CompleteSpace kernelThetaNull :=
  (kernelSpectralFormOperator (8/9:ℂ)).isClosed_ker.completeSpace_coe

instance kernelThetaRegular_complete : CompleteSpace kernelThetaRegular :=
  kernelThetaNull.isClosed_orthogonal.completeSpace_coe

instance kernelThetaNull_finiteDimensional : FiniteDimensional ℂ kernelThetaNull :=
  kernel_theta_spectral_fredholm.finite_ker

lemma kernelThetaNull_gram_eq (u : KernelEnergyGraph) (hu : u∈kernelThetaNull) :
    kernelMassGram u=(9/17:ℂ)•u := by
  have hh : u-(8/9+1:ℂ)•kernelMassGram u=0 := hu
  have he : u=(17/9:ℂ)•kernelMassGram u := by
    simpa only [show (8/9+1:ℂ)=17/9 by norm_num] using sub_eq_zero.mp hh
  calc
    _ = (9/17:ℂ)•((17/9:ℂ)•kernelMassGram u) := by rw [smul_smul]; norm_num
    _ = _ := by rw [←he]

lemma kernelThetaNull_spectral_eq (z : ℂ) (u : KernelEnergyGraph) (hu : u∈kernelThetaNull) :
    kernelSpectralFormOperator z u=((8/9-z)*(9/17):ℂ)•u := by
  change u-(z+1)•kernelMassGram u=_
  rw [kernelThetaNull_gram_eq u hu,smul_smul]
  calc
    u-((z+1)*(9/17):ℂ)•u=(1-(z+1)*(9/17):ℂ)•u := by rw [sub_smul,one_smul]
    _ = _ := by congr 1; ring

lemma kernelMassGram_preserves_regular (u : KernelEnergyGraph) (hu : u∈kernelThetaRegular) :
    kernelMassGram u∈kernelThetaRegular := by
  apply (kernelThetaNull.mem_orthogonal _).mpr
  intro v hv
  have he : inner ℂ v (kernelMassGram u)=inner ℂ (kernelMassGram v) u := by
    simpa only [ContinuousLinearMap.coe_coe] using (kernelMassGram_selfAdjoint.isSymmetric v u).symm
  rw [he,kernelThetaNull_gram_eq v hv,inner_smul_left (𝕜 := ℂ) v u (9/17:ℂ)]
  rw [kernelThetaNull.inner_right_of_mem_orthogonal hv hu,mul_zero]

lemma kernelSpectralFormOperator_preserves_regular (z : ℂ)
    (u : KernelEnergyGraph) (hu : u∈kernelThetaRegular) :
    kernelSpectralFormOperator z u∈kernelThetaRegular :=
  kernelThetaRegular.sub_mem hu (kernelThetaRegular.smul_mem _ (kernelMassGram_preserves_regular u hu))

def kernelRegularGram : kernelThetaRegular→L[ℂ]kernelThetaRegular :=
  kernelMassGram.restrict kernelMassGram_preserves_regular

def kernelRegularPencil (z : ℂ) : kernelThetaRegular→L[ℂ]kernelThetaRegular :=
  ContinuousLinearMap.id ℂ kernelThetaRegular-(z+1)•kernelRegularGram

lemma kernelRegularPencil_apply (z : ℂ) (u : kernelThetaRegular) :
    (kernelRegularPencil z u:KernelEnergyGraph)=kernelSpectralFormOperator z u := rfl

lemma kernelRegularPencil_center_isUnit : IsUnit (kernelRegularPencil (8/9:ℂ)) := by
  apply (ContinuousLinearMap.isUnit_iff_bijective (𝕜 := ℂ) (E := kernelThetaRegular)).mpr
  constructor
  · intro u v huv
    apply ker_orthogonal_restriction_injective (kernelSpectralFormOperator (8/9:ℂ))
    exact congrArg (fun w : kernelThetaRegular => (w:KernelEnergyGraph)) huv
  · intro v
    have he : (kernelSpectralFormOperator (8/9:ℂ)).range=kernelThetaRegular := by
      exact selfAdjoint_range_eq_ker_orthogonal _
        (by convert kernelSpectralFormOperator_selfAdjoint (8/9) using 1 ; norm_num)
        kernel_theta_spectral_fredholm.isClosed_range
    have hv : (v:KernelEnergyGraph)∈(kernelSpectralFormOperator (8/9:ℂ)).range := by
      rw [he]
      exact v.2
    obtain ⟨u,hu⟩ := hv
    change kernelSpectralFormOperator (8/9:ℂ) u=(v:KernelEnergyGraph) at hu
    let w : kernelThetaRegular := ⟨u-kernelThetaNull.starProjection u,kernelThetaNull.sub_starProjection_mem_orthogonal u⟩
    refine ⟨w,Subtype.ext ?_⟩
    rw [kernelRegularPencil_apply]
    change kernelSpectralFormOperator (8/9:ℂ) (u-kernelThetaNull.starProjection u)=v
    rw [map_sub,hu]
    have hz : kernelSpectralFormOperator (8/9:ℂ) (kernelThetaNull.starProjection u)=0 :=
      kernelThetaNull.starProjection_apply_mem u
    rw [hz,sub_zero]

private abbrev endomorphismNormedSpace (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] : NormedSpace ℂ (E →L[ℂ] E) := inferInstance

local instance : NormedSpace ℂ (kernelThetaRegular →L[ℂ] kernelThetaRegular) :=
  endomorphismNormedSpace kernelThetaRegular

lemma kernelRegularPencil_analyticAt (z : ℂ) :
    AnalyticAt ℂ kernelRegularPencil z := by
  have hc : AnalyticAt ℂ (fun w : ℂ => w • kernelRegularGram) (z+1) := by
    simpa only [ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply] using!
      (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := ℂ)
        (F := kernelThetaRegular→L[ℂ]kernelThetaRegular)
        (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) kernelRegularGram) (z+1))
  have hz : AnalyticAt ℂ (fun w : ℂ => w+1) z := analyticAt_id.add analyticAt_const
  exact analyticAt_const.sub (hc.comp_of_eq hz rfl)

lemma kernelRegularPencil_eventually_isUnit :
    ∀ᶠ z : ℂ in 𝓝 (8/9:ℂ), IsUnit (kernelRegularPencil z) :=
  (kernelRegularPencil_analyticAt (8/9)).continuousAt.eventually
    ((Units.isOpen (R := kernelThetaRegular→L[ℂ]kernelThetaRegular)).mem_nhds
      (show kernelRegularPencil (8/9)∈{x : kernelThetaRegular→L[ℂ]kernelThetaRegular | IsUnit x} from
        kernelRegularPencil_center_isUnit))

lemma kernelRegularInverse_analyticAt :
    AnalyticAt ℂ (fun z : ℂ => Ring.inverse (kernelRegularPencil z)) (8/9:ℂ) := by
  have hi := (analyticOnNhd_inverse (𝕜 := ℂ)
    (A := kernelThetaRegular→L[ℂ]kernelThetaRegular))
    (kernelRegularPencil (8/9)) kernelRegularPencil_center_isUnit
  exact hi.comp_of_eq (kernelRegularPencil_analyticAt (8/9)) rfl

private def continuousLinearSandwich {H G : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (A : H →L[ℂ] G) (B : G →L[ℂ] H) :
    (H →L[ℂ] H) →L[ℂ] (G →L[ℂ] G) :=
  (ContinuousLinearMap.compL ℂ G H G A).comp
    ((ContinuousLinearMap.compL ℂ G H H).flip B)

def kernelRegularLiftCLM :
    (kernelThetaRegular→L[ℂ]kernelThetaRegular)→L[ℂ](KernelEnergyGraph→L[ℂ]KernelEnergyGraph) :=
  continuousLinearSandwich (H := kernelThetaRegular) (G := KernelEnergyGraph)
    kernelThetaRegular.subtypeL
    kernelThetaRegular.orthogonalProjectionOnto

def kernelRegularInverseLift (z : ℂ) : KernelEnergyGraph→L[ℂ]KernelEnergyGraph :=
  kernelRegularLiftCLM (Ring.inverse (kernelRegularPencil z))

lemma kernelRegularInverseLift_apply (z : ℂ) (u : KernelEnergyGraph) :
    kernelRegularInverseLift z u =
      (Ring.inverse (kernelRegularPencil z) (kernelThetaRegular.orthogonalProjectionOnto u) :
        KernelEnergyGraph) := rfl

lemma kernelRegularInverseLift_analyticAt :
    AnalyticAt ℂ kernelRegularInverseLift (8/9:ℂ) := by
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := kernelThetaRegular→L[ℂ]kernelThetaRegular)
    (F := KernelEnergyGraph→L[ℂ]KernelEnergyGraph)
    kernelRegularLiftCLM (Ring.inverse (kernelRegularPencil (8/9)))).comp_of_eq
      kernelRegularInverse_analyticAt rfl

def kernelLocalEnergyResolvent (z : ℂ) : KernelEnergyGraph→L[ℂ]KernelEnergyGraph :=
  ((17/9)/(8/9-z):ℂ) • kernelThetaNull.starProjection + kernelRegularInverseLift z

lemma kernelLocalEnergyResolvent_meromorphicAt :
    MeromorphicAt kernelLocalEnergyResolvent (8/9:ℂ) := by
  have hs : MeromorphicAt (fun z : ℂ => (17/9)/(8/9-z)) (8/9:ℂ) := by fun_prop
  have hp : MeromorphicAt (fun z : ℂ => ((17/9)/(8/9-z):ℂ) • kernelThetaNull.starProjection) (8/9:ℂ) := by
    obtain ⟨n,hn⟩ := hs
    refine ⟨n,?_⟩
    let A := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) kernelThetaNull.starProjection
    have ha := ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := ℂ)
      (F := KernelEnergyGraph→L[ℂ]KernelEnergyGraph) A
      (((8/9:ℂ)-(8/9))^n*((17/9)/(8/9-(8/9))))
    convert ha.comp_of_eq hn rfl using 1 ;
      simp [A,Function.comp_def,smul_smul,smul_eq_mul]
  exact hp.add kernelRegularInverseLift_analyticAt.meromorphicAt

lemma kernelSpectralFormOperator_regularInverseLift (z : ℂ)
    (hz : IsUnit (kernelRegularPencil z)) (u : KernelEnergyGraph) :
    kernelSpectralFormOperator z (kernelRegularInverseLift z u)=
      kernelThetaRegular.starProjection u := by
  rw [kernelRegularInverseLift_apply,←kernelRegularPencil_apply]
  have he := congrArg (fun A : kernelThetaRegular→L[ℂ]kernelThetaRegular =>
    A (kernelThetaRegular.orthogonalProjectionOnto u))
      (Ring.mul_inverse_cancel (kernelRegularPencil z) hz)
  exact congrArg (fun v : kernelThetaRegular => (v:KernelEnergyGraph)) he

lemma kernelLocalEnergyResolvent_right_inverse (z : ℂ) (hne : z≠8/9)
    (hz : IsUnit (kernelRegularPencil z)) (u : KernelEnergyGraph) :
    kernelSpectralFormOperator z (kernelLocalEnergyResolvent z u)=u := by
  change kernelSpectralFormOperator z
    (((17/9)/(8/9-z):ℂ) • kernelThetaNull.starProjection u + kernelRegularInverseLift z u)=u
  rw [map_add,map_smul,kernelThetaNull_spectral_eq z _
    (kernelThetaNull.starProjection_apply_mem u),smul_smul]
  have hc : ((17/9)/(8/9-z):ℂ)*((8/9-z)*(9/17))=1 := by
    calc
      _ = (((17/9)/(8/9-z):ℂ)*(8/9-z))*(9/17) := by ring
      _ = (17/9:ℂ)*(9/17) := by rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hne.symm)]
      _ = 1 := by norm_num
  rw [hc,one_smul,kernelSpectralFormOperator_regularInverseLift z hz]
  exact kernelThetaNull.starProjection_add_starProjection_orthogonal u

lemma selfAdjoint_one_sub_smul_normal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (S : H→L[ℂ]H)
    (hS : IsSelfAdjoint S) (z : ℂ) : IsStarNormal (1-z•S) := by
  let : IsStarNormal S := hS.isStarNormal
  infer_instance

lemma kernelSpectralFormOperator_normal (z : ℂ) : IsStarNormal (kernelSpectralFormOperator z) := by
  exact selfAdjoint_one_sub_smul_normal kernelMassGram kernelMassGram_selfAdjoint (z+1)

lemma kernelSpectralFormOperator_isUnit_near (z : ℂ) (hne : z≠8/9)
    (hz : IsUnit (kernelRegularPencil z)) : IsUnit (kernelSpectralFormOperator z) := by
  have hsur : Function.Surjective (kernelSpectralFormOperator z) := fun u =>
    ⟨kernelLocalEnergyResolvent z u,kernelLocalEnergyResolvent_right_inverse z hne hz u⟩
  apply (ContinuousLinearMap.isUnit_iff_bijective (𝕜 := ℂ) (E := KernelEnergyGraph)).mpr
  refine ⟨?_,hsur⟩
  change Function.Injective (kernelSpectralFormOperator z).toLinearMap
  apply LinearMap.ker_eq_bot.mp
  rw [←ContinuousLinearMap.IsStarNormal.orthogonal_range (kernelSpectralFormOperator_normal z)]
  have hr : (kernelSpectralFormOperator z).range=⊤ := LinearMap.range_eq_top.mpr hsur
  rw [hr,Submodule.top_orthogonal_eq_bot]

lemma kernelLocalEnergyResolvent_left_inverse (z : ℂ) (hne : z≠8/9)
    (hz : IsUnit (kernelRegularPencil z)) (u : KernelEnergyGraph) :
    kernelLocalEnergyResolvent z (kernelSpectralFormOperator z u)=u := by
  have hinj := (ContinuousLinearMap.isUnit_iff_bijective (𝕜 := ℂ) (E := KernelEnergyGraph)).mp
    (kernelSpectralFormOperator_isUnit_near z hne hz)
  exact hinj.1 (kernelLocalEnergyResolvent_right_inverse z hne hz _)

lemma kernelLocalEnergyResolvent_eq_inverse (z : ℂ) (hne : z≠8/9)
    (hz : IsUnit (kernelRegularPencil z)) :
    kernelLocalEnergyResolvent z = Ring.inverse (kernelSpectralFormOperator z) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ((ContinuousLinearMap.isUnit_iff_bijective (𝕜 := ℂ) (E := KernelEnergyGraph)).mp
    (kernelSpectralFormOperator_isUnit_near z hne hz)).1
  rw [kernelLocalEnergyResolvent_right_inverse z hne hz]
  have hi := congrArg (fun A : KernelEnergyGraph→L[ℂ]KernelEnergyGraph => A u)
    (Ring.mul_inverse_cancel (kernelSpectralFormOperator z) (kernelSpectralFormOperator_isUnit_near z hne hz))
  exact hi.symm

lemma kernelSpectralFormInverse_meromorphicAt :
    MeromorphicAt (fun z : ℂ => Ring.inverse (kernelSpectralFormOperator z)) (8/9:ℂ) := by
  apply kernelLocalEnergyResolvent_meromorphicAt.congr
  filter_upwards [kernelRegularPencil_eventually_isUnit.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hne
  exact kernelLocalEnergyResolvent_eq_inverse z hne hz

end

open scoped Topology

lemma meromorphicAt_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (A : E→L[ℂ]F) {f : ℂ→E} {z : ℂ}
    (hf : MeromorphicAt f z) : MeromorphicAt (fun w => A (f w)) z := by
  obtain ⟨n,hn⟩ := hf
  refine ⟨n,?_⟩
  have hh := (A.analyticAt ((z-z)^n•f z)).comp_of_eq hn rfl
  simpa only [Function.comp_def,map_smul] using hh

lemma meromorphicAt_bilinear {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (B : E→L[ℂ]F→L[ℂ]G) {f : ℂ→E} {g : ℂ→F} {z : ℂ}
    (hf : MeromorphicAt f z) (hg : MeromorphicAt g z) :
    MeromorphicAt (fun w => B (f w) (g w)) z := by
  obtain ⟨m,hm⟩ := hf
  obtain ⟨n,hn⟩ := hg
  refine ⟨m+n,?_⟩
  have hh := (B.analyticAt_bilinear (((z-z)^m•f z),((z-z)^n•g z))).comp₂ hm hn
  simpa only [map_smul,_root_.smul_apply,smul_smul,pow_add,mul_comm] using hh

lemma meromorphicAt_clm_apply {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {A : ℂ→E→L[ℂ]F} {f : ℂ→E} {z : ℂ}
    (hA : MeromorphicAt A z) (hf : MeromorphicAt f z) :
    MeromorphicAt (fun w => A w (f w)) z :=
  meromorphicAt_bilinear (ContinuousLinearMap.apply ℂ F) hf hA

lemma selfAdjoint_pencil_isUnit_nonreal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (S : H→L[ℂ]H)
    (hS : IsSelfAdjoint S) (z : ℂ) (hz : z.im≠0) : IsUnit (1-z•S) := by
  have hne : z≠0 := fun h => hz (by rw [h]; rfl)
  have hi : z⁻¹.im≠0 := by
    rw [Complex.inv_im]
    exact div_ne_zero (neg_ne_zero.mpr hz) (mt Complex.normSq_eq_zero.mp hne)
  have hout : z⁻¹∉spectrum ℂ S := fun h => hi (hS.im_eq_zero_of_mem_spectrum h)
  have hu := (spectrum.notMem_iff (R := ℂ) (A := H→L[ℂ]H)).mp hout
  have hv := hu.smul (Units.mk0 z hne)
  simpa only [Units.smul_def,Units.val_mk0,Algebra.algebraMap_eq_smul_one,
    smul_sub,smul_smul,mul_inv_cancel₀ hne,one_smul] using hv

lemma kernelSpectralFormOperator_isUnit_nonreal (z : ℂ) (hz : z.im≠0) :
    IsUnit (kernelSpectralFormOperator z) := by
  exact selfAdjoint_pencil_isUnit_nonreal kernelMassGram kernelMassGram_selfAdjoint (z+1)
    (by simpa using hz)

lemma kernelSpectralFormInverse_analyticAt_of_isUnit (z : ℂ)
    (hz : IsUnit (kernelSpectralFormOperator z)) :
    AnalyticAt ℂ (fun w => Ring.inverse (kernelSpectralFormOperator w)) z := by
  have hi := (analyticOnNhd_inverse (𝕜 := ℂ)
    (A := KernelEnergyGraph→L[ℂ]KernelEnergyGraph)) (kernelSpectralFormOperator z) hz
  exact hi.comp_of_eq (kernelSpectralFormOperator_analyticAt z) rfl

lemma kernelSpectralFormInverse_analyticAt_nonreal (z : ℂ) (hz : z.im≠0) :
    AnalyticAt ℂ (fun w => Ring.inverse (kernelSpectralFormOperator w)) z :=
  kernelSpectralFormInverse_analyticAt_of_isUnit z (kernelSpectralFormOperator_isUnit_nonreal z hz)

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

def kernelL2SandwichCLM : (KernelEnergyGraph→L[ℂ]KernelEnergyGraph)→L[ℂ]
    (KernelQuotientL2→L[ℂ]KernelQuotientL2) :=
  continuousLinearSandwich kernelEnergyMass kernelEnergyMass.adjoint

def kernelSpectralResolvent (z : ℂ) : KernelQuotientL2→L[ℂ]KernelQuotientL2 :=
  kernelL2SandwichCLM (Ring.inverse (kernelSpectralFormOperator z))

lemma kernelSpectralResolvent_apply (z : ℂ) (F : KernelQuotientL2) :
    kernelSpectralResolvent z F=
      kernelEnergyMass (Ring.inverse (kernelSpectralFormOperator z) (kernelVariationalSolution F)) := rfl

private lemma meromorphicAt_operator_clm {H G : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (A : (H →L[ℂ] H) →L[ℂ] (G →L[ℂ] G))
    {f : ℂ → (H →L[ℂ] H)} {z : ℂ} (hf : MeromorphicAt f z) :
    MeromorphicAt (fun w => A (f w)) z :=
  meromorphicAt_clm A hf

lemma kernelSpectralResolvent_meromorphicAt :
    MeromorphicAt kernelSpectralResolvent (8/9:ℂ) := by
  exact meromorphicAt_operator_clm
    (H := KernelEnergyGraph) (G := KernelQuotientL2)
    (f := fun z : ℂ => Ring.inverse (kernelSpectralFormOperator z))
    kernelL2SandwichCLM kernelSpectralFormInverse_meromorphicAt

lemma kernelSpectralResolvent_analyticAt_nonreal (z : ℂ) (hz : z.im≠0) :
    AnalyticAt ℂ kernelSpectralResolvent z := by
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := KernelEnergyGraph→L[ℂ]KernelEnergyGraph)
    (F := KernelQuotientL2→L[ℂ]KernelQuotientL2) kernelL2SandwichCLM
      (Ring.inverse (kernelSpectralFormOperator z))).comp_of_eq
    (kernelSpectralFormInverse_analyticAt_nonreal z hz) rfl

lemma kernelSpectralResolvent_graph (z : ℂ) (hz : IsUnit (kernelSpectralFormOperator z))
    (F : KernelQuotientL2) :
    (kernelSpectralResolvent z F,F+z•kernelSpectralResolvent z F)∈kernelEnergyLaplacian.graph := by
  apply kernelSpectralFormOperator_solution_graph z F
  have hi := congrArg (fun A : KernelEnergyGraph→L[ℂ]KernelEnergyGraph =>
    A (kernelVariationalSolution F)) (Ring.mul_inverse_cancel (kernelSpectralFormOperator z) hz)
  exact hi

lemma kernelSpectralResolvent_left_inverse (z : ℂ) (hz : IsUnit (kernelSpectralFormOperator z))
    (u : kernelEnergyLaplacian.domain) :
    kernelSpectralResolvent z (kernelEnergyLaplacian u-z•(u:KernelQuotientL2))=u := by
  rw [kernelSpectralResolvent_apply,←kernelSpectralFormOperator_of_domain z u]
  have hi := congrArg (fun A : KernelEnergyGraph→L[ℂ]KernelEnergyGraph =>
    A (kernelVariationalSolution (kernelEnergyLaplacian u+u)))
      (Ring.inverse_mul_cancel (kernelSpectralFormOperator z) hz)
  change Ring.inverse (kernelSpectralFormOperator z)
    (kernelSpectralFormOperator z (kernelVariationalSolution (kernelEnergyLaplacian u+u)))=
      kernelVariationalSolution (kernelEnergyLaplacian u+u) at hi
  rw [hi]
  exact kernelEnergyLaplacian_resolvent_relation u

lemma kernelSpectralResolvent_unique (z : ℂ) (hz : IsUnit (kernelSpectralFormOperator z))
    (u F : KernelQuotientL2) (hu : (u,F+z•u)∈kernelEnergyLaplacian.graph) :
    kernelSpectralResolvent z F=u := by
  let v : kernelEnergyLaplacian.domain := ⟨u,LinearPMap.mem_domain_of_mem_graph hu⟩
  have hv : kernelEnergyLaplacian v=F+z•u :=
    kernelEnergyLaplacian.mem_graph_snd_inj (kernelEnergyLaplacian.mem_graph v) hu rfl
  have hh := kernelSpectralResolvent_left_inverse z hz v
  rw [hv] at hh
  simpa only [v,add_sub_cancel_right] using hh

def kernelEisensteinSpectralParameter (s : ℂ) : ℂ := s*(2-s)

def kernelEisensteinResolvent (s : ℂ) : KernelQuotientL2→L[ℂ]KernelQuotientL2 :=
  kernelSpectralResolvent (kernelEisensteinSpectralParameter s)

lemma kernelEisensteinSpectralParameter_center :
    kernelEisensteinSpectralParameter (4/3)=8/9 := by
  norm_num [kernelEisensteinSpectralParameter]

lemma kernelEisensteinResolvent_meromorphicAt :
    MeromorphicAt kernelEisensteinResolvent (4/3:ℂ) := by
  have hh : MeromorphicAt kernelSpectralResolvent (kernelEisensteinSpectralParameter (4/3)) := by
    rw [kernelEisensteinSpectralParameter_center]
    exact kernelSpectralResolvent_meromorphicAt
  exact hh.comp_analyticAt (by unfold kernelEisensteinSpectralParameter; fun_prop)

lemma kernelEisensteinSpectralParameter_nonreal (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    (kernelEisensteinSpectralParameter s).im≠0 := by
  have he : (kernelEisensteinSpectralParameter s).im=2*(1-s.re)*s.im := by
    simp only [kernelEisensteinSpectralParameter,Complex.mul_im,Complex.sub_re,Complex.sub_im]
    norm_num
    ring
  rw [he]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hs.symm)) hi

lemma kernelEisensteinResolvent_analyticAt_nonreal (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ kernelEisensteinResolvent s := by
  exact (kernelSpectralResolvent_analyticAt_nonreal _
    (kernelEisensteinSpectralParameter_nonreal s hs hi)).comp_of_eq
      (by unfold kernelEisensteinSpectralParameter; fun_prop) rfl

lemma kernelEisensteinResolvent_forcing_meromorphicAt
    (F : ℂ→KernelQuotientL2) (hF : MeromorphicAt F (4/3:ℂ)) :
    MeromorphicAt (fun s => kernelEisensteinResolvent s (F s)) (4/3:ℂ) :=
  meromorphicAt_clm_apply kernelEisensteinResolvent_meromorphicAt hF

lemma kernelEisensteinPencil_eventually_isUnit :
    ∀ᶠ s : ℂ in 𝓝[≠] (4/3:ℂ), IsUnit (kernelSpectralFormOperator (kernelEisensteinSpectralParameter s)) := by
  have hc : ContinuousAt kernelEisensteinSpectralParameter (4/3:ℂ) := by
    unfold kernelEisensteinSpectralParameter
    fun_prop
  have hp : ∀ᶠ s : ℂ in 𝓝 (4/3:ℂ), IsUnit (kernelRegularPencil (kernelEisensteinSpectralParameter s)) := by
    have hh : ∀ᶠ z : ℂ in 𝓝 (kernelEisensteinSpectralParameter (4/3)), IsUnit (kernelRegularPencil z) := by
      rw [kernelEisensteinSpectralParameter_center]
      exact kernelRegularPencil_eventually_isUnit
    exact hc.eventually hh
  filter_upwards [hp.filter_mono nhdsWithin_le_nhds,
    eventually_ne_nhdsWithin (show (4/3:ℂ)≠2/3 by norm_num),self_mem_nhdsWithin] with s hs htwo hfour
  apply kernelSpectralFormOperator_isUnit_near _ _ hs
  intro he
  have hzero : (s-4/3)*(s-2/3)=0 := by
    have hid : (s-4/3)*(s-2/3)=(8/9:ℂ)-kernelEisensteinSpectralParameter s := by
      unfold kernelEisensteinSpectralParameter
      ring
    rw [hid,he,sub_self]
  rcases mul_eq_zero.mp hzero with h | h
  · exact hfour (sub_eq_zero.mp h)
  · exact htwo (sub_eq_zero.mp h)

def kernelEisensteinL2Correction (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    KernelQuotientL2 :=
  kernelEisensteinResolvent s (kernelL2Defect a b ha hab s)

lemma kernelEisensteinL2Correction_meromorphicAt (a b : ℝ) (ha : 0<a) (hab : a<b) :
    MeromorphicAt (kernelEisensteinL2Correction a b ha hab) (4/3:ℂ) :=
  kernelEisensteinResolvent_forcing_meromorphicAt _
    ((kernelL2Defect_entire a b ha hab).analyticAt (4/3)).meromorphicAt

lemma kernelEisensteinL2Correction_analyticAt_nonreal
    (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (kernelEisensteinL2Correction a b ha hab) s := by
  exact ((ContinuousLinearMap.apply ℂ KernelQuotientL2).analyticAt_bilinear
    (kernelL2Defect a b ha hab s,kernelEisensteinResolvent s)).comp₂
      ((kernelL2Defect_entire a b ha hab).analyticAt s)
      (kernelEisensteinResolvent_analyticAt_nonreal s hs hi)

lemma kernelEisensteinL2Correction_graph (a b : ℝ) (ha : 0<a) (hab : a<b)
    (s : ℂ) (hs : IsUnit (kernelSpectralFormOperator (kernelEisensteinSpectralParameter s))) :
    (kernelEisensteinL2Correction a b ha hab s,
      kernelL2Defect a b ha hab s + kernelEisensteinSpectralParameter s •
        kernelEisensteinL2Correction a b ha hab s)∈kernelEnergyLaplacian.graph :=
  kernelSpectralResolvent_graph _ hs _

lemma kernelEisensteinL2Correction_graph_nonreal (a b : ℝ) (ha : 0<a) (hab : a<b)
    (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    (kernelEisensteinL2Correction a b ha hab s,
      kernelL2Defect a b ha hab s + kernelEisensteinSpectralParameter s •
        kernelEisensteinL2Correction a b ha hab s)∈kernelEnergyLaplacian.graph :=
  kernelEisensteinL2Correction_graph a b ha hab s
    (kernelSpectralFormOperator_isUnit_nonreal _ (kernelEisensteinSpectralParameter_nonreal s hs hi))

lemma kernelEisensteinL2Correction_graph_eventually (a b : ℝ) (ha : 0<a) (hab : a<b) :
    ∀ᶠ s : ℂ in 𝓝[≠] (4/3:ℂ),
    (kernelEisensteinL2Correction a b ha hab s,
      kernelL2Defect a b ha hab s + kernelEisensteinSpectralParameter s •
        kernelEisensteinL2Correction a b ha hab s)∈kernelEnergyLaplacian.graph := by
  filter_upwards [kernelEisensteinPencil_eventually_isUnit] with s hs
  exact kernelEisensteinL2Correction_graph a b ha hab s hs

lemma kernelEisensteinL2Correction_unique (a b : ℝ) (ha : 0<a) (hab : a<b)
    (s : ℂ) (hs : IsUnit (kernelSpectralFormOperator (kernelEisensteinSpectralParameter s)))
    (u : KernelQuotientL2)
    (hu : (u,kernelL2Defect a b ha hab s+kernelEisensteinSpectralParameter s•u)∈kernelEnergyLaplacian.graph) :
    kernelEisensteinL2Correction a b ha hab s=u :=
  kernelSpectralResolvent_unique _ hs _ _ hu

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

def kernelThetaMassProjection : KernelQuotientL2→L[ℂ]KernelQuotientL2 :=
  kernelL2SandwichCLM kernelThetaNull.starProjection

def kernelRegularL2Resolvent (z : ℂ) : KernelQuotientL2→L[ℂ]KernelQuotientL2 :=
  kernelL2SandwichCLM (kernelRegularInverseLift z)

lemma kernelRegularL2Resolvent_analyticAt :
    AnalyticAt ℂ kernelRegularL2Resolvent (8/9:ℂ) := by
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := KernelEnergyGraph→L[ℂ]KernelEnergyGraph)
    (F := KernelQuotientL2→L[ℂ]KernelQuotientL2) kernelL2SandwichCLM
      (kernelRegularInverseLift (8/9))).comp_of_eq kernelRegularInverseLift_analyticAt rfl

lemma kernelSpectralResolvent_decomposition (z : ℂ) (hne : z≠8/9)
    (hz : IsUnit (kernelRegularPencil z)) (F : KernelQuotientL2) :
    kernelSpectralResolvent z F=((17/9)/(8/9-z):ℂ)•kernelThetaMassProjection F+
      kernelRegularL2Resolvent z F := by
  unfold kernelSpectralResolvent
  rw [←kernelLocalEnergyResolvent_eq_inverse z hne hz]
  simp only [kernelLocalEnergyResolvent,map_add,map_smul,_root_.add_apply,
    _root_.smul_apply,kernelThetaMassProjection,kernelRegularL2Resolvent]

def kernelEisensteinCorrectionNumerator (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    KernelQuotientL2 :=
  ((17/9)/(s-2/3):ℂ)•kernelThetaMassProjection (kernelL2Defect a b ha hab s)+
    (s-4/3)•kernelRegularL2Resolvent (kernelEisensteinSpectralParameter s)
      (kernelL2Defect a b ha hab s)

def kernelEisensteinResidueVector (a b : ℝ) (ha : 0<a) (hab : a<b) : KernelQuotientL2 :=
  (17/6:ℂ)•kernelThetaMassProjection (kernelL2Defect a b ha hab (4/3))

lemma kernelEisensteinCorrectionNumerator_center (a b : ℝ) (ha : 0<a) (hab : a<b) :
    kernelEisensteinCorrectionNumerator a b ha hab (4/3)=kernelEisensteinResidueVector a b ha hab := by
  simp only [kernelEisensteinCorrectionNumerator,kernelEisensteinResidueVector,sub_self,zero_smul,add_zero]
  congr 1
  norm_num

lemma kernelEisensteinCorrectionNumerator_analyticAt (a b : ℝ) (ha : 0<a) (hab : a<b) :
    AnalyticAt ℂ (kernelEisensteinCorrectionNumerator a b ha hab) (4/3:ℂ) := by
  have hf := (kernelL2Defect_entire a b ha hab).analyticAt (4/3:ℂ)
  have hp := (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2)
    (F := KernelQuotientL2) kernelThetaMassProjection (kernelL2Defect a b ha hab (4/3))).comp_of_eq hf rfl
  have hr : AnalyticAt ℂ (fun s => kernelRegularL2Resolvent (kernelEisensteinSpectralParameter s)) (4/3:ℂ) := by
    have hreg : AnalyticAt ℂ kernelRegularL2Resolvent (kernelEisensteinSpectralParameter (4/3)) := by
      rw [kernelEisensteinSpectralParameter_center]
      exact kernelRegularL2Resolvent_analyticAt
    exact hreg.comp_of_eq (by unfold kernelEisensteinSpectralParameter; fun_prop) rfl
  have happ := ((ContinuousLinearMap.apply ℂ KernelQuotientL2).analyticAt_bilinear
    (kernelL2Defect a b ha hab (4/3),kernelRegularL2Resolvent (kernelEisensteinSpectralParameter (4/3)))).comp₂ hf hr
  have hscalar : AnalyticAt ℂ (fun s : ℂ => (17/9)/(s-2/3)) (4/3:ℂ) := by
    apply AnalyticAt.div analyticAt_const (analyticAt_id.sub analyticAt_const)
    norm_num
  exact (hscalar.smul hp).add ((analyticAt_id.sub analyticAt_const).smul happ)

lemma kernelEisensteinCorrectionNumerator_eventually (a b : ℝ) (ha : 0<a) (hab : a<b) :
    ∀ᶠ s : ℂ in 𝓝[≠] (4/3:ℂ),
      (s-4/3)•kernelEisensteinL2Correction a b ha hab s=
        kernelEisensteinCorrectionNumerator a b ha hab s := by
  have hc : ContinuousAt kernelEisensteinSpectralParameter (4/3:ℂ) := by
    unfold kernelEisensteinSpectralParameter
    fun_prop
  have hp : ∀ᶠ s : ℂ in 𝓝 (4/3:ℂ), IsUnit (kernelRegularPencil (kernelEisensteinSpectralParameter s)) := by
    have hh : ∀ᶠ z : ℂ in 𝓝 (kernelEisensteinSpectralParameter (4/3)), IsUnit (kernelRegularPencil z) := by
      rw [kernelEisensteinSpectralParameter_center]
      exact kernelRegularPencil_eventually_isUnit
    exact hc.eventually hh
  filter_upwards [hp.filter_mono nhdsWithin_le_nhds,
    eventually_ne_nhdsWithin (show (4/3:ℂ)≠2/3 by norm_num),self_mem_nhdsWithin] with s hs htwo hfour
  have hfactor : (8/9:ℂ)-kernelEisensteinSpectralParameter s=(s-4/3)*(s-2/3) := by
    unfold kernelEisensteinSpectralParameter
    ring
  have hne : kernelEisensteinSpectralParameter s≠8/9 := by
    intro he
    have hh := mul_ne_zero (sub_ne_zero.mpr hfour) (sub_ne_zero.mpr htwo)
    rw [←hfactor,he,sub_self] at hh
    exact hh rfl
  change (s-4/3)•kernelSpectralResolvent (kernelEisensteinSpectralParameter s)
    (kernelL2Defect a b ha hab s)=_
  rw [kernelSpectralResolvent_decomposition _ hne hs,smul_add,smul_smul]
  have hscalar : (s-4/3)*((17/9)/(8/9-kernelEisensteinSpectralParameter s))=(17/9)/(s-2/3) := by
    rw [hfactor]
    have hcancel (x y c : ℂ) (hx : x≠0) : x*(c/(x*y))=c/y := by
      rw [div_eq_mul_inv,mul_inv_rev]
      calc
        _ = (x*x⁻¹)*(c*y⁻¹) := by ring
        _ = c/y := by rw [mul_inv_cancel₀ hx,one_mul,div_eq_mul_inv]
    exact hcancel _ _ _ (sub_ne_zero.mpr hfour)
  rw [hscalar]
  rfl

lemma kernelEisensteinResidueVector_limit (a b : ℝ) (ha : 0<a) (hab : a<b) :
    Tendsto (fun s : ℂ => (s-4/3)•kernelEisensteinL2Correction a b ha hab s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (kernelEisensteinResidueVector a b ha hab)) := by
  apply (tendsto_congr' (kernelEisensteinCorrectionNumerator_eventually a b ha hab)).mpr
  rw [←kernelEisensteinCorrectionNumerator_center a b ha hab]
  exact (kernelEisensteinCorrectionNumerator_analyticAt a b ha hab).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds

instance kernelThetaMassProjection_range_finiteDimensional :
    FiniteDimensional ℂ kernelThetaMassProjection.range := by
  let B : kernelThetaNull→L[ℂ]KernelQuotientL2 := kernelEnergyMass.comp kernelThetaNull.subtypeL
  have : FiniteDimensional ℂ B.range := LinearMap.finiteDimensional_range B.toLinearMap
  apply Submodule.finiteDimensional_of_le (S₂ := B.range)
  rintro y ⟨x,rfl⟩
  exact ⟨kernelThetaNull.orthogonalProjectionOnto (kernelEnergyMass.adjoint x),rfl⟩

lemma kernelEisensteinResidueVector_graph (a b : ℝ) (ha : 0<a) (hab : a<b) :
    (kernelEisensteinResidueVector a b ha hab,(8/9:ℂ)•kernelEisensteinResidueVector a b ha hab)
      ∈kernelEnergyLaplacian.graph := by
  let v : KernelEnergyGraph := (17/6:ℂ)•kernelThetaNull.starProjection
    (kernelVariationalSolution (kernelL2Defect a b ha hab (4/3)))
  have hv : kernelSpectralFormOperator (8/9) v=kernelVariationalSolution 0 := by
    change kernelSpectralFormOperator (8/9) ((17/6:ℂ)•kernelThetaNull.starProjection _)=_
    rw [map_smul]
    have hz : kernelSpectralFormOperator (8/9) (kernelThetaNull.starProjection
        (kernelVariationalSolution (kernelL2Defect a b ha hab (4/3))))=0 :=
      kernelThetaNull.starProjection_apply_mem _
    rw [hz,smul_zero,map_zero]
  have hh := kernelSpectralFormOperator_solution_graph (8/9) 0 v hv
  simpa only [v,map_smul,zero_add,kernelEisensteinResidueVector,kernelThetaMassProjection,
    kernelL2SandwichCLM,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply,kernelVariationalSolution] using! hh

end CubicEisenstein

end

end OAI
