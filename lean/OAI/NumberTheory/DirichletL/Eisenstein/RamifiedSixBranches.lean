import OAI.NumberTheory.DirichletL.Eisenstein.CorrespondencePullback

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
open scoped BigOperators Classical Topology MatrixGroups

section
open CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

def arbitraryIntervalWhittaker (a b:ℝ) (ρ:BoundedContinuousFunction ℝ ℂ) (freq s:ℂ) :ℂ:=
  ∫v in Set.Icc a b,ρ v*(v:ℂ)^(-s-1)*sourceFourierKernel s (freq*v)

lemma arbitraryIntervalWhittaker_analyticAt (a b:ℝ) (ha:0<a)
    (ρ:BoundedContinuousFunction ℝ ℂ) (freq s:ℂ) (hs:1<s.re) :
    AnalyticAt ℂ (arbitraryIntervalWhittaker a b ρ freq) s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
  exact cuspWeightedWhittakerInterval_differentiableAt ρ a b ha freq w hw

lemma ramifiedSource_height_fourier_average (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side))
    (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (s:ℂ) (hs:2<s.re) :
    (∫w in cuspPeriodStrip a b,sourceEisenstein s
      (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis))•w)*
        arbitraryCuspWeightedPhase ρ (ninthCuspFrequency h) w∂hyperbolicVolume)=
      ramifiedCuspGaussSeries side h hf s*arbitraryIntervalWhittaker a b ρ (ninthCuspFrequency h) s := by
  let M:=integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis))
  let g:HyperbolicSpace→ℂ:=fun w=>sourceEisenstein s (M•w)*
    arbitraryCuspWeightedPhase ρ (ninthCuspFrequency h) w
  have hg:Continuous g:=((sourceProjection_continuous _ (hyperbolicEisenstein_continuous s hs)).comp
    (continuous_hyperbolic_action M)).mul (arbitraryCuspWeightedPhase_continuous ρ _)
  rw [cuspPeriodStrip_integral_coordinates_of_pos a b ha g hg.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha g hg)]
  rw [arbitraryIntervalWhittaker,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hv0:0<v:=ha.trans_le hv.1
  have hvz:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv0.ne'
  have hinner:(∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
      ρ v*((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
        ramifiedCuspGaussSeries side h hf s:=by
    simp only [g,cuspCoordinateLift_positive v _ hv0,arbitraryCuspWeightedPhase,
      hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
    have he (z:ℂ):sourceEisenstein s (M•upperPoint z v hv0)*
        (ρ v*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ρ v*(sourceEisenstein s (M•upperPoint z v hv0)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z)):=by ring
    simp_rw [he]
    rw [integral_const_mul,ramifiedSourceEisenstein_fourier side h hf v hv0 s hs]
    ring
  have hp:(v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3:=by
    rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hvz]
    congr 1
    exact Complex.cpow_natCast _ 3
  dsimp only
  rw [hinner,hp]
  ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

abbrev RamifiedSixBranch := Unit ⊕ (Unit ⊕ (Unit ⊕ Fin 3))

def unitCuspUnramifiedIndex (u t:Eisˣ) (h:Eis) :Eis:=
  3*((↑u⁻¹:Eis)^2*(t:Eis))^2*((↑t⁻¹:Eis)*h)

def ramifiedSixIndex (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side)) :RamifiedSixBranch→Eis
  | .inl _=>unitCuspUnramifiedIndex 1 (ramifiedCuspRoot side) h
  | .inr (.inl _)=>unitCuspUnramifiedIndex (-(ramifiedCuspRoot side)) (-(ramifiedCuspRoot side)) h
  | .inr (.inr (.inl _))=>unitCuspUnramifiedIndex (-(ramifiedCuspRoot side)) 1 h
  | .inr (.inr (.inr l))=>3*((↑(-(ramifiedCuspRoot side))⁻¹:Eis)^2*
      (onceCuspScale (ramifiedCuspScaleUnit side)*omega^l.val))^2*
        onceCuspFrequencyQuotient (ramifiedCuspScaleUnit side) h hf l

def ramifiedSixWeight (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side)) (i:RamifiedSixBranch) (s:ℂ) :ℂ:=
  let t:=ramifiedCuspRoot side
  let phase:=ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (↑t⁻¹:Eis))
  match i with
  | .inl _=>(4:ℂ)⁻¹*ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (t:Eis))
  | .inr (.inl _)=>(4:ℂ)⁻¹*phase*ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding ((-t:Eisˣ):Eis))
  | .inr (.inr (.inl _))=>(4:ℂ)⁻¹*phase*ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding ((1:Eisˣ):Eis))
  | .inr (.inr (.inr l))=>(4:ℂ)⁻¹*phase*
      (if (3:Eis)∣onceCuspFrequencyQuotient (ramifiedCuspScaleUnit side) h hf l+
          ramifiedAffineParameter (onceCuspRayIndex (-t) (ramifiedCuspScaleUnit side) l).val 1 then
        (3:ℂ)*(3:ℂ)^(-s)*ShortDraftTrace.breveE
          (ninthCuspFrequency h/eisEmbedding (onceCuspScale (ramifiedCuspScaleUnit side)*omega^l.val)) else 0)

lemma ramifiedSixWeight_analytic (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side)) (i:RamifiedSixBranch) (s:ℂ) :
    AnalyticAt ℂ (ramifiedSixWeight side h hf i) s := by
  rcases i with i|i
  · exact analyticAt_const
  rcases i with i|i
  · exact analyticAt_const
  rcases i with i|i
  · exact analyticAt_const
  unfold ramifiedSixWeight
  dsimp only
  split_ifs
  · apply analyticAt_const.mul
    apply AnalyticAt.mul _ analyticAt_const
    apply analyticAt_const.mul
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    exact Eventually.of_forall (fun z=>(differentiableAt_id.neg).const_cpow (Or.inl (by norm_num)))
  · exact analyticAt_const

lemma ramifiedCuspGaussSeries_eq_six (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side)) (s:ℂ) :
    ramifiedCuspGaussSeries side h hf s=
      ∑i:RamifiedSixBranch,ramifiedSixWeight side h hf i s*
        unramifiedCubicGaussSeries s (ramifiedSixIndex side h hf i) := by
  simp only [Fintype.sum_sum_type,Fintype.sum_unique,ramifiedSixWeight,ramifiedSixIndex,
    ramifiedCuspGaussSeries,unitCuspGaussSeries,unitCuspUnramifiedIndex,onceCuspGaussSeries]
  simp only [Fin.sum_univ_three]
  split_ifs <;> ring

def ramifiedArithmeticResidue (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side)) :ℂ:=
  ∑i:RamifiedSixBranch,ramifiedSixWeight side h hf i (4/3)*
    unramifiedGaussResidue (ramifiedSixIndex side h hf i)

end

open CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

theorem ramifiedSource_height_residue (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side))
    (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) :
    sourceArbitraryHeightFourier
      (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis)))
      a b ha ρ (ninthCuspFrequency h) cubicEisensteinResidue=
      ramifiedArithmeticResidue side h hf*
        arbitraryIntervalWhittaker a b ρ (ninthCuspFrequency h) (4/3) := by
  let M:=integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis))
  let coeff:RamifiedSixBranch→ℂ→ℂ:=fun i s=>
    ramifiedSixWeight side h hf i s*arbitraryIntervalWhittaker a b ρ (ninthCuspFrequency h) s
  have hc:∀i s,1<s.re→AnalyticAt ℂ (coeff i) s:=fun i s hs=>
    (ramifiedSixWeight_analytic side h hf i s).mul
      (arbitraryIntervalWhittaker_analyticAt a b ha ρ (ninthCuspFrequency h) s hs)
  have he:=finite_unramified_residue (ramifiedSixIndex side h hf) coeff hc
    (sourceArbitraryHeightFamily M a b ha ρ (ninthCuspFrequency h))
    (sourceArbitraryHeightFourier M a b ha ρ (ninthCuspFrequency h) cubicEisensteinResidue)
    (sourceArbitraryHeightFamily_analyticAt M a b ha ρ (ninthCuspFrequency h))
    (sourceArbitraryHeightFamily_residue_limit M a b ha ρ (ninthCuspFrequency h)) (by
      intro s hs hi
      rw [sourceArbitraryHeightFamily_initial M a b ha ρ (ninthCuspFrequency h) s hs hi,
        ramifiedSource_height_fourier_average side h hf a b ha ρ s (by linarith),
        ramifiedCuspGaussSeries_eq_six,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi'
      dsimp only [coeff]
      ring)
  refine he.trans ?_
  rw [ramifiedArithmeticResidue,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [coeff]
  ring

theorem ramifiedSource_height_residue_integral (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side))
    (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) :
    (∫w in cuspPeriodStrip a b,
      ramifiedSourceFunction (ramifiedCuspRoot side:Eis) w*
        arbitraryCuspWeightedPhase ρ (ninthCuspFrequency h) w∂hyperbolicVolume)=
      ramifiedArithmeticResidue side h hf*
        arbitraryIntervalWhittaker a b ρ (ninthCuspFrequency h) (4/3) := by
  unfold ramifiedSourceFunction
  rw [←sourceArbitraryHeightFourier_residue_integral
    (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis))) a b ha ρ (ninthCuspFrequency h)]
  exact ramifiedSource_height_residue side h hf a b ha ρ

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise Manifold ContDiff ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O

variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)

def kernelCorrespondenceMatrix (q : IntegralCoverCosets H globalKubotaKernel) : SL(2,ℂ) :=
  g*integralComplexMatrix (((integralCoverRep H globalKubotaKernel q)⁻¹:globalKubotaKernel):SL(2,ActualEisensteinCubic.O))

lemma kernelCorrespondenceTest_field (f : kernelSmoothTests) (p : EuclideanSpatial) :
    kernelTestField (kernelCorrespondenceTest hHK hJK e g he f) p=
      letI : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
      ∑q : IntegralCoverCosets H globalKubotaKernel,
        kernelTestField f (euclideanAction (kernelCorrespondenceMatrix g q) p) := by
  let : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
  change kernelCorrespondenceFunction hJK e g he f.1
    (integralOrbitProjection globalKubotaKernel (euclideanToHyperbolic p))=_
  rw [kernelCorrespondenceFunction_lift]
  apply Finset.sum_congr rfl
  intro q _
  change f.1 (integralOrbitProjection globalKubotaKernel
      (kernelCorrespondenceMatrix g q•euclideanToHyperbolic p))=
    f.1 (integralOrbitProjection globalKubotaKernel
      (euclideanToHyperbolic (euclideanAction (kernelCorrespondenceMatrix g q) p)))
  rw [euclideanAction,euclideanToHyperbolic_coordinates]

lemma kernelCorrespondenceTest_energyDensity_le (f : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelTestEnergyDensity (kernelCorrespondenceTest hHK hJK e g he f) w≤
      (H.relIndex globalKubotaKernel:ℝ)*
        (kernelCorrespondenceFunction hJK e g he (fun q=>(kernelQuotientEnergyDensity f q:ℂ))
          (integralOrbitProjection globalKubotaKernel w)).re := by
  let : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
  let p := hyperbolicEuclideanCoordinates w
  let A := kernelCorrespondenceMatrix (H:=H) g
  have hFd (q : IntegralCoverCosets H globalKubotaKernel) :
      DifferentiableAt ℝ (kernelTestField f) (euclideanAction (A q) p) :=
    (kernelTestField_contDiffAt f _ (euclideanAction_positive _ _)).differentiableAt (by simp)
  have hcomp (q : IntegralCoverCosets H globalKubotaKernel) :
      DifferentiableAt ℝ (kernelTestField f ∘ euclideanAction (A q)) p := by
    obtain ⟨der,hder,_⟩ := hyperbolicDifferentialIsometry (A q) p (hyperbolicHeight_pos w)
    exact (hFd q).comp p hder.differentiableAt
  have hh := coverEnergyDensity_sum_le Finset.univ
    (fun q : IntegralCoverCosets H globalKubotaKernel=>kernelTestField f ∘ euclideanAction (A q))
    p (fun q _=>hcomp q)
  have hfield : kernelTestField (kernelCorrespondenceTest hHK hJK e g he f)=
      fun p=>∑q : IntegralCoverCosets H globalKubotaKernel,kernelTestField f (euclideanAction (A q) p) :=
    funext (kernelCorrespondenceTest_field hHK hJK e g he f)
  rw [kernelTestEnergyDensity_eq_cover,hfield]
  change coverEnergyDensity (fun p=>∑q : IntegralCoverCosets H globalKubotaKernel,
    kernelTestField f (euclideanAction (A q) p)) p≤_
  calc
    _ ≤ (Fintype.card (IntegralCoverCosets H globalKubotaKernel):ℝ)*
        ∑q : IntegralCoverCosets H globalKubotaKernel,
          coverEnergyDensity (kernelTestField f ∘ euclideanAction (A q)) p := by
      simpa only [Finset.card_univ,Function.comp_def] using hh
    _ = _ := by
      have hcard : Fintype.card (IntegralCoverCosets H globalKubotaKernel)=
          H.relIndex globalKubotaKernel := by
        rw [Subgroup.relIndex,Subgroup.index,Nat.card_eq_fintype_card]
      rw [hcard,kernelCorrespondenceFunction_lift]
      simp only [Complex.re_sum,Complex.ofReal_re]
      congr 1
      apply Finset.sum_congr rfl
      intro q _
      rw [coverEnergyDensity_comp (A q) _ p (hyperbolicHeight_pos w) (hFd q)]
      change coverEnergyDensity (kernelTestField f) (euclideanAction (A q) p)=
        kernelTestEnergyDensity f (A q•w)
      rw [kernelTestEnergyDensity_eq_cover]
      congr 1
      dsimp [p,euclideanAction]
      rw [euclideanToHyperbolic_coordinates]

lemma kernelCorrespondenceTest_energy_le (f : kernelSmoothTests) :
    kernelDirichletEnergy (kernelCorrespondenceTest hHK hJK e g he f)≤
      (H.relIndex globalKubotaKernel:ℝ)*(J.relIndex globalKubotaKernel:ℝ)*kernelDirichletEnergy f := by
  let density : KernelQuotient→ℂ := fun q=>(kernelQuotientEnergyDensity f q:ℂ)
  have hdm : Measurable density := Complex.continuous_ofReal.measurable.comp
    (kernelQuotientEnergyDensity_continuous f).measurable
  have hdi : Integrable density (integralQuotientVolume globalKubotaKernel) :=
    (kernelQuotientEnergyDensity_integrable f).ofReal
  have hTi := kernelCorrespondenceFunction_integrable hHK hJK e g he density hdm hdi
  have hint := kernelCorrespondenceFunction_integral hHK hJK e g he density hdm hdi
  have hre : (∫q,(kernelCorrespondenceFunction hJK e g he density q).re
      ∂integralQuotientVolume globalKubotaKernel)=
        (J.relIndex globalKubotaKernel:ℝ)*kernelDirichletEnergy f := by
    have htr := integral_re hTi
    have hdf := integral_re hdi
    simp only [RCLike.re_to_complex] at htr hdf
    rw [htr,hint]
    simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]
    rw [←hdf]
    rfl
  unfold kernelDirichletEnergy
  calc
    _ ≤ ∫q,(H.relIndex globalKubotaKernel:ℝ)*
        (kernelCorrespondenceFunction hJK e g he density q).re
        ∂integralQuotientVolume globalKubotaKernel := by
      apply integral_mono (kernelQuotientEnergyDensity_integrable _) (hTi.re.const_mul _)
      intro q
      induction q using Quotient.inductionOn with
      | _ w => exact kernelCorrespondenceTest_energyDensity_le hHK hJK e g he f w
    _ = _ := by
      rw [integral_const_mul,hre]
      exact (mul_assoc _ _ _).symm

end

local notation "O" => ActualEisensteinCubic.O

variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)

def kernelCorrespondenceTestLinear : kernelSmoothTests→ₗ[ℂ]kernelSmoothTests where
  toFun := kernelCorrespondenceTest hHK hJK e g he
  map_add' f h := by
    apply Subtype.ext
    funext q
    induction q using Quotient.inductionOn with
    | _ w =>
      let : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
      change kernelCorrespondenceFunction hJK e g he (f+h).1
        (integralOrbitProjection globalKubotaKernel w)=
          kernelCorrespondenceFunction hJK e g he f.1 (integralOrbitProjection globalKubotaKernel w)+
          kernelCorrespondenceFunction hJK e g he h.1 (integralOrbitProjection globalKubotaKernel w)
      simp only [kernelCorrespondenceFunction_lift,Submodule.coe_add,Pi.add_apply,Finset.sum_add_distrib]
  map_smul' c f := by
    apply Subtype.ext
    funext q
    induction q using Quotient.inductionOn with
    | _ w =>
      let : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
      change kernelCorrespondenceFunction hJK e g he (c•f).1
        (integralOrbitProjection globalKubotaKernel w)=
          c • kernelCorrespondenceFunction hJK e g he f.1 (integralOrbitProjection globalKubotaKernel w)
      simp only [kernelCorrespondenceFunction_lift,Submodule.coe_smul,Pi.smul_apply,Finset.smul_sum]

lemma kernelCorrespondenceL2_norm_le (F : KernelQuotientL2) :
    ‖kernelCorrespondenceL2 hHK hJK e g he F‖≤
      Real.sqrt ((H.relIndex globalKubotaKernel:ℝ)*(J.relIndex globalKubotaKernel:ℝ))*‖F‖ := by
  let C := integralConjugatePullback e g he
    (hHK.trans globalKubotaKernel_le_levelThree) (hJK.trans globalKubotaKernel_le_levelThree)
  let P := integralCoverPullback hJK globalKubotaKernel_le_levelThree
  let Tr := integralCoverTrace hHK globalKubotaKernel_le_levelThree
  have hTr := integralCoverTrace_opNorm_le hHK globalKubotaKernel_le_levelThree
  have hP := integralCoverPullback_norm_le hJK globalKubotaKernel_le_levelThree F
  rw [←Real.sqrt_eq_rpow] at hTr hP
  change ‖Tr (C (P F))‖≤_
  calc
    _ ≤ ‖Tr‖*‖C (P F)‖ := Tr.le_opNorm _
    _ ≤ Real.sqrt (H.relIndex globalKubotaKernel:ℝ)*‖C (P F)‖ :=
      mul_le_mul_of_nonneg_right hTr (norm_nonneg _)
    _ = Real.sqrt (H.relIndex globalKubotaKernel:ℝ)*‖P F‖ := by rw [C.norm_map]
    _ ≤ Real.sqrt (H.relIndex globalKubotaKernel:ℝ)*
        (Real.sqrt (J.relIndex globalKubotaKernel:ℝ)*‖F‖) :=
      mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg _)]; ring

lemma kernelCorrespondenceTest_graph_norm (f : kernelSmoothTests) :
    ‖kernelEnergyGraphCore (kernelCorrespondenceTest hHK hJK e g he f)‖≤
      Real.sqrt ((H.relIndex globalKubotaKernel:ℝ)*(J.relIndex globalKubotaKernel:ℝ))*
        ‖kernelEnergyGraphCore f‖ := by
  have hm := kernelCorrespondenceL2_norm_le hHK hJK e g he (kernelSmoothTestsToL2 f)
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mpr hm
  rw [←kernelCorrespondenceTest_mass hHK hJK e g he,mul_pow,
    Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))] at hs
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [kernelEnergyGraphCore_norm_sq,mul_pow,
    Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),kernelEnergyGraphCore_norm_sq]
  have he := kernelCorrespondenceTest_energy_le hHK hJK e g he f
  nlinarith

def kernelCorrespondenceEnergy : KernelEnergyGraph→L[ℂ]KernelEnergyGraph :=
  (kernelEnergyGraphCore.comp (kernelCorrespondenceTestLinear hHK hJK e g he)).extendOfNorm
    kernelEnergyGraphCore

lemma kernelCorrespondenceEnergy_core (f : kernelSmoothTests) :
    kernelCorrespondenceEnergy hHK hJK e g he (kernelEnergyGraphCore f)=
      kernelEnergyGraphCore (kernelCorrespondenceTest hHK hJK e g he f) :=
  LinearMap.extendOfNorm_eq kernelEnergyGraphCore_dense
    ⟨_,kernelCorrespondenceTest_graph_norm hHK hJK e g he⟩ f

lemma kernelCorrespondenceEnergy_mass (u : KernelEnergyGraph) :
    kernelEnergyMass (kernelCorrespondenceEnergy hHK hJK e g he u)=
      kernelCorrespondenceL2 hHK hJK e g he (kernelEnergyMass u) := by
  apply congrFun (kernelEnergyGraphCore_dense.equalizer
    (kernelEnergyMass.continuous.comp (kernelCorrespondenceEnergy hHK hJK e g he).continuous)
    ((kernelCorrespondenceL2 hHK hJK e g he).continuous.comp kernelEnergyMass.continuous) ?_) u
  funext f
  change kernelEnergyMass (kernelCorrespondenceEnergy hHK hJK e g he (kernelEnergyGraphCore f))=
    kernelCorrespondenceL2 hHK hJK e g he (kernelEnergyMass (kernelEnergyGraphCore f))
  rw [kernelCorrespondenceEnergy_core,kernelEnergyMass_core,kernelEnergyMass_core,
    kernelCorrespondenceTest_mass]

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def ramifiedCuspShiftNumerator (b : Bool) : Eis :=
  if b then -2-omega else omega-1

lemma ramifiedCuspShift_congr (b : Bool) :
    (3:Eis)∣ramifiedCuspShiftNumerator b-onceCuspScale (ramifiedCuspScaleUnit b) := by
  refine ⟨-1,?_⟩
  cases b
  · simp [ramifiedCuspShiftNumerator,ramifiedCuspScaleUnit,onceCuspScale,
      Units.val_neg,ramifiedOmegaUnit_val,ramifiedTraceLambda]
    linear_combination 2*ramified_omega_relation
  · simp only [ramifiedCuspShiftNumerator,ramifiedCuspScaleUnit,ite_true,onceCuspScale,
      Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val,ramifiedTraceLambda]
    linear_combination -(2*omega-1)*ramified_omega_relation

lemma ramifiedCuspShift_support (b : Bool) (h : Eis) :
    (3:Eis)∣ramifiedCuspShiftNumerator b-h ↔
      (3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b) := by
  constructor
  · intro hh
    convert dvd_sub (ramifiedCuspShift_congr b) hh using 1 ; ring
  · intro hh
    convert dvd_sub (ramifiedCuspShift_congr b) hh using 1 ; ring

lemma ramifiedSource_affine_shift (b : Bool) (x : Eis) (z : ℂ)
    (v : ℝ) (hv : 0<v) :
    ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint (z+3*eisEmbedding x) v hv)=
      affinePeriodChar (3:Eis) (by norm_num) (ramifiedCuspShiftNumerator b)
        (Ideal.Quotient.mk (Ideal.span {(3:Eis)}) x)*
      ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint z v hv) := by
  rw [affinePeriodChar_mk]
  cases b
  · simp only [ramifiedCuspRoot,ramifiedCuspShiftNumerator]
    simp only [Bool.false_eq_true,↓reduceIte,ramifiedOmegaUnit_val]
    rw [ramifiedSourceFunction_upper_shift10]
    congr 2
    simp only [ramifiedShift10,map_mul,map_ofNat]
    ring
  · simp only [ramifiedCuspRoot,ite_true,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val,
      ramifiedCuspShiftNumerator]
    rw [ramifiedSourceFunction_upper_shift19]
    congr 2
    simp only [ramifiedShift19,map_mul,map_ofNat]
    ring

lemma ramifiedSource_weighted_shift (b : Bool) (h x : Eis) (z : ℂ)
    (v : ℝ) (hv : 0<v) :
    ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint (z+3*eisEmbedding x) v hv)*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding x))=
    affinePeriodChar (3:Eis) (by norm_num) (ramifiedCuspShiftNumerator b-h)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)}) x)*
      (ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint z v hv)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z)) := by
  rw [ramifiedSource_affine_shift]
  have hphase : affinePeriodChar (3:Eis) (by norm_num) (ramifiedCuspShiftNumerator b)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)}) x)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding x))=
    affinePeriodChar (3:Eis) (by norm_num) (ramifiedCuspShiftNumerator b-h)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)}) x)*ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
    rw [affinePeriodChar_mk,affinePeriodChar_mk,←AddChar.map_add_eq_mul,←AddChar.map_add_eq_mul]
    congr 1
    simp only [ninthCuspFrequency,cuspFrequency,map_mul,map_sub,map_ofNat]
    ring
  calc
    _ = ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint z v hv)*
        (affinePeriodChar (3:Eis) (by norm_num) (ramifiedCuspShiftNumerator b)
          (Ideal.Quotient.mk (Ideal.span {(3:Eis)}) x)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding x))) := by ring
    _ = _ := by rw [hphase];ring

theorem ramifiedSource_active_weighted_periodic (b : Bool) (h : Eis)
    (hh : (3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b)) (v : ℝ) (hv : 0<v) :
    ∀x : Eis,∀z : ℂ,
      ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint (z+3*eisEmbedding x) v hv)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding x))=
      ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint z v hv)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
  intro x z
  rw [ramifiedSource_weighted_shift]
  have hc := (affinePeriodChar_eq_one (3:Eis) (by norm_num) (ramifiedCuspShiftNumerator b-h)).mpr
    ((ramifiedCuspShift_support b h).mpr hh)
  rw [hc]
  simp

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def ramifiedScaledMode (b : Bool) (h : Eis) (v : ℝ) (hv : 0<v) (z : ℂ) : ℂ :=
  ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint (3*z) v hv)*
    ShortDraftTrace.breveE (-cuspFrequency h*z)

lemma ramifiedScaledMode_shift (b : Bool) (h x : Eis) (v : ℝ) (hv : 0<v) (z : ℂ) :
    ramifiedScaledMode b h v hv (z+eisEmbedding x)=
      affinePeriodChar (3:Eis) (by norm_num) (ramifiedCuspShiftNumerator b-h)
        (Ideal.Quotient.mk (Ideal.span {(3:Eis)}) x)*ramifiedScaledMode b h v hv z := by
  unfold ramifiedScaledMode
  rw [show 3*(z+eisEmbedding x)=3*z+3*eisEmbedding x by ring]
  have h1 : -cuspFrequency h*(z+eisEmbedding x)=
      -ninthCuspFrequency h*(3*z+3*eisEmbedding x) := by rw [ninthCuspFrequency];ring
  have h2 : -cuspFrequency h*z= -ninthCuspFrequency h*(3*z) := by rw [ninthCuspFrequency];ring
  rw [h1,h2]
  exact ramifiedSource_weighted_shift b h x (3*z) v hv

lemma ramifiedScaledMode_periodic (b : Bool) (h : Eis) (v : ℝ) (hv : 0<v) :
    ∀x : Eis,∀z : ℂ,ramifiedScaledMode b h v hv (z+3*eisEmbedding x)=
      ramifiedScaledMode b h v hv z := by
  intro x z
  have hx : Ideal.Quotient.mk (Ideal.span {(3:Eis)}) (3*x)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_mul_right 3 x))
  simpa only [map_mul,map_ofNat,hx,AddChar.map_zero_eq_one,one_mul] using
    ramifiedScaledMode_shift b h (3*x) v hv z

theorem ramifiedSource_scaled_fourier_off_support (b : Bool) (h : Eis)
    (hh : ¬(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b)) (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,ramifiedSourceFunction (ramifiedCuspRoot b:Eis)
      (upperPoint (3*z) v hv)*ShortDraftTrace.breveE (-cuspFrequency h*z))=0 := by
  let χ := affinePeriodChar (3:Eis) (by norm_num) (ramifiedCuspShiftNumerator b-h)
  have hχ : χ≠1 := by
    intro he
    exact hh ((ramifiedCuspShift_support b h).mp
      ((affinePeriodChar_eq_one (3:Eis) (by norm_num) _).mp he))
  have hex : ∃x : Eis⧸Ideal.span {(3:Eis)},χ x≠1 := by
    by_contra he
    push Not at he
    apply hχ
    ext x
    simpa only [AddChar.one_apply] using he x
  obtain ⟨x,hx⟩ := hex
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective x
  change (∫z in periodDomain,ramifiedScaledMode b h v hv z)=0
  apply periodic_integral_zero_of_eigen_translation _ (ramifiedScaledMode_periodic b h v hv)
    (eisEmbedding y) (χ (Ideal.Quotient.mk (Ideal.span {(3:Eis)}) y)) hx
  intro z
  simpa only [add_comm] using ramifiedScaledMode_shift b h y v hv z

lemma ramifiedSource_height_continuous (b : Bool) (v : ℝ) (hv : 0<v) :
    Continuous (fun z : ℂ=>ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint z v hv)) := by
  let c : ℂ→UpperCoordinates := fun z=>⟨(z,v),hv⟩
  have hc : Continuous c := by
    apply Continuous.subtype_mk
    exact continuous_id.prodMk continuous_const
  have ht := continuous_upperCoordinates.comp hc
  have ht' : Continuous (fun z : ℂ=>upperPoint z v hv) := by
    simpa only [Function.comp_def,c] using ht
  exact (ramifiedSourceFunction_continuous _).comp ht'

theorem ramifiedSource_scaled_fourier_active (b : Bool) (h : Eis)
    (hh : (3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b)) (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,ramifiedSourceFunction (ramifiedCuspRoot b:Eis)
      (upperPoint (3*z) v hv)*ShortDraftTrace.breveE (-cuspFrequency h*z))=
    ∫z in periodDomain,ramifiedSourceFunction (ramifiedCuspRoot b:Eis)
      (upperPoint z v hv)*ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
  have he (z : ℂ) : -ninthCuspFrequency h*(3*z)= -cuspFrequency h*z := by
    rw [ninthCuspFrequency]
    ring
  have hphase : Continuous (fun z : ℂ=>ShortDraftTrace.breveE (-ninthCuspFrequency h*z)) := by
    change Continuous (fun z : ℂ=>Complex.exp (2*Real.pi*Complex.I*
      ((-ninthCuspFrequency h*z)+starRingEnd ℂ (-ninthCuspFrequency h*z))))
    fun_prop
  have hi := period_integral_eisenstein_mul
    (fun z=>ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint z v hv)*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z))
    ((ramifiedSource_height_continuous b v hv).mul hphase).measurable
    (ramifiedSource_active_weighted_periodic b h hh v hv) (3:Eis) (by norm_num)
  simpa only [map_ofNat,he] using hi

end CubicEisenstein

end

end OAI
