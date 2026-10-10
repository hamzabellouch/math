import OAI.NumberTheory.DirichletL.Eisenstein.FullFrequencyExpansion

namespace OAI

noncomputable section

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

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

open CompletedGauss ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceCuspCoefficients_full_support (j:Fin 3) (h:Eis) (hh:h≠0)
    (hc:(sourceCuspCoefficients j).value h≠0) :
    ∃p:ThetaFullIndex,thetaFullFrequency p=h := by
  have hs : ∃u:Eisˣ,∃m:ℕ,∃I J:Ideal Eis,Squarefree I ∧
      primaryGenerator I≠0 ∧ primaryGenerator J≠0 ∧
      h=(u:Eis)*ActualEisensteinCubic.lambda^m*primaryGenerator I*(primaryGenerator J)^3 := by
    fin_cases j
    · exact sourceResidualFourierCoefficient_full_squarefree_cube_support h hh hc
    · exact ramifiedBesselValue_squarefree_cube_support false h hh hc
    · exact ramifiedBesselValue_squarefree_cube_support true h hh hc
  obtain ⟨u,m,I,J,hI,hIg,hJg,he⟩:=hs
  exact ⟨(u,m,(⟨I,hI,hIg⟩,⟨J,hJg⟩)),he.symm⟩

lemma sourceCuspRadialCoefficient_full_support (j:Fin 3) (z:ℂ) (h:Eis)
    (hh:h≠0) (hc:sourceCuspRadialCoefficient j z h≠0) :
    ∃p:ThetaFullIndex,thetaFullFrequency p=h := by
  apply sourceCuspCoefficients_full_support j h hh
  intro hz
  apply hc
  simp only [sourceCuspRadialCoefficient,sourceCuspRadialBaseCoefficient,hz,
    star_zero,mul_zero,zero_div,zero_mul]

theorem sourceCuspRadialCoefficient_tsum_full_index (j:Fin 3) (z:ℂ) (w:Eis→ℂ) :
    (∑'h:Eis,w h*sourceCuspRadialCoefficient j z h)=
      ∑'p:ThetaFullIndex,w (thetaFullFrequency p)*
        sourceCuspRadialCoefficient j z (thetaFullFrequency p) := by
  have hs:Function.support (fun h:Eis=>w h*sourceCuspRadialCoefficient j z h)⊆
      {h:Eis|h≠0}:=by
    intro h hh hz
    subst h
    exact hh (by
      change w 0*sourceCuspRadialCoefficient j z 0=0
      rw [sourceCuspRadialCoefficient_zero,mul_zero])
  calc
    _=∑'h:{h:Eis//h≠0},w h.val*sourceCuspRadialCoefficient j z h.val:=
      (tsum_subtype_eq_of_support_subset hs).symm
    _=_:=thetaFullFrequency_tsum (sourceCuspRadialCoefficient j z) w
      (sourceCuspRadialCoefficient_full_support j z)

lemma SourceCuspDatum.smoothedKernel_full_index (d:SourceCuspDatum) (W:ℝ→ℂ) (X:ℝ) :
    d.smoothedKernel W X=
      (d.multiplier*(d.heightScale:ℂ)*(sourceCuspScale d.index:ℂ)^2)*
        ∑'p:ThetaFullIndex,sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)*
          CubicReflectionKernel.paperKernel (Vstar W)
            (X*sourceCuspRadialLength (thetaFullFrequency p)/
              (27*(sourceCuspScale d.index)^2*d.heightScale^2)) := by
  rw [d.smoothedKernel_eq]
  congr 1
  have he:=sourceCuspRadialCoefficient_tsum_full_index d.index d.dualPoint
    (fun h=>CubicReflectionKernel.paperKernel (Vstar W)
      (X*sourceCuspRadialLength h/(27*(sourceCuspScale d.index)^2*d.heightScale^2)))
  simpa only [mul_comm] using he

lemma SourceCuspDatum.smoothedKernel_full_index_norm_summable
    (d:SourceCuspDatum) (W:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hWs:Function.support W⊆Set.Icc v0 v1) (hW:ContDiff ℝ ∞ W)
    (X:ℝ) (hX:0<X) :
    Summable (fun p:ThetaFullIndex=>
      ‖sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)*
        CubicReflectionKernel.paperKernel (Vstar W)
          (X*sourceCuspRadialLength (thetaFullFrequency p)/
            (27*(sourceCuspScale d.index)^2*d.heightScale^2))‖) := by
  have hs:=paperKernel_weighted_norm_summable sourceCuspRadialLength sourceCuspRadialLength_pos
    (sourceCuspRadialCoefficient d.index d.dualPoint)
    (sourceCuspRadialCoefficient_weighted_summable _ _)
    (Vstar W) v0 v1 hv0 (Vstar_support W v0 v1 hWs) (Vstar_contDiff W v0 v1 hv0 hWs hW)
    (X/(27*(sourceCuspScale d.index)^2*d.heightScale^2))
    (by have := sourceCuspScale_pos d.index; have := d.heightScale_pos; positivity)
  have hp:=hs.comp_injective thetaFullFrequency_injective
  apply hp.congr
  intro p
  exact congrArg (fun y:ℝ=>‖sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)*
    CubicReflectionKernel.paperKernel (Vstar W) y‖)
    (by ring :
      X/(27*(sourceCuspScale d.index)^2*d.heightScale^2)*sourceCuspRadialLength (thetaFullFrequency p)=
        X*sourceCuspRadialLength (thetaFullFrequency p)/(27*(sourceCuspScale d.index)^2*d.heightScale^2))

theorem completedT_finite_smoothed_full_index
    (Ψ:Eis→*ℂ) (hΨ:∀x,‖Ψ x‖≤1)
    (Q:Ideal Eis) (hperiod:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (d:(Eis⧸Ideal.span {c})→SourceCuspDatum)
    (hd:∀h,(d h).point=thetaFourierTranslation c h)
    (W:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hWs:Function.support W⊆Set.Icc v0 v1) (hW:ContDiff ℝ ∞ W)
    (X:ℝ) (hX:0<X) :
    completedT Ψ W X=thetaDerivativeScalar⁻¹*
      ∑h:Eis⧸Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h*
          ((d h).multiplier*((d h).heightScale:ℂ)*(sourceCuspScale (d h).index:ℂ)^2)*
        ∑'p:ThetaFullIndex,sourceCuspRadialCoefficient (d h).index (d h).dualPoint (thetaFullFrequency p)*
          CubicReflectionKernel.paperKernel (Vstar W)
            (X*sourceCuspRadialLength (thetaFullFrequency p)/
              (27*(sourceCuspScale (d h).index)^2*(d h).heightScale^2)) := by
  rw [completedT_finite_smoothed_reflection Ψ hΨ Q hperiod c hc hcQ d hd W v0 v1 hv0 hWs hW X hX]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  rw [(d h).smoothedKernel_full_index]
  ring

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def fixedCuspCoefficientBound : ℝ :=
  Classical.choose three_cusp_coefficients_squarefree_cube_bound

lemma fixedCuspCoefficientBound_pos : 0<fixedCuspCoefficientBound :=
  (Classical.choose_spec three_cusp_coefficients_squarefree_cube_bound).1

def fixedCuspArrayIndex (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : Eis :=
  (u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3

def fixedCuspArrayEligible (I J:Ideal Eis) : Prop :=
  Squarefree I ∧ primaryGenerator I≠0 ∧ primaryGenerator J≠0

def fixedCuspArrayWeight (m:ℕ) (J:Ideal Eis) : ℝ :=
  (3:ℝ)^((m:ℝ)/6)*Real.sqrt (Ideal.absNorm J:ℝ)

lemma fixedCuspArrayWeight_nonneg (m:ℕ) (J:Ideal Eis) :
    0≤fixedCuspArrayWeight m J := by
  unfold fixedCuspArrayWeight
  positivity

lemma fixedCuspArrayWeight_pos (m:ℕ) (J:Ideal Eis) (hJ:primaryGenerator J≠0) :
    0<fixedCuspArrayWeight m J := by
  rw [fixedCuspArrayWeight,←primaryGenerator_norm J hJ]
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (norm_pos_iff.mpr (eisEmbedding_ne_zero hJ))

lemma sourceCuspCoefficients_squarefree_cube_bound (j:Fin 3) (u:Eisˣ) (m:ℕ)
    (I J:Ideal Eis) (helig:fixedCuspArrayEligible I J) :
    ‖(sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J)‖≤
      fixedCuspCoefficientBound*fixedCuspArrayWeight m J := by
  rcases helig with ⟨hsq,hI,hJ⟩
  have hb:=(Classical.choose_spec three_cusp_coefficients_squarefree_cube_bound).2
    I J hI hJ hsq u m
  rw [primaryGenerator_norm J hJ] at hb
  fin_cases j
  · simpa [sourceCuspCoefficients,sourceBesselCoefficients,ramifiedBesselCoefficients,fixedCuspCoefficientBound,fixedCuspArrayWeight,fixedCuspArrayIndex,mul_assoc] using hb.1
  · simpa [sourceCuspCoefficients,sourceBesselCoefficients,ramifiedBesselCoefficients,fixedCuspCoefficientBound,fixedCuspArrayWeight,fixedCuspArrayIndex,mul_assoc] using hb.2 false
  · simpa [sourceCuspCoefficients,sourceBesselCoefficients,ramifiedBesselCoefficients,fixedCuspCoefficientBound,fixedCuspArrayWeight,fixedCuspArrayIndex,mul_assoc] using hb.2 true

def fixedCuspArray (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : ℂ :=
  if fixedCuspArrayEligible I J then
    (sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J) /
      ((fixedCuspCoefficientBound*fixedCuspArrayWeight m J:ℝ):ℂ)
  else 0

lemma fixedCuspArray_zero_of_ineligible (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (h:¬fixedCuspArrayEligible I J) : fixedCuspArray j u m I J=0 := by
  simp only [fixedCuspArray,ite_eq_right h]

lemma fixedCuspArray_norm_le_one (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    ‖fixedCuspArray j u m I J‖≤1 := by
  by_cases h:fixedCuspArrayEligible I J
  · have hpos:=mul_pos fixedCuspCoefficientBound_pos (fixedCuspArrayWeight_pos m J h.2.2)
    rw [fixedCuspArray,ite_eq_left h,norm_div,Complex.norm_real,Real.norm_of_nonneg hpos.le]
    exact (div_le_one hpos).mpr (sourceCuspCoefficients_squarefree_cube_bound j u m I J h)
  · simp only [fixedCuspArray,ite_eq_right h,norm_zero,zero_le_one]

lemma fixedCuspArray_reconstruct (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (h:fixedCuspArrayEligible I J) :
    (sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J)=
      ((fixedCuspCoefficientBound*fixedCuspArrayWeight m J:ℝ):ℂ)*fixedCuspArray j u m I J := by
  have hpos:=mul_pos fixedCuspCoefficientBound_pos (fixedCuspArrayWeight_pos m J h.2.2)
  rw [fixedCuspArray,ite_eq_left h,mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hpos.ne')]

def fixedConjugateCuspArray (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : ℂ :=
  star (fixedCuspArray j u m I J)

lemma fixedConjugateCuspArray_norm_le_one (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    ‖fixedConjugateCuspArray j u m I J‖≤1 := by
  simpa only [fixedConjugateCuspArray,norm_star] using fixedCuspArray_norm_le_one j u m I J

lemma fixedConjugateCuspArray_reconstruct (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (h:fixedCuspArrayEligible I J) :
    star ((sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J))=
      ((fixedCuspCoefficientBound*fixedCuspArrayWeight m J:ℝ):ℂ)*fixedConjugateCuspArray j u m I J := by
  rw [fixedCuspArray_reconstruct j u m I J h,star_mul]
  simp only [fixedConjugateCuspArray,Complex.star_def,Complex.conj_ofReal]
  ring

lemma fixedConjugateCuspArray_reconstruct_explicit (j:Fin 3) (u:Eisˣ) (m:ℕ)
    (I J:Ideal Eis) (hsq:Squarefree I) (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) :
    star ((sourceCuspCoefficients j).value
      ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3))=
      ((fixedCuspCoefficientBound*(3:ℝ)^((m:ℝ)/6)*Real.sqrt (Ideal.absNorm J:ℝ):ℝ):ℂ)*
        fixedConjugateCuspArray j u m I J := by
  simpa only [fixedCuspArrayIndex,fixedCuspArrayWeight,mul_assoc] using
    fixedConjugateCuspArray_reconstruct j u m I J ⟨hsq,hI,hJ⟩

end CubicEisenstein

section
open scoped BigOperators Classical
open Finset AddChar MulChar EisensteinEmbedding

namespace IdealGaussCRT
open CubicEisenstein

theorem finiteAdditiveFourierCoeff_crt {ι T : Type*} [Fintype ι]
    (R : ι→Type*) [CommRing T] [∀i,CommRing (R i)]
    [Fintype T] [∀i,Fintype (R i)] (e : T≃+*∀i,R i)
    (ψ : AddChar T ℂ) (φ : ∀i,R i→ℂ) (h : T) :
    finiteAdditiveFourierCoeff ψ (fun x=>∏i,φ i (e x i)) h=
      ∏i,finiteAdditiveFourierCoeff (coordinateAddChar R e ψ i) (φ i) (e h i) := by
  have hsum : (∑x:T,(∏i,φ i (e x i))*ψ (-h*x))=
      ∏i,∑x:R i,φ i x*coordinateAddChar R e ψ i (-(e h i)*x) := by
    calc
      _ = ∑x:T,∏i,φ i (e x i)*coordinateAddChar R e ψ i (-(e h i)*e x i) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [addChar_finite_crt_factor R e ψ (-h*x)]
        simp only [map_mul,map_neg,Pi.mul_apply,Pi.neg_apply,Finset.prod_mul_distrib]
      _ = ∑x:(∀i,R i),∏i,φ i (x i)*coordinateAddChar R e ψ i (-(e h i)*x i) :=
        Equiv.sum_comp e.toEquiv (fun x:∀i,R i=>∏i,φ i (x i)*coordinateAddChar R e ψ i (-(e h i)*x i))
      _ = _ := (Fintype.prod_sum (fun i (x:R i)=>φ i x*coordinateAddChar R e ψ i (-(e h i)*x))).symm
  have hcard : (Fintype.card T:ℂ)=∏i,(Fintype.card (R i):ℂ) := by
    rw [Fintype.card_congr e.toEquiv,Fintype.card_pi,Nat.cast_prod]
  simp only [finiteAdditiveFourierCoeff,hsum,hcard,Finset.prod_div_distrib]

theorem finite_fourier_weighted_crt {ι T : Type*} [Fintype ι]
    (R : ι→Type*) [CommRing T] [∀i,CommRing (R i)]
    [Fintype T] [∀i,Fintype (R i)] (e : T≃+*∀i,R i)
    (ψ : AddChar T ℂ) (φ κ : ∀i,R i→ℂ) :
    (∑h:T,finiteAdditiveFourierCoeff ψ (fun x=>∏i,φ i (e x i)) h *
      ∏i,κ i (e h i))=
      ∏i,∑h:R i,finiteAdditiveFourierCoeff (coordinateAddChar R e ψ i) (φ i) h*κ i h := by
  simp only [finiteAdditiveFourierCoeff_crt,←Finset.prod_mul_distrib]
  calc
    _ = ∑h:∀i,R i,∏i,finiteAdditiveFourierCoeff (coordinateAddChar R e ψ i) (φ i) (h i)*κ i (h i) :=
      Equiv.sum_comp e.toEquiv
        (fun h:∀i,R i=>∏i,finiteAdditiveFourierCoeff (coordinateAddChar R e ψ i) (φ i) (h i)*κ i (h i))
    _ = _ := (Fintype.prod_sum (fun i (h:R i)=>
      finiteAdditiveFourierCoeff (coordinateAddChar R e ψ i) (φ i) h*κ i h)).symm

end IdealGaussCRT

namespace LocalReflectionBrackets

section
open CubicEisenstein
variable {F : Type*} [Field F] [Fintype F]

def frequencyMultiplier (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (σ ε : Fˣ) (x h : F) : ℂ :=
  if h=0 then 1 else (((χ⁻¹)^2) ((σ:F)*h))*ψ (((ε:F)*x)*h⁻¹)

def frequencyRow (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (j : ℕ) (σ ε : Fˣ) (x h : F) : ℂ :=
  finiteAdditiveFourierCoeff ψ (fun t=>(χ^j) t) h*frequencyMultiplier χ ψ σ ε x h

lemma frequencyRow_zero (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (j : ℕ) (σ ε : Fˣ) (x : F) :
    frequencyRow χ ψ j σ ε x 0=zeroFourierCoefficient χ j := by
  simp only [frequencyRow,frequencyMultiplier,finiteAdditiveFourierCoeff,
    zeroFourierCoefficient,ite_true,neg_zero,zero_mul,AddChar.map_zero_eq_one,
    mul_one,div_eq_mul_inv]
  ring

lemma frequencyRow_units (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (j : ℕ) (σ ε : Fˣ) (x : F) :
    (∑h:Fˣ,frequencyRow χ ψ j σ ε x h)=activeRow χ ψ j σ ε x := by
  unfold frequencyRow finiteAdditiveFourierCoeff frequencyMultiplier activeRow
  simp only [Units.ne_zero,ite_false,Units.val_inv_eq_inv_val,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  ring_nf

open ActualEisensteinCubic CompletedGauss
noncomputable local instance quotientFieldFrequency (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] :
    Field (ActualEisensteinCubic.O⧸P) := Ideal.Quotient.field P
noncomputable local instance quotientFintypeFrequency (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] :
    Fintype (ActualEisensteinCubic.O⧸P) := Fintype.ofFinite _

theorem canonical_frequencyRow_zero (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hgood : lambda∉P) (hchar : ringChar (ActualEisensteinCubic.O⧸P)≠2) (ψ : AddChar (ActualEisensteinCubic.O⧸P) ℂ)
    (j : ℕ) (hj : j<6) (σ ε : (ActualEisensteinCubic.O⧸P)ˣ) (x : ActualEisensteinCubic.O⧸P) :
    frequencyRow (actualSextic P hgood) ψ j σ ε x 0=
      if j=0 then 1-(Fintype.card (ActualEisensteinCubic.O⧸P):ℂ)⁻¹ else 0 := by
  rw [frequencyRow_zero]
  simpa only [actualSextic] using canonical_zeroFourierCoefficient P hgood hchar j hj

theorem canonical_frequencyRow_units (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hgood : lambda∉P) (hchar : ringChar (ActualEisensteinCubic.O⧸P)≠2) (ψ : AddChar (ActualEisensteinCubic.O⧸P) ℂ)
    (hψ : ψ.IsPrimitive) (j : ℕ) (hj : j<6) (σ ε : (ActualEisensteinCubic.O⧸P)ˣ) (x : ActualEisensteinCubic.O⧸P) :
    (∑h:(ActualEisensteinCubic.O⧸P)ˣ,frequencyRow (actualSextic P hgood) ψ j σ ε x h)=
      (((actualSextic P hgood)⁻¹)^2) σ *
        phase (actualSextic P hgood) ψ j ε*bracket (actualSextic P hgood) j x := by
  rw [frequencyRow_units]
  simpa only [actualSextic] using canonical_A5_normalized P hgood hchar ψ hψ j hj σ ε x

end

open ActualEisensteinCubic CubicEisenstein IdealGaussCRT CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance quotientFintypeCrt (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

theorem canonical_finite_reflection_crt {ι T : Type*} [Fintype ι]
    [CommRing T] [Fintype T]
    (P : ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (e : T≃+*∀i,Eis⧸P i) (ψ : AddChar T ℂ) (hψ : ψ.IsPrimitive)
    (hg : ∀i,lambda∉P i) (hchar : ∀i,ringChar (Eis⧸P i)≠2)
    (j : ι→ℕ) (hj : ∀i,j i<6) (σ ε : ∀i,(Eis⧸P i)ˣ) (x : ∀i,Eis⧸P i) :
    let χ := fun i=>actualSextic (P i) (hg i)
    let ψi := coordinateAddChar (fun i=>Eis⧸P i) e ψ
    (∑h:T,finiteAdditiveFourierCoeff ψ (fun t=>∏i,(χ i^j i) (e t i)) h*
      ∏i,frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i) (e h i))=
      ∑A∈(Finset.univ:Finset ι).powerset,
        (∏i∈A,(((χ i)⁻¹)^2) (σ i)*phase (χ i) (ψi i) (j i) (ε i)*bracket (χ i) (j i) (x i))*
        (∏i∈(Finset.univ:Finset ι)\A,if j i=0 then 1-(Fintype.card (Eis⧸P i):ℂ)⁻¹ else 0) := by
  let (i : ι) : Field (Eis⧸P i) := Ideal.Quotient.field (P i)
  let χ := fun i=>actualSextic (P i) (hg i)
  let ψi := coordinateAddChar (fun i=>Eis⧸P i) e ψ
  let f := fun i=>frequencyRow (χ i) (ψi i) (j i) (σ i) (ε i) (x i)
  have hsum : (∑h:T,finiteAdditiveFourierCoeff ψ (fun t=>∏i,(χ i^j i) (e t i)) h*
      ∏i,frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i) (e h i))=
      ∑h:∀i,Eis⧸P i,∏i,f i (h i) := by
    simp only [finiteAdditiveFourierCoeff_crt,←Finset.prod_mul_distrib]
    exact Equiv.sum_comp e.toEquiv (fun h:∀i,Eis⧸P i=>∏i,f i (h i))
  have hactive (i : ι) : (∑h:(Eis⧸P i)ˣ,f i h)=
      (((χ i)⁻¹)^2) (σ i)*phase (χ i) (ψi i) (j i) (ε i)*bracket (χ i) (j i) (x i) := by
    exact canonical_frequencyRow_units (P i) (hg i) (hchar i) (ψi i)
      (coordinateAddChar_isPrimitive (fun i=>Eis⧸P i) e ψ hψ i) (j i) (hj i) (σ i) (ε i) (x i)
  have hzero (i : ι) : f i 0=if j i=0 then 1-(Fintype.card (Eis⧸P i):ℂ)⁻¹ else 0 := by
    exact canonical_frequencyRow_zero (P i) (hg i) (hchar i) (ψi i) (j i) (hj i) (σ i) (ε i) (x i)
  change (∑h:T,finiteAdditiveFourierCoeff ψ (fun t=>∏i,(χ i^j i) (e t i)) h*
      ∏i,frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i) (e h i))=_
  rw [hsum,FixedRayActiveSet.product_sum_by_active_set (fun i=>Eis⧸P i) f]
  simp only [hactive,hzero]
  rfl

theorem canonical_principal_reflection_crt {ι : Type*} [Fintype ι]
    (P : ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀i,lambda∉P i) (hchar : ∀i,ringChar (Eis⧸P i)≠2)
    (j : ι→ℕ) (hj : ∀i,j i<6) (σ ε : ∀i,(Eis⧸P i)ˣ) (x : ∀i,Eis⧸P i)
    (c : Eis) (hc : c≠0) (hcP : Ideal.span {c}=∏i,P i)
    [Fintype (Eis⧸Ideal.span {c})] :
    let e := (Ideal.quotEquivOfEq hcP).trans (quotientProdEquivPi P hcop)
    let ψ := quotientTrace c hc
    let χ := fun i=>actualSextic (P i) (hg i)
    let ψi := coordinateAddChar (fun i=>Eis⧸P i) e ψ
    (∑h:Eis⧸Ideal.span {c},finiteAdditiveFourierCoeff ψ (principalSexticRow P hcop hg j c hcP) h*
      ∏i,frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i) (e h i))=
      ∑A∈(Finset.univ:Finset ι).powerset,
        (∏i∈A,(((χ i)⁻¹)^2) (σ i)*phase (χ i) (ψi i) (j i) (ε i)*bracket (χ i) (j i) (x i))*
        (∏i∈(Finset.univ:Finset ι)\A,if j i=0 then 1-(Fintype.card (Eis⧸P i):ℂ)⁻¹ else 0) := by
  let e := (Ideal.quotEquivOfEq hcP).trans (quotientProdEquivPi P hcop)
  have hψ : (quotientTrace c hc).IsPrimitive :=
    GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc
  have hrow : principalSexticRow P hcop hg j c hcP=
      fun t=>∏i,(actualSextic (P i) (hg i)^j i) (e t i) := by
    funext t
    rfl
  dsimp only
  rw [hrow]
  exact canonical_finite_reflection_crt P e (quotientTrace c hc) hψ hg hchar j hj σ ε x

end LocalReflectionBrackets
end

namespace CubicEisenstein
open scoped Classical MatrixGroups Matrix

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma upper_right_removed_bottom (M T:SL(2,Eis)) (hT:T 1 0=0) :
    (M*T⁻¹) 1 0=M 1 0*T 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,hT]

lemma upper_right_removed_top (M T:SL(2,Eis)) (hT:T 1 0=0) :
    (M*T⁻¹) 0 0=M 0 0*T 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,hT]

lemma upper_right_removed_last (M T:SL(2,Eis)) :
    (M*T⁻¹) 1 1= -M 1 0*T 0 1+M 1 1*T 0 0 := by
  simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two]

lemma upper_diagonal_product (T:SL(2,Eis)) (hT:T 1 0=0) : T 0 0*T 1 1=1 := by
  have hd:=T.property
  simpa only [Matrix.det_fin_two,hT,mul_zero,sub_zero] using hd

structure FixedCuspShape (H:SL(2,Eis)) where
  gamma : levelTwo
  index : Fin 3
  upper : SL(2,Eis)
  lower_zero : upper 1 0=0
  upper_unit : IsUnit (upper 0 0)
  lower_unit : IsUnit (upper 1 1)
  factorization : H=(gamma:SL(2,Eis))*cuspRepresentative index*upper

lemma exists_fixedCuspShape (H:SL(2,Eis)) : Nonempty (FixedCuspShape H) := by
  obtain ⟨G,j,T,hT,hT0,hT1,he⟩:=three_cusp_decomposition H
  exact ⟨⟨G,j,T,hT,hT0,hT1,he⟩⟩

namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H) (g:levelTwo)

lemma removed_eq : (g:SL(2,Eis))*H*s.upper⁻¹=
    ((g*s.gamma:levelTwo):SL(2,Eis))*cuspRepresentative s.index := by
  calc
    _ = (g:SL(2,Eis))*((s.gamma:SL(2,Eis))*cuspRepresentative s.index*s.upper)*s.upper⁻¹ :=
      congrArg (fun K:SL(2,Eis)=>(g:SL(2,Eis))*K*s.upper⁻¹) s.factorization
    _ = _ := by simp only [Subgroup.coe_mul]; group

def datum (h:((g:SL(2,Eis))*H) 1 0≠0) : SourceCuspDatum where
  gamma := g*s.gamma
  index := s.index
  lower_ne_zero := by
    rw [←map_mul,←s.removed_eq g,integralComplexMatrix_apply,
      upper_right_removed_bottom _ _ s.lower_zero,map_mul]
    exact mul_ne_zero (eisEmbedding_ne_zero h) (eisEmbedding_ne_zero s.lower_unit.ne_zero)

lemma datum_matrix (h:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g h).matrix=integralComplexMatrix ((g:SL(2,Eis))*H*s.upper⁻¹) := by
  rw [s.removed_eq g,map_mul]
  rfl

lemma datum_point (h:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g h).point=
      eisEmbedding (((g:SL(2,Eis))*H) 0 0)/eisEmbedding (((g:SL(2,Eis))*H) 1 0) := by
  rw [SourceCuspDatum.point,s.datum_matrix]
  rw [integralComplexMatrix_apply,integralComplexMatrix_apply,
    upper_right_removed_top _ _ s.lower_zero,upper_right_removed_bottom _ _ s.lower_zero]
  simp only [map_mul]
  exact mul_div_mul_right _ _ (eisEmbedding_ne_zero s.lower_unit.ne_zero)

lemma datum_heightScale (h:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g h).heightScale=‖eisEmbedding (((g:SL(2,Eis))*H) 1 0)‖^2 := by
  rw [SourceCuspDatum.heightScale,s.datum_matrix,integralComplexMatrix_apply,
    upper_right_removed_bottom _ _ s.lower_zero,map_mul,norm_mul]
  have hn:‖eisEmbedding (s.upper 1 1)‖=1 := by
    rcases s.lower_unit with ⟨u,hu⟩
    rw [←hu]
    exact GaussGeneratorTransport.norm_eisEmbedding_unit u
  rw [hn,mul_one]

lemma datum_dualPoint (h:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g h).dualPoint=
      eisEmbedding (s.upper 0 0*s.upper 0 1)-
        eisEmbedding (s.upper 0 0)^2*
          (eisEmbedding (((g:SL(2,Eis))*H) 1 1)/eisEmbedding (((g:SL(2,Eis))*H) 1 0)) := by
  rw [SourceCuspDatum.dualPoint,s.datum_matrix]
  rw [integralComplexMatrix_apply,integralComplexMatrix_apply,upper_right_removed_last,
    upper_right_removed_bottom _ _ s.lower_zero]
  simp only [map_add,map_neg,map_mul]
  have hd:eisEmbedding (s.upper 0 0)*eisEmbedding (s.upper 1 1)=1 := by
    rw [←map_mul,upper_diagonal_product _ s.lower_zero,map_one]
  have hc:=eisEmbedding_ne_zero h
  have ht:=eisEmbedding_ne_zero s.lower_unit.ne_zero
  field_simp [hc,ht]
  linear_combination (eisEmbedding (s.upper 0 0)*eisEmbedding (((g:SL(2,Eis))*H) 1 1)-
    eisEmbedding (((g:SL(2,Eis))*H) 1 0)*eisEmbedding (s.upper 0 1))*hd

lemma datum_multiplier (h:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g h).multiplier=
      -star (levelTwoComplexCharacter g)*star (levelTwoComplexCharacter s.gamma)*
        eisEmbedding (s.upper 0 0)^2/eisEmbedding (((g:SL(2,Eis))*H) 1 0)^2 := by
  rw [SourceCuspDatum.multiplier,s.datum_matrix,integralComplexMatrix_apply,
    upper_right_removed_bottom _ _ s.lower_zero,map_mul]
  change -star (levelTwoComplexCharacter (g*s.gamma))/
    (eisEmbedding (((g:SL(2,Eis))*H) 1 0)*eisEmbedding (s.upper 1 1))^2=_
  rw [map_mul,star_mul]
  have hc:=eisEmbedding_ne_zero h
  have ht:=eisEmbedding_ne_zero s.lower_unit.ne_zero
  have hd:eisEmbedding (s.upper 0 0)*eisEmbedding (s.upper 1 1)=1 := by
    rw [←map_mul,upper_diagonal_product _ s.lower_zero,map_one]
  have hp:eisEmbedding (s.upper 0 0)^2*eisEmbedding (s.upper 1 1)^2=1 := by
    rw [←mul_pow,hd,one_pow]
  field_simp [hc,ht]
  linear_combination (star (levelTwoComplexCharacter g)*star (levelTwoComplexCharacter s.gamma))*hp

lemma datum_additive_phase (h:((g:SL(2,Eis))*H) 1 0≠0) (freq:ℂ) (scale:ℂ) :
    ShortDraftTrace.breveE (-freq*(s.datum g h).dualPoint/scale)=
      ShortDraftTrace.breveE (-freq*eisEmbedding (s.upper 0 0*s.upper 0 1)/scale)*
      ShortDraftTrace.breveE (freq*eisEmbedding (s.upper 0 0)^2*
        (eisEmbedding (((g:SL(2,Eis))*H) 1 1)/eisEmbedding (((g:SL(2,Eis))*H) 1 0))/scale) := by
  rw [s.datum_dualPoint]
  rw [show -freq*(eisEmbedding (s.upper 0 0*s.upper 0 1)-
      eisEmbedding (s.upper 0 0)^2*(eisEmbedding (((g:SL(2,Eis))*H) 1 1)/
        eisEmbedding (((g:SL(2,Eis))*H) 1 0)))/scale=
    -freq*eisEmbedding (s.upper 0 0*s.upper 0 1)/scale+
      freq*eisEmbedding (s.upper 0 0)^2*eisEmbedding (((g:SL(2,Eis))*H) 1 1)/
        eisEmbedding (((g:SL(2,Eis))*H) 1 0)/scale by ring]
  simp only [AddChar.map_add_eq_mul,mul_div_assoc]

end FixedCuspShape
end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups ContDiff

namespace CompletedGauss
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

namespace ReflectedBranchData

def withFixedCuspArray {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀m k,‖rowPhase m k‖≤1) : ReflectedBranchData levelBound K I F Q :=
  d.withCanonicalCuspArray (fixedConjugateCuspArray cusp u)
    (fun m n b=>fixedConjugateCuspArray_norm_le_one cusp u m n.val b.val) rowPhase hrow

lemma withFixedCuspArray_amplitude {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀m k,‖rowPhase m k‖≤1) (i:ℕ×ℕ×ℕ) (n b:Ideal Eis) :
    (d.withFixedCuspArray cusp u rowPhase hrow).amplitude i n b=
      fixedConjugateCuspArray cusp u i.1 n b := rfl

theorem withFixedCuspArray_value {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀m k,‖rowPhase m k‖≤1)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hsupp:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W)
    (X ρ q:ℝ) (hX:0<X) (hρ:0<ρ) (hq:1<q)
    (hK:0<completedResidualScale K I Q)
    (k:idealRange (completedResidualScale K I Q))
    (hk:completedResidualScale K I Q/2≤(Ideal.absNorm k.val:ℝ)) :
    (d.withFixedCuspArray cusp u rowPhase hrow).value W X ρ q k=
      d.rawValue (fixedConjugateCuspArray cusp u) rowPhase W X ρ q k :=
  d.withCanonicalCuspArray_value (fixedConjugateCuspArray cusp u)
    (fun m n b=>fixedConjugateCuspArray_norm_le_one cusp u m n.val b.val)
    rowPhase hrow W a b ha hsupp hW X ρ q hX hρ hq hK k hk

def extractedFixedCuspArray {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (m:ℕ) (n b:Ideal Eis) : ℂ :=
  fixedConjugateCuspArray cusp u m
    (reflectionExtractedDivisor (fun p:d.primes=>p.val)
      (fun p=>completedLocalExponent I F p.val) d.label 1*n)
    (reflectionExtractedDivisor (fun p:d.primes=>p.val)
      (fun p=>completedLocalExponent I F p.val) d.label 2*b)

lemma extractedFixedCuspArray_norm_le_one {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (m:ℕ) (n b:Ideal Eis) : ‖d.extractedFixedCuspArray cusp u m n b‖≤1 :=
  fixedConjugateCuspArray_norm_le_one cusp u m _ _

lemma extractedFixedCuspArray_zero {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (m:ℕ) (n b:Ideal Eis)
    (h:¬fixedCuspArrayEligible
      (reflectionExtractedDivisor (fun p:d.primes=>p.val)
        (fun p=>completedLocalExponent I F p.val) d.label 1*n)
      (reflectionExtractedDivisor (fun p:d.primes=>p.val)
        (fun p=>completedLocalExponent I F p.val) d.label 2*b)) :
    d.extractedFixedCuspArray cusp u m n b=0 := by
  simp only [extractedFixedCuspArray,fixedConjugateCuspArray,
    fixedCuspArray_zero_of_ineligible _ _ _ _ _ h,star_zero]

def withExtractedFixedCuspArray {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀m k,‖rowPhase m k‖≤1) : ReflectedBranchData levelBound K I F Q :=
  d.withCanonicalCuspArray (d.extractedFixedCuspArray cusp u)
    (fun m n b=>d.extractedFixedCuspArray_norm_le_one cusp u m n.val b.val) rowPhase hrow

lemma withExtractedFixedCuspArray_amplitude {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀m k,‖rowPhase m k‖≤1) (i:ℕ×ℕ×ℕ) (n b:Ideal Eis) :
    (d.withExtractedFixedCuspArray cusp u rowPhase hrow).amplitude i n b=
      d.extractedFixedCuspArray cusp u i.1 n b := rfl

theorem withExtractedFixedCuspArray_value {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀m k,‖rowPhase m k‖≤1)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hsupp:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W)
    (X ρ q:ℝ) (hX:0<X) (hρ:0<ρ) (hq:1<q)
    (hK:0<completedResidualScale K I Q)
    (k:idealRange (completedResidualScale K I Q))
    (hk:completedResidualScale K I Q/2≤(Ideal.absNorm k.val:ℝ)) :
    (d.withExtractedFixedCuspArray cusp u rowPhase hrow).value W X ρ q k=
      d.rawValue (d.extractedFixedCuspArray cusp u) rowPhase W X ρ q k :=
  d.withCanonicalCuspArray_value (d.extractedFixedCuspArray cusp u)
    (fun m n b=>d.extractedFixedCuspArray_norm_le_one cusp u m n.val b.val)
    rowPhase hrow W a b ha hsupp hW X ρ q hX hρ hq hK k hk

end ReflectedBranchData
end CompletedGauss

end

end OAI
