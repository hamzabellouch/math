import OAI.NumberTheory.DirichletL.GaussSum.BesselReflection

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

open scoped BigOperators Classical

namespace CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma cubeWeight_zero_of_primaryGenerator_zero (Ψ:Eis→*ℂ) (I:Ideal Eis)
    (h:primaryGenerator I=0) : cubeWeight Ψ I=0 := by
  simp [cubeWeight,h,FiniteGaussPhase.angularFactor]

lemma completedMellinCoefficient_support (Ψ:Eis→*ℂ) (p:CompletedMellinIndex)
    (hp:completedMellinCoefficient Ψ p≠0) :
    Squarefree p.1.val ∧ primaryGenerator p.1.val≠0 ∧ primaryGenerator p.2.val≠0 := by
  have hleft:Squarefree p.1.val ∧ primaryGenerator p.1.val≠0 := by
    by_contra hh
    apply hp
    simp only [completedMellinCoefficient,columnWeight,squarefreeGaussCoefficient,
      dite_eq_right hh,zero_mul,zero_div]
  refine ⟨hleft.1,hleft.2,?_⟩
  intro hright
  apply hp
  rw [completedMellinCoefficient,cubeWeight_zero_of_primaryGenerator_zero Ψ _ hright,mul_zero]

lemma completedMellinCoefficient_zero_off_support (Ψ:Eis→*ℂ) (p:CompletedMellinIndex)
    (hp:¬(Squarefree p.1.val ∧ primaryGenerator p.1.val≠0 ∧ primaryGenerator p.2.val≠0)) :
    completedMellinCoefficient Ψ p=0 := by
  by_contra hn
  exact hp (completedMellinCoefficient_support Ψ p hn)

def primaryCubePairToMellinIndex
    (p:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
      {J:Ideal Eis // primaryGenerator J≠0})) : CompletedMellinIndex :=
  (⟨p.1.val,p.1.property.1.ne_zero⟩,
    ⟨p.2.val,primaryGenerator_ne_zero_ideal p.2.val p.2.property⟩)

lemma primaryCubePairToMellinIndex_injective : Function.Injective primaryCubePairToMellinIndex := by
  intro p q hpq
  exact Prod.ext
    (Subtype.ext (congrArg (fun x:CompletedMellinIndex=>x.1.val) hpq))
    (Subtype.ext (congrArg (fun x:CompletedMellinIndex=>x.2.val) hpq))

theorem completedMellinCoefficient_tsum_primary_pairs (Ψ:Eis→*ℂ)
    (w:CompletedMellinIndex→ℂ) :
    (∑'p:CompletedMellinIndex,completedMellinCoefficient Ψ p*w p)=
      ∑'p:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
        {J:Ideal Eis // primaryGenerator J≠0}),
        completedMellinCoefficient Ψ (primaryCubePairToMellinIndex p)*
          w (primaryCubePairToMellinIndex p) := by
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun p=>primaryCubePairToMellinIndex p.val)
  · exact primaryCubePairToMellinIndex_injective.comp Subtype.val_injective
  · intro p hp
    change completedMellinCoefficient Ψ p*w p≠0 at hp
    have hc:completedMellinCoefficient Ψ p≠0 := by
      intro hz
      exact hp (by rw [hz,zero_mul])
    obtain ⟨hs,hI,hJ⟩:=completedMellinCoefficient_support Ψ p hc
    let q:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
      {J:Ideal Eis // primaryGenerator J≠0}):=(⟨p.1.val,hs,hI⟩,⟨p.2.val,hJ⟩)
    have hq:primaryCubePairToMellinIndex q=p := by
      exact Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
    refine ⟨⟨q,?_⟩,hq⟩
    change completedMellinCoefficient Ψ (primaryCubePairToMellinIndex q)*
      w (primaryCubePairToMellinIndex q)≠0
    simpa only [hq] using hp
  · intro p
    rfl

theorem completedBesselProfile_primary_pairs (Ψ:Eis→*ℂ) (q v:ℝ) :
    completedBesselProfile Ψ q v=
      ∑'p:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
        {J:Ideal Eis // primaryGenerator J≠0}),
        (completedMellinCoefficient Ψ (primaryCubePairToMellinIndex p)*
          (completedMellinLength (primaryCubePairToMellinIndex p):ℂ))*(v:ℂ)*
            CubicEisenstein.schlafliBesselK (1/3)
              (4*Real.pi*q*Real.sqrt (completedMellinLength (primaryCubePairToMellinIndex p))*v) := by
  unfold completedBesselProfile CubicEisenstein.radialBesselProfile
  simpa only [mul_assoc] using completedMellinCoefficient_tsum_primary_pairs Ψ
    (fun p=>(completedMellinLength p:ℂ)*(v:ℂ)*CubicEisenstein.schlafliBesselK (1/3)
      (4*Real.pi*q*Real.sqrt (completedMellinLength p)*v))

end CompletedGauss

namespace CubicEisenstein
open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology MatrixGroups

section
open CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

lemma cubicSourceConjugateFunction_levelTwo (G:levelTwo) (w:HyperbolicSpace) :
    cubicSourceConjugateFunction (integralComplexMatrix (G:SL(2,Eis)) • w)=
      star (levelTwoComplexCharacter G)*cubicSourceConjugateFunction w := by
  simp only [cubicSourceConjugateFunction,cubicSourceResidualFunction_automorphy,star_mul]
  ring

theorem cubicSourceConjugateFunction_cuspDerivative_levelTwo (G:levelTwo)
    (g H:SL(2,ℂ)) (hfactor:g=integralComplexMatrix (G:SL(2,Eis))*H)
    (hc:g 1 0≠0) (v:ℝ) (hv:0<v) :
    horizontalWirtingerBar (fun z=>cubicSourceConjugateFunction (upperPoint z v hv)) (g 0 0/g 1 0)=
      (star (levelTwoComplexCharacter G)*(-1/((g 1 0)^2*(v:ℂ)^2)))*
        horizontalWirtingerZ
          (fun z=>cubicSourceConjugateFunction (H • upperPoint z (1/(‖g 1 0‖^2*v)) (by positivity)))
          (-g 1 1/g 1 0) := by
  refine cuspDerivative_of_transform cubicSourceConjugateFunction g H
    (star (levelTwoComplexCharacter G)) ?_ hc v hv ?_
  · intro w
    rw [hfactor,mul_smul,cubicSourceConjugateFunction_levelTwo]
  · exact cubicSourceConjugateFunction_translate_split_differentiableAt H _ (by positivity)

lemma cuspBarProfile_conjugate_reflection_levelTwo (G:levelTwo)
    (g H:SL(2,ℂ)) (hfactor:g=integralComplexMatrix (G:SL(2,Eis))*H)
    (hc:g 1 0≠0) (v:ℝ) (hv:0<v) :
    cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0) v=
      reflectedCuspProfile (-star (levelTwoComplexCharacter G)/(g 1 0)^2)
        (‖g 1 0‖^2)
        (cuspZProfile (fun w=>cubicSourceConjugateFunction (H • w)) (-g 1 1/g 1 0)) v := by
  have hdual:0<(‖g 1 0‖^2*v)⁻¹ := by positivity
  rw [cuspBarProfile_positive _ _ _ hv,reflectedCuspProfile,cuspZProfile_positive _ _ _ hdual]
  have he:=cubicSourceConjugateFunction_cuspDerivative_levelTwo G g H hfactor hc v hv
  have hp:(v:ℂ)^(-2:ℂ)=((v:ℂ)^2)⁻¹ := by
    rw [Complex.cpow_neg,Complex.cpow_ofNat]
  rw [hp]
  simp only [one_div] at he
  rw [he]
  ring

lemma conjugateSource_cuspRepresentative_zProfile_decay (j:Fin 3) (z:ℂ) :
    ∃deltaLoss:ℝ,0<deltaLoss ∧ cuspZProfile (fun w=>cubicSourceConjugateFunction
      (integralComplexMatrix (cuspRepresentative j) • w)) z
        =O[atTop] (fun v:ℝ=>Real.exp (-deltaLoss*v)) := by
  fin_cases j
  · refine ⟨residualCuspDecayRate,residualCuspDecayRate_pos,?_⟩
    simpa [cuspRepresentative,cuspParameter,lowerCuspMatrix_zero]
      using cuspZProfile_conjugate_isBigO z
  · refine ⟨residualCuspDecayRate/3,div_pos residualCuspDecayRate_pos (by norm_num),?_⟩
    simpa [cuspRepresentative,cuspParameter,ramifiedCuspRoot,ramifiedOmegaUnit_val]
      using ramifiedConjugate_zProfile_isBigO false z
  · refine ⟨residualCuspDecayRate/3,div_pos residualCuspDecayRate_pos (by norm_num),?_⟩
    simpa [cuspRepresentative,cuspParameter,ramifiedCuspRoot,ramifiedOmegaUnit_val]
      using ramifiedConjugate_zProfile_isBigO true z

theorem conjugateSource_levelTwo_three_cusp_mellin_entire (G:levelTwo)
    (j:Fin 3) (g:SL(2,ℂ))
    (hfactor:g=integralComplexMatrix (G:SL(2,Eis))*integralComplexMatrix (cuspRepresentative j))
    (hc:g 1 0≠0) :
    ((∀s:ℂ,MellinConvergent
      (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0)) s) ∧
      Differentiable ℂ (mellin (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0)))) ∧
    ((∀s:ℂ,MellinConvergent
      (cuspZProfile (fun w=>cubicSourceConjugateFunction
        (integralComplexMatrix (cuspRepresentative j) • w)) (-g 1 1/g 1 0)) s) ∧
      Differentiable ℂ (mellin
        (cuspZProfile (fun w=>cubicSourceConjugateFunction
          (integralComplexMatrix (cuspRepresentative j) • w)) (-g 1 1/g 1 0)))) := by
  have hchar:levelTwoComplexCharacter G≠0 := by
    intro hz
    have hn:=norm_levelTwoComplexCharacter G
    rw [hz,norm_zero] at hn
    exact zero_ne_one hn
  have hscalar:-star (levelTwoComplexCharacter G)/(g 1 0)^2≠0 :=
    div_ne_zero (neg_ne_zero.mpr (star_ne_zero.mpr hchar)) (pow_ne_zero 2 hc)
  obtain ⟨deltaLoss,hδ,hb⟩:=conjugateSource_cuspRepresentative_zProfile_decay j (-g 1 1/g 1 0)
  exact cusp_mellin_entire_both
    (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0))
    (cuspZProfile (fun w=>cubicSourceConjugateFunction
      (integralComplexMatrix (cuspRepresentative j) • w)) (-g 1 1/g 1 0))
    (-star (levelTwoComplexCharacter G)/(g 1 0)^2) hscalar (‖g 1 0‖^2)
    residualCuspDecayRate deltaLoss (sq_pos_of_pos (norm_pos_iff.mpr hc)) residualCuspDecayRate_pos hδ
    (cuspBarProfile_conjugate_continuousOn _) (cuspZProfile_conjugate_translate_continuousOn _ _)
    (cuspBarProfile_conjugate_isBigO _) hb
    (fun v hv=>cuspBarProfile_conjugate_reflection_levelTwo G g _ hfactor hc v hv)

end

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma upper_triangular_right_cusp_ratio (g T:SL(2,ℂ)) (hT:T 1 0=0)
    (hc:(g*T) 1 0≠0) :
    g 1 0≠0 ∧ (g*T) 0 0/(g*T) 1 0=g 0 0/g 1 0 := by
  have hcol (i:Fin 2) : (g*T) i 0=g i 0*T 0 0 := by
    change (∑k:Fin 2,g i k*T k 0)=_
    rw [Fin.sum_univ_two,hT,mul_zero,add_zero]
  have hn:g 1 0*T 0 0≠0:=by rwa [hcol] at hc
  have hg: g 1 0≠0:=(mul_ne_zero_iff.mp hn).1
  have ht:T 0 0≠0:=(mul_ne_zero_iff.mp hn).2
  refine ⟨hg,?_⟩
  rw [hcol,hcol]
  field_simp

theorem conjugateSource_integral_cusp_mellin_entire (M:SL(2,Eis)) (hc:M 1 0≠0) :
    (∀s:ℂ,MellinConvergent
      (cuspBarProfile cubicSourceConjugateFunction
        (eisEmbedding (M 0 0)/eisEmbedding (M 1 0))) s) ∧
    Differentiable ℂ (mellin (cuspBarProfile cubicSourceConjugateFunction
      (eisEmbedding (M 0 0)/eisEmbedding (M 1 0)))) := by
  obtain ⟨G,j,T,hT,_,_,hM⟩:=three_cusp_decomposition M
  let g:SL(2,ℂ):=integralComplexMatrix (G:SL(2,Eis))*integralComplexMatrix (cuspRepresentative j)
  have he:integralComplexMatrix M=g*integralComplexMatrix T:=by
    rw [hM,map_mul,map_mul]
  have ht:integralComplexMatrix T 1 0=0:=by
    rw [integralComplexMatrix_apply,hT,map_zero]
  have hmc:(g*integralComplexMatrix T) 1 0≠0:=by
    rw [←he,integralComplexMatrix_apply]
    exact eisEmbedding_ne_zero hc
  obtain ⟨hg,hratio⟩:=upper_triangular_right_cusp_ratio g (integralComplexMatrix T) ht hmc
  have hresult:=(conjugateSource_levelTwo_three_cusp_mellin_entire G j g rfl hg).1
  rw [←hratio,←he] at hresult
  simpa only [integralComplexMatrix_apply] using hresult

lemma exists_integral_matrix_cusp_ratio (a c:Eis) (hc:c≠0) :
    ∃M:SL(2,Eis),M 1 0≠0 ∧
      eisEmbedding (M 0 0)/eisEmbedding (M 1 0)=eisEmbedding a/eisEmbedding c := by
  let d:Eis:=IsBezout.gcd a c
  obtain ⟨a',ha⟩:=IsBezout.gcd_dvd_left a c
  obtain ⟨c',hc'⟩:=IsBezout.gcd_dvd_right a c
  change a=d*a' at ha
  change c=d*c' at hc'
  have hd:d≠0:=by
    intro hz
    exact hc (by rw [hc',hz,zero_mul])
  have hcp:c'≠0:=by
    intro hz
    exact hc (by rw [hc',hz,mul_zero])
  obtain ⟨u,v,huv⟩:=IsBezout.gcd_eq_sum a c
  change u*a+v*c=d at huv
  have hred:u*a'+v*c'=1:=by
    apply mul_left_cancel₀ hd
    calc
      d*(u*a'+v*c')=u*a+v*c:=by rw [ha,hc'];ring
      _=d:=huv
      _=d*1:=(mul_one d).symm
  let M:SL(2,Eis):=⟨!![a',-v;c',u],by
    rw [Matrix.det_fin_two_of]
    linear_combination hred⟩
  refine ⟨M,hcp,?_⟩
  change eisEmbedding a'/eisEmbedding c'=eisEmbedding a/eisEmbedding c
  rw [ha,hc',map_mul,map_mul]
  have hde:eisEmbedding d≠0:=eisEmbedding_ne_zero hd
  have hce:eisEmbedding c'≠0:=eisEmbedding_ne_zero hcp
  field_simp

theorem conjugateSource_rational_cusp_mellin_entire (a c:Eis) (hc:c≠0) :
    (∀s:ℂ,MellinConvergent
      (cuspBarProfile cubicSourceConjugateFunction (eisEmbedding a/eisEmbedding c)) s) ∧
    Differentiable ℂ (mellin
      (cuspBarProfile cubicSourceConjugateFunction (eisEmbedding a/eisEmbedding c))) := by
  obtain ⟨M,hM,hratio⟩:=exists_integral_matrix_cusp_ratio a c hc
  simpa only [hratio] using conjugateSource_integral_cusp_mellin_entire M hM

theorem conjugateSource_finite_twist_cusp_mellin_entire (h c:Eis) (hc:c≠0) :
    (∀s:ℂ,MellinConvergent
      (cuspBarProfile cubicSourceConjugateFunction (-3*eisEmbedding h/eisEmbedding c)) s) ∧
    Differentiable ℂ (mellin
      (cuspBarProfile cubicSourceConjugateFunction (-3*eisEmbedding h/eisEmbedding c))) := by
  simpa only [map_mul,map_neg,map_ofNat] using
    conjugateSource_rational_cusp_mellin_entire (-3*h) c hc

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance signedOmegaUnitsFintype : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def signedOmegaUnit (s:Bool) (j:Fin 3) :Eisˣ :=
  if s then -(ramifiedOmegaUnit^j.val) else ramifiedOmegaUnit^j.val

lemma signedOmegaUnit_val (s:Bool) (j:Fin 3) :
    (signedOmegaUnit s j:Eis)=if s then -(omega^j.val) else omega^j.val := by
  cases s <;> simp [signedOmegaUnit,ramifiedOmegaUnit_val]

lemma signedOmegaUnit_surjective : Function.Surjective (fun p:Bool×Fin 3=>signedOmegaUnit p.1 p.2) := by
  intro u
  obtain ⟨j,hj|hj⟩:=unit_eq_sign_omega u
  · refine ⟨(false,j),Units.ext ?_⟩
    simpa only [signedOmegaUnit_val,Bool.false_eq_true,ite_false] using hj.symm
  · refine ⟨(true,j),Units.ext ?_⟩
    simpa only [signedOmegaUnit_val,ite_true] using hj.symm

def signedOmegaEquiv : (Bool×Fin 3)≃Eisˣ := Equiv.ofBijective
  (fun p=>signedOmegaUnit p.1 p.2)
  ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨signedOmegaUnit_surjective,by
    have hc:Fintype.card Eisˣ=6:=by
      simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six
    simp [hc]⟩)

lemma cubicSymbol_norm_one (c n:Eis) (hn:lambda^2∣n-1) (hc:IsCoprime c n) :
    ‖eisEmbedding (symbol c n)‖=1 := by
  have hcube:(eisEmbedding (symbol c n))^3=1:=by
    rw [←map_pow,symbol_cube_of_isCoprime c n hn hc,map_one]
  apply (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (3:ℕ)≠0)).mp
  simpa only [norm_pow,norm_one,one_pow] using congrArg norm hcube

lemma arithmeticResidueSum_norm_mul_primary (h n:Eis) (hn:lambda^2∣n-1)
    (u:Eisˣ) (r:ℕ) (hr:2≤r) :
    ‖arithmeticResidueSum (h*n) (u.val*lambda^r)‖=
      ‖arithmeticResidueSum h (u.val*lambda^r)‖ := by
  have hc: IsCoprime (u.val*lambda^r) n :=
    (ramified_primary_coprime u r n hn).of_mul_left_right
  have he:=congrArg norm (arithmeticResidueSum_frequency_twist h (u.val*lambda^r) n
    (ramifiedElement_ne_zero u r) (ramifiedElement_level u r hr)
    ⟨hc,three_dvd_lambda_sq.trans hn⟩)
  simpa only [norm_mul,cubicSymbol_norm_one _ n hn hc,one_mul] using he

def lowRamifiedFrequency (a r:Fin 3) : Eis := omega^a.val*lambda^(r.val+2)

lemma lowRamifiedFrequency_ne_zero (a r:Fin 3) : lowRamifiedFrequency a r≠0 := by
  simpa only [lowRamifiedFrequency,←ramifiedOmegaUnit_val,←Units.val_pow_eq_pow_val] using
    ramifiedElement_ne_zero (ramifiedOmegaUnit^a.val) (r.val+2)

lemma lowRamifiedFrequency_absNorm (a r:Fin 3) :
    Ideal.absNorm (Ideal.span {lowRamifiedFrequency a r})=3^(r.val+2) := by
  simpa only [lowRamifiedFrequency,←ramifiedOmegaUnit_val,←Units.val_pow_eq_pow_val] using
    ramifiedElement_absNorm (ramifiedOmegaUnit^a.val) (r.val+2)

lemma lowRamifiedFrequency_arithmetic_vanish (a r:Fin 3) (u:Eisˣ) (k:ℕ) (hk:5≤k) :
    arithmeticResidueSum (lowRamifiedFrequency a r) (u.val*lambda^(k+2))=0 := by
  by_contra hA
  have hb:=ramified_arithmetic_norm_bound _ (lowRamifiedFrequency_ne_zero a r) u (k+2) (by omega) hA
  rw [lowRamifiedFrequency_absNorm] at hb
  have hlo:(3:ℕ)^7≤3^(k+2):=Nat.pow_le_pow_right (by decide) (by omega)
  have hhi:(3:ℕ)^(r.val+2)≤3^4:=Nat.pow_le_pow_right (by decide) (by omega)
  norm_num at hlo hhi
  omega

lemma lowRamifiedFrequency_primary_vanish (a r:Fin 3) (n:Eis) (hn:lambda^2∣n-1)
    (u:Eisˣ) (k:ℕ) (hk:5≤k) :
    arithmeticResidueSum (lowRamifiedFrequency a r*n) (u.val*lambda^(k+2))=0 := by
  apply norm_eq_zero.mp
  rw [arithmeticResidueSum_norm_mul_primary _ n hn u (k+2) (by omega),
    lowRamifiedFrequency_arithmetic_vanish a r u k hk,norm_zero]

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance ramifiedCoordinateUnitsFintype : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def ramifiedCoordMul (x y:ℤ×ℤ) :ℤ×ℤ := (x.1*y.1-x.2*y.2,x.1*y.2+x.2*y.1-x.2*y.2)
def ramifiedCoordPow (x:ℤ×ℤ) :ℕ→ℤ×ℤ
  | 0=>(1,0)
  | n+1=>ramifiedCoordMul (ramifiedCoordPow x n) x

def lowRamifiedQuotientCoord (a r:Fin 3) (s:Bool) (j:Fin 3) (n:Fin 5) :ℤ×ℤ :=
  let z:=ramifiedCoordMul (ramifiedCoordPow (0,1) (a.val+5-j.val))
    (ramifiedCoordPow (-1,1) (r.val+2-n.val))
  if s then z else (-z.1,-z.2)

def lowRamifiedSupport (a r:Fin 3) (p:Bool×Fin 3×Fin 5) :Prop :=
  p.2.2.val≤r.val+2 ∧
  let z:=lowRamifiedQuotientCoord a r p.1 p.2.1 p.2.2
  (3:ℤ)∣2*(p.2.1.val:ℤ)+(p.2.2.val+2:ℕ)+z.2 ∧
  (3:ℤ)∣2*(p.2.1.val:ℤ)+z.1-z.2

instance lowRamifiedSupport_decidable (a r:Fin 3) (p:Bool×Fin 3×Fin 5) :
    Decidable (lowRamifiedSupport a r p) :=
  inferInstanceAs (Decidable (p.2.2.val≤r.val+2 ∧
    (3:ℤ)∣2*(p.2.1.val:ℤ)+(p.2.2.val+2:ℕ)+(lowRamifiedQuotientCoord a r p.1 p.2.1 p.2.2).2 ∧
    (3:ℤ)∣2*(p.2.1.val:ℤ)+(lowRamifiedQuotientCoord a r p.1 p.2.1 p.2.2).1-
      (lowRamifiedQuotientCoord a r p.1 p.2.1 p.2.2).2))

def lowRamifiedSupportSet (a r:Fin 3) :Finset (Bool×Fin 3×Fin 5) :=
  Finset.univ.filter (lowRamifiedSupport a r)

lemma lowRamifiedSupport_card (a r:Fin 3) : (lowRamifiedSupportSet a r).card≤5 := by
  decide +revert

lemma lowRamifiedSupport_exponent (a r:Fin 3) (p:Bool×Fin 3×Fin 5)
    (hp:lowRamifiedSupport a r p) : 1≤p.2.2.val := by
  decide +revert

lemma ramifiedCoordMul_eval (x y:ℤ×ℤ) :
    ActualEisensteinCoordinates.eval (ramifiedCoordMul x y).1 (ramifiedCoordMul x y).2=
      ActualEisensteinCoordinates.eval x.1 x.2*ActualEisensteinCoordinates.eval y.1 y.2 :=
  (ActualEisensteinCoordinates.eval_mul _ _ _ _).symm

lemma ramifiedCoordPow_eval (x:ℤ×ℤ) (n:ℕ) :
    ActualEisensteinCoordinates.eval (ramifiedCoordPow x n).1 (ramifiedCoordPow x n).2=
      (ActualEisensteinCoordinates.eval x.1 x.2)^n := by
  induction n with
  | zero => simp [ramifiedCoordPow,ActualEisensteinCoordinates.eval]
  | succ n ih => rw [ramifiedCoordPow,ramifiedCoordMul_eval,ih,pow_succ]

lemma lowRamifiedQuotientCoord_eval (a r:Fin 3) (s:Bool) (j:Fin 3) (n:Fin 5) :
    ActualEisensteinCoordinates.eval (lowRamifiedQuotientCoord a r s j n).1
      (lowRamifiedQuotientCoord a r s j n).2=
      if s then omega^(a.val+5-j.val)*lambda^(r.val+2-n.val)
      else -(omega^(a.val+5-j.val)*lambda^(r.val+2-n.val)) := by
  have ho:ActualEisensteinCoordinates.eval 0 1=omega:=by
    simp [ActualEisensteinCoordinates.eval]; rfl
  have hl:ActualEisensteinCoordinates.eval (-1) 1=lambda:=by
    change ActualEisensteinCoordinates.eval (-1) 1=omega-1
    have he:ActualEisensteinCoordinates.eval (-1) 1=(-1:Eis)+ActualEisensteinCoordinates.eval 0 1:=by
      simp [ActualEisensteinCoordinates.eval]
    rw [he,ho]
    ring
  have he:∀x:ℤ×ℤ,ActualEisensteinCoordinates.eval (-x.1) (-x.2)=
      -ActualEisensteinCoordinates.eval x.1 x.2:=by
    intro x
    simp only [ActualEisensteinCoordinates.eval,Int.cast_neg]
    ring
  cases s <;> simp only [lowRamifiedQuotientCoord,Bool.false_eq_true,ite_false,ite_true,
    he,ramifiedCoordMul_eval,ramifiedCoordPow_eval,ho,hl]

lemma lowRamifiedQuotientCoord_relation (a r:Fin 3) (s:Bool) (j:Fin 3) (n:Fin 5)
    (hn:n.val≤r.val+2) :
    3*lowRamifiedFrequency a r=
      ((signedOmegaUnit s j:Eis)*lambda^(n.val+2))*
        ActualEisensteinCoordinates.eval (lowRamifiedQuotientCoord a r s j n).1
          (lowRamifiedQuotientCoord a r s j n).2 := by
  have hw:omega^2=-omega-1:=by linear_combination ramified_omega_relation
  have hl:lambda^2=-3*omega:=by
    change (omega-1)^2=-3*omega
    linear_combination hw
  have h3:(3:Eis)=-omega^2*lambda^2:=by
    rw [hl]
    calc
      (3:Eis)=3*omega^3:=by rw [omega_primitive.pow_eq_one]; ring
      _=_:=by ring
  have ho:omega^j.val*omega^(a.val+5-j.val)=omega^(a.val+2):=by
    rw [←pow_add,show j.val+(a.val+5-j.val)=a.val+5 by omega]
    rw [show a.val+5=(a.val+2)+3 by omega,pow_add,omega_primitive.pow_eq_one,mul_one]
  have hp:lambda^(n.val+2)*lambda^(r.val+2-n.val)=lambda^(r.val+4):=by
    rw [←pow_add]
    congr 1
    omega
  have he:3*lowRamifiedFrequency a r=
      -(omega^j.val*omega^(a.val+5-j.val))*(lambda^(n.val+2)*lambda^(r.val+2-n.val)):=by
    rw [ho,hp,lowRamifiedFrequency]
    conv_lhs => rw [h3]
    rw [show r.val+4=2+(r.val+2) by omega,pow_add,pow_add]
    ring
  rw [lowRamifiedQuotientCoord_eval,signedOmegaUnit_val]
  cases s <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> linear_combination he

lemma lowRamifiedSupport_of_ne_zero (a r:Fin 3) (s:Bool) (j:Fin 3) (n:Fin 5)
    (hA:arithmeticResidueSum (lowRamifiedFrequency a r)
      ((signedOmegaUnit s j:Eis)*lambda^(n.val+2))≠0) :
    lowRamifiedSupport a r (s,j,n) := by
  have hn:n.val≤r.val+2:=by
    have hb:=ramified_arithmetic_norm_bound _ (lowRamifiedFrequency_ne_zero a r)
      (signedOmegaUnit s j) (n.val+2) (by omega) hA
    rw [lowRamifiedFrequency_absNorm] at hb
    have he:9*3^(r.val+2)=(3:ℕ)^(r.val+4):=by
      rw [show r.val+4=(r.val+2)+2 by omega,pow_add]
      ring
    rw [he] at hb
    have hh: n.val+2≤r.val+4 := (Nat.pow_le_pow_iff_right (by decide : 1<(3:ℕ))).mp hb
    omega
  let z:=lowRamifiedQuotientCoord a r s j n
  have hu:(signedOmegaUnit s j:Eis)=omega^j.val ∨
      (signedOmegaUnit s j:Eis)=-(omega^j.val):=by
    cases s <;> simp [signedOmegaUnit_val]
  have he:=ramified_arithmetic_explicit_table (lowRamifiedFrequency a r)
    (ActualEisensteinCoordinates.eval z.1 z.2) (signedOmegaUnit s j) (n.val+2) j.val
    (by omega) hu (lowRamifiedQuotientCoord_relation a r s j n hn)
  have hz:ramifiedCongruence (ActualEisensteinCoordinates.eval z.1 z.2) j.val (n.val+2):=by
    by_contra hc
    rw [ite_eq_right hc] at he
    exact hA he
  exact ⟨hn,by simpa only [ramifiedCongruence,ShortDraftLatticeCount.coords_eval] using hz⟩

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance ramifiedRawWeightUnitsFintype : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def ramifiedRawWeight (h:Eis) (u:Eisˣ) (k:ℕ) :ℂ :=
  ((3^(k+2):ℕ):ℂ)^(-(4/3:ℂ))*arithmeticResidueSum h (u.val*lambda^(k+2))

lemma ramifiedRawWeight_norm_le (h:Eis) (u:Eisˣ) (k:ℕ) :
    ‖ramifiedRawWeight h u k‖≤ramifiedDecayRatio^(k+2) := by
  rw [ramifiedRawWeight,norm_mul,
    arithmeticResidueSum_eq_explicitRamifiedCoefficient h u (k+2) (by omega)]
  exact (mul_le_mul_of_nonneg_left (explicitRamifiedCoefficient_norm_le h u (k+2))
    (norm_nonneg _)).trans_eq (ramifiedWeight_norm_scalar _)

lemma ramifiedRawWeight_norm_mul_primary (h n:Eis) (hn:lambda^2∣n-1) (u:Eisˣ) (k:ℕ) :
    ‖ramifiedRawWeight (h*n) u k‖=‖ramifiedRawWeight h u k‖ := by
  simp only [ramifiedRawWeight,norm_mul,
    arithmeticResidueSum_norm_mul_primary h n hn u (k+2) (by omega)]

lemma ramifiedDecayRatio_cube : ramifiedDecayRatio^3=(1/3:ℝ) := by
  rw [ramifiedDecayRatio,←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
  norm_num

lemma lowRamifiedRawWeight_bound (a r:Fin 3) (s:Bool) (j:Fin 3) (k:Fin 5) :
    ‖ramifiedRawWeight (lowRamifiedFrequency a r) (signedOmegaUnit s j) k.val‖≤
      if lowRamifiedSupport a r (s,j,k) then (1/3:ℝ) else 0 := by
  split_ifs with hs
  · have hh:1≤k.val:=lowRamifiedSupport_exponent a r (s,j,k) hs
    have hb:ramifiedDecayRatio^(k.val+2)≤ramifiedDecayRatio^3:=
      pow_le_pow_of_le_one ramifiedDecayRatio_pos.le ramifiedDecayRatio_lt_one.le (by omega)
    exact (ramifiedRawWeight_norm_le (lowRamifiedFrequency a r) (signedOmegaUnit s j) k.val).trans
      (hb.trans_eq ramifiedDecayRatio_cube)
  · have hz:arithmeticResidueSum (lowRamifiedFrequency a r)
        ((signedOmegaUnit s j:Eis)*lambda^(k.val+2))=0:=by
      by_contra hne
      exact hs (lowRamifiedSupport_of_ne_zero a r s j k hne)
    simp only [ramifiedRawWeight,hz,mul_zero,norm_zero,le_refl]

theorem lowRamifiedRawWeight_sum (a r:Fin 3) (n:Eis) (hn:lambda^2∣n-1) :
    (∑u:Eisˣ,∑k:Fin 5,‖ramifiedRawWeight (lowRamifiedFrequency a r*n) u k.val‖)≤5/3 := by
  simp_rw [ramifiedRawWeight_norm_mul_primary _ n hn]
  have hu:(∑u:Eisˣ,∑k:Fin 5,‖ramifiedRawWeight (lowRamifiedFrequency a r) u k.val‖)=
      ∑p:Bool×Fin 3,∑k:Fin 5,‖ramifiedRawWeight (lowRamifiedFrequency a r)
        (signedOmegaUnit p.1 p.2) k.val‖ := by
    symm
    exact Fintype.sum_equiv signedOmegaEquiv _ _ (fun _=>rfl)
  rw [hu]
  calc
    _≤∑p:Bool×Fin 3,∑k:Fin 5,
        if lowRamifiedSupport a r (p.1,p.2,k) then (1/3:ℝ) else 0:=by
      apply Finset.sum_le_sum
      intro p hp
      exact Finset.sum_le_sum (fun k hk=>lowRamifiedRawWeight_bound a r p.1 p.2 k)
    _=∑p:Bool×Fin 3×Fin 5,if lowRamifiedSupport a r p then (1/3:ℝ) else 0:=by
      simp only [Fintype.sum_prod_type]
    _=(lowRamifiedSupportSet a r).card*(1/3:ℝ):=by
      rw [←Finset.sum_filter]
      simp only [Finset.sum_const,nsmul_eq_mul,lowRamifiedSupportSet]
    _≤5/3:=by
      have hc:(lowRamifiedSupportSet a r).card≤5:=lowRamifiedSupport_card a r
      exact_mod_cast (show ((lowRamifiedSupportSet a r).card:ℝ)*(1/3:ℝ)≤5/3 by
        have hcr:((lowRamifiedSupportSet a r).card:ℝ)≤5:=by exact_mod_cast hc
        linarith)

end CubicEisenstein

end

end OAI
