import OAI.NumberTheory.DirichletL.Cusp.ResiduePhases

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

open scoped Classical BigOperators

namespace ShortDraftCRT
open ActualEisensteinCubic FiniteGaussPhase ConcreteTraceCRT CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]

omit [Fintype ι] in
theorem exists_strong_unit_frequency_lifts (M:Eis) (p:ι→Eis)
    (hM:∀i,IsCoprime M (p i)) (x:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    ∃h:ι→Eis,(∀i,M^2∣h i) ∧
      (∀i,Ideal.Quotient.mk (Ideal.span {p i}) (h i)=(x i:Eis⧸Ideal.span {p i})) ∧
      ∀i,IsCoprime (h i) (p i) := by
  have hx (i:ι) := exists_frequency_lift (M^2) (p i)
    (Quotient.out (x i:Eis⧸Ideal.span {p i})) (hM i).pow_left
  choose h hh hd using hx
  have he (i:ι):Ideal.Quotient.mk (Ideal.span {p i}) (h i)=(x i:Eis⧸Ideal.span {p i}) := by
    calc
      _=Ideal.Quotient.mk (Ideal.span {p i}) (Quotient.out (x i:Eis⧸Ideal.span {p i})) :=
        Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr (hd i))
      _=x i:=Ideal.Quotient.mk_out _
  refine ⟨h,hh,he,?_⟩
  intro i
  apply IsCoprime.symm
  apply (isUnit_quotient_span_iff (p i) (h i)).mp
  rw [he]
  exact (x i).isUnit

theorem finiteCrossNumerator_fraction (a c l:Eis) (p h:ι→Eis)
    (hc:c≠0) (hp:∀i,p i≠0) :
    eisEmbedding (finiteCrossNumerator a c l p h)/eisEmbedding (c*∏i,p i)=
      eisEmbedding a/eisEmbedding c+eisEmbedding l^2*
        ∑i,eisEmbedding (h i)/eisEmbedding (p i) := by
  have hR:(∏i,p i)≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hcC:=eisEmbedding_ne_zero hc
  have hRC:=eisEmbedding_ne_zero hR
  have hs:eisEmbedding (∑i,h i*cofactor p i)/eisEmbedding (∏i,p i)=
      ∑i,eisEmbedding (h i)/eisEmbedding (p i) := by
    rw [map_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    have hpi:=eisEmbedding_ne_zero (hp i)
    have hr:eisEmbedding (p i)*eisEmbedding (cofactor p i)=eisEmbedding (∏i,p i) := by
      rw [←map_mul,prime_mul_cofactor]
    rw [map_mul]
    apply (div_eq_div_iff hRC hpi).mpr
    linear_combination eisEmbedding (h i)*hr
  simp only [finiteCrossNumerator,map_add,map_mul,map_pow]
  rw [←hs]
  field_simp [hcC,hRC]

end ShortDraftCRT

open scoped BigOperators Classical

namespace IdealGaussCRT
open CubicEisenstein

theorem finite_fourier_sum_reindex {ι T : Type*} [Fintype ι]
    (R : ι→Type*) [CommRing T] [∀i,CommRing (R i)]
    [Fintype T] [∀i,Fintype (R i)] (e:T≃+*∀i,R i)
    (ψ:AddChar T ℂ) (ψi:∀i,AddChar (R i) ℂ) (k:∀i,(R i)ˣ)
    (hψ:∀i,coordinateAddChar R e ψ i=(ψi i).mulShift (k i:R i))
    (φ:∀i,R i→ℂ) (weight:(∀i,R i)→ℂ) :
    (∑H:T,finiteAdditiveFourierCoeff ψ (fun t=>∏i,φ i (e t i)) H*
      weight (fun i=>(k i:R i)*e H i))=
    ∑h:∀i,R i,(∏i,finiteAdditiveFourierCoeff (ψi i) (φ i) (h i))*weight h := by
  let E:T≃(∀i,R i):=e.toEquiv.trans (Equiv.piCongrRight (fun i=>(k i).mulLeft))
  have hc (H:T) : finiteAdditiveFourierCoeff ψ (fun t=>∏i,φ i (e t i)) H=
      ∏i,finiteAdditiveFourierCoeff (ψi i) (φ i) ((k i:R i)*e H i) := by
    rw [finiteAdditiveFourierCoeff_crt]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hψ,finiteAdditiveFourierCoeff_mulShift]
  simp only [hc]
  exact Equiv.sum_comp E
    (fun h:∀i,R i=>(∏i,finiteAdditiveFourierCoeff (ψi i) (φ i) (h i))*weight h)

end IdealGaussCRT

namespace FiniteGaussPhase
open ActualEisensteinCubic CubicEisenstein IdealGaussCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem product_trace_fourier_sum_reindex {ι : Type*} [Fintype ι]
    (p:ι→Eis) (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    [Fintype (Eis⧸Ideal.span {∏i,p i})] [∀i,Fintype (Eis⧸Ideal.span {p i})]
    (φ:∀i,(Eis⧸Ideal.span {p i})→ℂ)
    (weight:(∀i,Eis⧸Ideal.span {p i})→ℂ) :
    (∑H:Eis⧸Ideal.span {∏i,p i},finiteAdditiveFourierCoeff
      (quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))
      (fun t=>∏i,φ i (productElementCRT p hcop t i)) H*
      weight (fun i=>(productTraceShift p hp hcop i:Eis⧸Ideal.span {p i})*productElementCRT p hcop H i))=
    ∑h:∀i,Eis⧸Ideal.span {p i},
      (∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i)) (φ i) (h i))*weight h := by
  exact finite_fourier_sum_reindex (fun i=>Eis⧸Ideal.span {p i})
    (productElementCRT p hcop) _ (fun i=>quotientTrace (p i) (hp i))
    (productTraceShift p hp hcop) (productTraceShift_character p hp hcop) φ weight

end FiniteGaussPhase

namespace FixedRayActiveSet

lemma sum_nonzero_ite {F : Type*} [Field F] [Fintype F] (f:F→ℂ) :
    (∑x:F,if x≠0 then f x else 0)=∑u:Fˣ,f (u:F) := by
  calc
    _ = ∑x∈(Finset.univ:Finset F).filter (fun x=>x≠0),f x := by rw [Finset.sum_filter]
    _ = ∑x:{x:F//x≠0},f x := by
      apply Finset.sum_subtype
      intro x
      simp
    _ = _ := (Equiv.sum_comp unitsEquivNeZero (fun x:{x:F//x≠0}=>f x)).symm

def activeStratum {ι : Type*} [Fintype ι]
    (F : ι→Type*) [∀i,Field (F i)] [∀i,Fintype (F i)] (A:Finset ι) :
    Finset (∀i,F i) := Finset.univ.filter (fun h=>∀i,h i≠0↔i∈A)

theorem sum_active_stratum {ι : Type*} [Fintype ι]
    (F : ι→Type*) [∀i,Field (F i)] [∀i,Fintype (F i)]
    (A:Finset ι) (f:∀i,F i→ℂ) :
    (∑h∈activeStratum F A,∏i,f i (h i))=
      (∏i∈A,∑u:(F i)ˣ,f i (u:F i))*
        (∏i∈(Finset.univ:Finset ι)\A,f i 0) := by
  classical
  let g:=fun i (x:F i)=>if (x≠0↔i∈A) then f i x else 0
  have hs : (∑h∈activeStratum F A,∏i,f i (h i))=
      ∏i,∑x:F i,g i x := by
    rw [activeStratum,Finset.sum_filter]
    calc
      _ = ∑h:∀i,F i,∏i,g i (h i) := by
        apply Finset.sum_congr rfl
        intro h hh
        exact (Fintype.prod_ite_zero (p:=fun i=>h i≠0↔i∈A) (f:=fun i=>f i (h i))).symm
      _ = _ := (Fintype.prod_sum g).symm
  have hg (i:ι) : (∑x:F i,g i x)=if i∈A then ∑u:(F i)ˣ,f i (u:F i) else f i 0 := by
    by_cases hi:i∈A
    · simpa only [g,hi,iff_true,ite_true] using sum_nonzero_ite (f i)
    · simp [g,hi]
  rw [hs]
  simp only [hg,Finset.prod_ite]
  have ha : (Finset.univ:Finset ι).filter (fun i=>i∈A)=A := by ext i;simp
  have hn : (Finset.univ:Finset ι).filter (fun i=>i∉A)=(Finset.univ:Finset ι)\A := by ext i;simp
  rw [ha,hn]

theorem sum_by_active_strata {ι : Type*} [Fintype ι]
    (F : ι→Type*) [∀i,Field (F i)] [∀i,Fintype (F i)]
    (weight:(∀i,F i)→ℂ) :
    (∑h:∀i,F i,weight h)=
      ∑A∈(Finset.univ:Finset ι).powerset,∑h∈activeStratum F A,weight h := by
  classical
  symm
  simp only [activeStratum,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  let A:Finset ι:=Finset.univ.filter (fun i=>h i≠0)
  have he : ∀i,h i≠0↔i∈A := by intro i;simp [A]
  rw [Finset.sum_eq_single A]
  · simp only [he,implies_true,ite_true]
  · intro B hB hBA
    have hbad : ¬(∀i,h i≠0↔i∈B) := by
      intro hgood
      apply hBA
      ext i
      simpa only [A,Finset.mem_filter,Finset.mem_univ,true_and] using (hgood i).symm
    simp only [hbad,ite_false]
  · intro hnot
    exact (hnot (Finset.mem_powerset.mpr (Finset.filter_subset _ _))).elim

end FixedRayActiveSet

namespace LocalReflectionBrackets
open ActualEisensteinCubic CubicEisenstein CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance stratumField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance stratumFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

theorem canonical_active_stratum {ι : Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (hchar:∀i,ringChar (Eis⧸P i)≠2)
    (ψ:∀i,AddChar (Eis⧸P i) ℂ) (hψ:∀i,(ψ i).IsPrimitive)
    (A:Finset ι) (j:ι→ℕ) (hj:∀i,j i<6)
    (σ ε:∀i,(Eis⧸P i)ˣ) (x:∀i,Eis⧸P i) :
    (∑h∈FixedRayActiveSet.activeStratum (fun i=>Eis⧸P i) A,
      ∏i,frequencyRow (actualSextic (P i) (hg i)) (ψ i) (j i) (σ i) (ε i) (x i) (h i))=
    (∏i∈A,(((actualSextic (P i) (hg i))⁻¹)^2) (σ i)*
      phase (actualSextic (P i) (hg i)) (ψ i) (j i) (ε i)*
      bracket (actualSextic (P i) (hg i)) (j i) (x i))*
    (∏i∈(Finset.univ:Finset ι)\A,if j i=0 then 1-(Fintype.card (Eis⧸P i):ℂ)⁻¹ else 0) := by
  rw [FixedRayActiveSet.sum_active_stratum]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    exact canonical_frequencyRow_units (P i) (hg i) (hchar i) (ψ i) (hψ i) (j i) (hj i) (σ i) (ε i) (x i)
  · apply Finset.prod_congr rfl
    intro i hi
    exact canonical_frequencyRow_zero (P i) (hg i) (hchar i) (ψ i) (j i) (hj i) (σ i) (ε i) (x i)

end LocalReflectionBrackets

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedTraceLambda_dvd_of_lambda_dvd (h:Eis) (hh:lambda∣h) :
    ramifiedTraceLambda∣h := by
  obtain ⟨q,hq⟩:=hh
  refine ⟨(paperLambdaUnit⁻¹:Eisˣ)*q,?_⟩
  change h=paperLambda*((paperLambdaUnit⁻¹:Eisˣ)*q)
  rw [paperLambda_eq,hq]
  have hu : (paperLambdaUnit:Eis)*(paperLambdaUnit⁻¹:Eisˣ)=1 := by
    simpa only [Units.val_mul,Units.val_one] using
      congrArg (fun v:Eisˣ=>(v:Eis)) (mul_inv_cancel paperLambdaUnit)
  calc
    _=(paperLambdaUnit:Eis)*(paperLambdaUnit⁻¹:Eisˣ)*(lambda*q) := by rw [hu,one_mul]
    _=_ := by ring

def paperLambdaQuotient (h:Eis) : Eis :=
  if hh:ramifiedTraceLambda∣h then hh.choose else 0

lemma paperLambdaQuotient_mul (h:Eis) (hh:ramifiedTraceLambda∣h) :
    ramifiedTraceLambda*paperLambdaQuotient h=h := by
  simp only [paperLambdaQuotient,dite_eq_left hh]
  exact hh.choose_spec.symm

lemma sourceCuspCoefficients_ramified_divisibility (j:Fin 3) (hj:j≠0) (h:Eis)
    (hh:(sourceCuspCoefficients j).value h≠0) : ramifiedTraceLambda∣h := by
  apply ramifiedTraceLambda_dvd_of_lambda_dvd
  fin_cases j
  · exact (hj rfl).elim
  · exact (ramifiedBesselValue_exact_lambda_valuation false h hh).1
  · exact (ramifiedBesselValue_exact_lambda_valuation true h hh).1

def sourceCuspPhaseNumerator (j:Fin 3) (u h:Eis) : Eis :=
  if j=0 then ramifiedTraceLambda*u^2*h else -u^2*paperLambdaQuotient h

lemma sourceCuspPhaseNumerator_embedding (j:Fin 3) (u h:Eis)
    (hh:(sourceCuspCoefficients j).value h≠0) :
    eisEmbedding (sourceCuspPhaseNumerator j u h)=
      -eisLam^4*cuspFrequency h*(eisEmbedding u)^2/(sourceCuspScale j:ℂ) := by
  by_cases hj:j=0
  · subst j
    simp only [sourceCuspPhaseNumerator,ite_true,map_mul,map_pow,
      ramifiedEmbedding_traceLambda,cuspFrequency,sourceCuspScale]
    norm_num only [Matrix.cons_val_zero,Complex.ofReal_one,div_one]
    field_simp [eisLam_ne_zero]
    linear_combination (eisEmbedding h*(eisEmbedding u)^2)*TraceLambdaPhase.eisLam_sq
  · have hdiv:=sourceCuspCoefficients_ramified_divisibility j hj h hh
    have hprod:=congrArg eisEmbedding (paperLambdaQuotient_mul h hdiv)
    have hscale:sourceCuspScale j=3 := by fin_cases j <;> simp_all [sourceCuspScale]
    have hfour:eisLam^4=(9:ℂ) := by
      calc
        eisLam^4=(eisLam^2)^2:=by ring
        _=9:=by rw [TraceLambdaPhase.eisLam_sq];norm_num
    rw [sourceCuspPhaseNumerator,ite_eq_right hj]
    simp only [map_mul,map_neg,map_pow]
    rw [cuspFrequency,hscale,←hprod,map_mul,ramifiedEmbedding_traceLambda,hfour]
    norm_num only [Complex.ofReal_ofNat]
    field_simp [eisLam_ne_zero]
    ; ring

lemma sourceCuspPhaseNumerator_phase (j:Fin 3) (u h c d:Eis) (hc:c≠0)
    (hh:(sourceCuspCoefficients j).value h≠0) :
    ShortDraftTrace.breveE (cuspFrequency h*(eisEmbedding u)^2*
      (eisEmbedding d/eisEmbedding c)/(sourceCuspScale j:ℂ))=
    ShortDraftTrace.breveE (-(eisEmbedding d*
      (eisEmbedding (sourceCuspPhaseNumerator j u h)/eisLam^4))/eisEmbedding c) := by
  rw [sourceCuspPhaseNumerator_embedding j u h hh]
  congr 1
  field_simp [eisLam_ne_zero,eisEmbedding_ne_zero hc,
    Complex.ofReal_ne_zero.mpr (sourceCuspScale_pos j).ne']

end CubicEisenstein

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve QuadraticAllOddCRT
open ConcreteTraceCRT UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

def cubicTwoSupplement : Eis→*ℂ where
  toFun n:=(actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2) (Ideal.Quotient.mk cubicTwoIdeal n)
  map_one' := by simp
  map_mul' x y := by simp only [map_mul]

def quadraticTwoSupplement : Eis→*ℂ :=
  InitialMeanSquare.normCharacter (ZMod.χ₈.ringHomComp (Int.castRingHom ℂ))

def twoSupplement : Eis→*ℂ := cubicTwoSupplement^2*quadraticTwoSupplement

lemma cubicTwoSupplement_norm (n:Eis) : ‖cubicTwoSupplement n‖≤1 := by
  change ‖(actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2)
    (Ideal.Quotient.mk cubicTwoIdeal n)‖≤1
  exact FiniteRayExpansion.norm_char_le_one _ _

lemma twoSupplement_norm (n:Eis) : ‖twoSupplement n‖≤1 := by
  change ‖cubicTwoSupplement n^2*quadraticTwoSupplement n‖≤1
  rw [norm_mul,norm_pow]
  apply (mul_le_of_le_one_left (norm_nonneg _)
    _).trans (InitialMeanSquare.normCharacter_norm_le_one _ n)
  exact pow_le_one₀ (norm_nonneg _) (cubicTwoSupplement_norm n)

lemma cubicTwoSupplement_periodic (x y:Eis) (hxy:x-y∈Ideal.span {(8:Eis)}) :
    cubicTwoSupplement x=cubicTwoSupplement y := by
  have h2:x-y∈cubicTwoIdeal:=by
    obtain ⟨k,hk⟩:=Ideal.mem_span_singleton.mp hxy
    apply Ideal.mem_span_singleton.mpr
    refine ⟨-4*k,?_⟩
    change x-y=(-2:Eis)*(-4*k)
    rw [hk]
    ring
  change (actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2) (Ideal.Quotient.mk cubicTwoIdeal x)=
    (actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2) (Ideal.Quotient.mk cubicTwoIdeal y)
  rw [Ideal.Quotient.eq.mpr h2]

lemma twoSupplement_periodic :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(8:Eis)}) twoSupplement := by
  intro x y hxy
  change cubicTwoSupplement x^2*quadraticTwoSupplement x=
    cubicTwoSupplement y^2*quadraticTwoSupplement y
  rw [cubicTwoSupplement_periodic x y hxy]
  congr 1
  exact CanonicalCoefficientClass.normCharacter_factorsModulo _ x y hxy

lemma idealRowHom_two_prime (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (hs:Supported (Ideal.span {p})) :
    idealRowHom (2:Eis) (Ideal.span {p})=twoSupplement p := by
  let:(Ideal.span {p}).IsMaximal:=PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let:Field (Eis⧸Ideal.span {p}):=Ideal.Quotient.field _
  let:Fintype (Eis⧸Ideal.span {p}):=Fintype.ofFinite _
  obtain ⟨hg,hc⟩:=supported_prime_data p hp hs
  have h2:idealRowHom (2:Eis) (Ideal.span {p})^2=cubicTwoSupplement p:=by
    rw [idealRowHom_prime _ _ hg]
    have he:=canonicalSextic_four_eq_fixed_two (Ideal.span {p}) hg p rfl hprimary
    have hfour:Ideal.Quotient.mk (Ideal.span {p}) (4:Eis)=
      (Ideal.Quotient.mk (Ideal.span {p}) (2:Eis))^2:=by norm_num [map_ofNat]
    rw [hfour,map_pow] at he
    change (actualSextic (Ideal.span {p}) hg) (Ideal.Quotient.mk _ 2)^2=
      (actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2) (Ideal.Quotient.mk cubicTwoIdeal p)
    rw [canonicalSextic_pow_two]
    exact he
  have h3:idealRowHom (2:Eis) (Ideal.span {p})^3=quadraticTwoSupplement p:=by
    rw [idealRowHom_prime _ _ hg,←MulChar.pow_apply' _ (by decide : (3:ℕ)≠0),actualSextic_cube_quadratic]
    change ((quadraticChar (Eis⧸Ideal.span {p}) (Ideal.Quotient.mk _ (2:Eis)):ℤ):ℂ)=_
    simp only [map_ofNat]
    rw [quadraticChar_two hc]
    have hn:Ideal.absNorm (Ideal.span {p})=Fintype.card (Eis⧸Ideal.span {p}):=by
      rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]
    change ((ZMod.χ₈ (Fintype.card (Eis⧸Ideal.span {p})):ℤ):ℂ)=
      ((ZMod.χ₈ (Ideal.absNorm (Ideal.span {p})):ℤ):ℂ)
    rw [hn]
  have hn2:(2:Eis)∉Ideal.span {p}:=by
    intro hz
    have he: (2:Eis⧸Ideal.span {p})=0:=by
      simpa only [map_ofNat] using Ideal.Quotient.eq_zero_iff_mem.mpr hz
    exact Ring.two_ne_zero hc he
  have h6:idealRowHom (2:Eis) (Ideal.span {p})^6=1:=by
    rw [idealRowHom_prime _ _ hg]
    have he:=canonicalSextic_sixth_power_mask (Ideal.span {p}) hg (2:Eis)
    change actualSextic _ hg (Ideal.Quotient.mk _ ((2:Eis)^6))=_ at he
    simpa only [map_pow,ite_eq_right hn2] using he
  calc
    _=idealRowHom (2:Eis) (Ideal.span {p})*idealRowHom (2:Eis) (Ideal.span {p})^6:=by rw [h6,mul_one]
    _=idealRowHom (2:Eis) (Ideal.span {p})^3*(idealRowHom (2:Eis) (Ideal.span {p})^2)^2:=by ring
    _=twoSupplement p:=by
      rw [h2,h3]
      change quadraticTwoSupplement p*cubicTwoSupplement p^2=cubicTwoSupplement p^2*quadraticTwoSupplement p
      ring

theorem idealRowHom_two_formula (n:Eis) (hn:lambda^2∣n-1)
    (hs:Supported (Ideal.span {n})) :
    idealRowHom (2:Eis) (Ideal.span {n})=twoSupplement n := by
  have hn0:n≠0:=by intro hz;apply hs.1;simp [hz]
  obtain ⟨s,hprod,hfactors⟩:=exists_primary_prime_factorization n hn0 hn
  rw [←hprod] at hs ⊢
  clear hprod hn hn0 n
  induction s using Multiset.induction_on with
  | empty=>simp only [Multiset.prod_zero,Ideal.span_singleton_one,←Ideal.one_eq_top,map_one]
  | @cons p s ih=>
    have hp:=hfactors p (Multiset.mem_cons_self _ _)
    have htail:∀q∈s,Prime q ∧ lambda^2∣q-1:=fun q hq=>hfactors q (Multiset.mem_cons_of_mem hq)
    have hsplit:Supported (Ideal.span {p}) ∧ Supported (Ideal.span {s.prod}):=by
      simpa only [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,supported_mul_iff] using hs
    rw [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,map_mul,
      idealRowHom_two_prime p hp.1 hp.2 hsplit.1,ih hsplit.2 htail,map_mul]

end

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

def supportedIdealRow (a:Eis) : Eis→*ℂ where
  toFun n:=if Supported (Ideal.span {n}) then idealRowHom a (Ideal.span {n}) else 0
  map_one' := by
    have hs:Supported (1:Ideal Eis):=⟨one_ne_zero,by
      intro P hP
      rw [normalizedFactors_one] at hP
      exact False.elim (Multiset.notMem_zero P hP)⟩
    rw [show Ideal.span {(1:Eis)}=(1:Ideal Eis) by simp only [Ideal.span_singleton_one,Ideal.one_eq_top],
      ite_eq_left hs,map_one]
  map_mul' x y := by
    rw [←Ideal.span_singleton_mul_span_singleton,supported_mul_iff,map_mul]
    by_cases hx:Supported (Ideal.span {x}) <;> by_cases hy:Supported (Ideal.span {y}) <;> simp [hx,hy]

lemma supportedIdealRow_norm (a n:Eis) : ‖supportedIdealRow a n‖≤1 := by
  change ‖if _ then _ else _‖≤_
  split_ifs
  · exact idealRowHom_norm _ _
  · simp

lemma exists_supported_primary_unit (x:Eis) (hx:Supported (Ideal.span {x})) :
    ∃u:Eisˣ,lambda^2∣u.val*x-1 := by
  have hg:=supported_primaryGenerator_ne_zero (Ideal.span {x}) hx
  have hp:=primaryGenerator_spec (Ideal.span {x}) hg
  have ha:Associated x (primaryGenerator (Ideal.span {x})):=
    Ideal.span_singleton_eq_span_singleton.mp hp.1.symm
  obtain ⟨u,hu⟩:=ha
  refine ⟨u,?_⟩
  have he:u.val*x=primaryGenerator (Ideal.span {x}):=by simpa only [mul_comm] using hu
  rw [he]
  exact hp.2

theorem supportedIdealRow_lambda_periodic :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(36:Eis)}) (supportedIdealRow lambda) := by
  intro x y hxy
  have hs:=CanonicalUnitEuler.supported_span_congruent_mod_thirty_six x y hxy
  change (if Supported (Ideal.span {x}) then _ else 0)=
    (if Supported (Ideal.span {y}) then _ else 0)
  by_cases hx:Supported (Ideal.span {x})
  · have hy:=hs.mp hx
    rw [ite_eq_left hx,ite_eq_left hy]
    obtain ⟨u,hux⟩:=exists_supported_primary_unit x hx
    have h36:(36:Eis)∣u.val*x-u.val*y:=by
      convert dvd_mul_of_dvd_right (Ideal.mem_span_singleton.mp hxy) u.val using 1 ; ring
    have hl:lambda^2∣u.val*x-u.val*y:=
      lambda_sq_dvd_three.trans ((show (3:Eis)∣36 from ⟨12,by norm_num⟩).trans h36)
    have huy:lambda^2∣u.val*y-1:=by
      convert dvd_sub hux hl using 1 ; ring
    have hsp (z:Eis) : Ideal.span {u.val*z}=Ideal.span {z}:=
      Ideal.span_singleton_mul_left_unit u.isUnit z
    have he:=idealRowHom_lambda_mod_thirty_six (u.val*x) (u.val*y) hux huy
      (by rwa [hsp]) (by rwa [hsp]) h36
    simpa only [hsp] using he
  · rw [ite_eq_right hx,ite_eq_right (fun hy=>hx (hs.mpr hy))]

lemma supportedIdealRow_lambda_primary (n:Eis) (hs:Supported (Ideal.span {n})) :
    supportedIdealRow lambda n=idealRowHom lambda (Ideal.span {n}) := by
  change (if Supported (Ideal.span {n}) then _ else _)=_
  rw [ite_eq_left hs]

end
section

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

lemma negative_two_prime : Prime (-2:Eis) :=
  (Ideal.span_singleton_prime (by norm_num : (-2:Eis)≠0)).mp
    (show (Ideal.span {(-2:Eis)}).IsPrime from cubicTwoIdeal_isMaximal.isPrime)

theorem exists_supported_numerator_factorization (x:Eis) (hx:x≠0) :
    ∃u:Eisˣ,∃a b:ℕ,∃r:Eis,Supported (Ideal.span {r}) ∧ lambda^2∣r-1 ∧
      x=u.val*lambda^a*(2:Eis)^b*r := by
  obtain ⟨n,u,a,hn,hxform⟩:=CubicEisenstein.exists_primary_unit_lambda_factor x hx
  have hn0:n≠0:=by
    intro hz
    exact hx (by rw [hxform,hz,zero_mul])
  obtain ⟨r,hr,hrnot⟩:=(FiniteMultiplicity.of_prime_left negative_two_prime hn0).exists_eq_pow_mul_and_not_dvd
  let b:ℕ:=multiplicity (-2:Eis) n
  change n=(-2:Eis)^b*r at hr
  have hp:lambda^2∣(-2:Eis)^b-1:=neg_two_primary.trans (sub_one_dvd_pow_sub_one (-2:Eis) b)
  have hprimary:lambda^2∣r-1:=by
    have hh:=dvd_sub hn (dvd_mul_of_dvd_left hp r)
    have he:n-1-(((-2:Eis)^b-1)*r)=r-1:=by rw [hr];ring
    rwa [he] at hh
  have hnot2:¬(2:Eis)∣r:=by
    intro h2
    exact hrnot (by simpa only [neg_dvd] using h2)
  have hnotlambda:¬lambda∣r:=by
    intro hLam
    have hsub:lambda∣r-1:=(dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans hprimary
    have hone:lambda∣(1:Eis):=by
      convert dvd_sub hLam hsub using 1 ; ring
    exact PrimaryIdealUnitReindex.lambda_prime_actual.not_isUnit (isUnit_of_dvd_one hone)
  let v:Eisˣ:=u*(-1:Eisˣ)^b
  refine ⟨v,a,b,r,(supported_span_iff r).mpr ⟨hnotlambda,hnot2⟩,hprimary,?_⟩
  have hp2:(-2:Eis)^b=(-1:Eis)^b*(2:Eis)^b:=by
    rw [show (-2:Eis)=(-1)*2 by ring,mul_pow]
  rw [hxform,hr,hp2]
  dsimp only [v]
  simp only [Units.val_mul,Units.val_pow_eq_pow_val,Units.coe_neg_one]
  ring

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalUnitEuler
local notation "Eis" => ActualEisensteinCubic.O

lemma idealRowHom_argument_pow (a:Eis) (k:ℕ) (I:Ideal Eis) (hI:Supported I) :
    idealRowHom (a^k) I=(idealRowHom a I)^k := by
  induction k with
  | zero => simpa only [pow_zero] using idealRowHom_one_supported I hI
  | succ k ih => rw [pow_succ,idealRowHom_argument_mul,ih,pow_succ]

def reciprocityPhaseMonoid (r:Eis) (hr:Supported (Ideal.span {r})) : Eis→*ℂ where
  toFun n:=sexticReciprocityPhase r n
  map_one' := sexticReciprocityPhase_one_right r hr
  map_mul' := sexticReciprocityPhase_mul_right r

def numeratorBadTwist (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r})) : Eis→*ℂ :=
  unitSupplement u * supportedIdealRow lambda^a * twoSupplement^b * reciprocityPhaseMonoid r hr

lemma numeratorBadTwist_norm (u:Eisˣ) (a b:ℕ) (r:Eis)
    (hr:Supported (Ideal.span {r})) (n:Eis) : ‖numeratorBadTwist u a b r hr n‖≤1 := by
  change ‖((unitSupplement u n * (supportedIdealRow lambda n)^a) * (twoSupplement n)^b) *
    sexticReciprocityPhase r n‖≤1
  simp only [norm_mul,norm_pow]
  have hu:=unitSupplement_norm u n
  have ha:‖supportedIdealRow lambda n‖^a≤1:=
    pow_le_one₀ (norm_nonneg _) (supportedIdealRow_norm lambda n)
  have hb:‖twoSupplement n‖^b≤1:=
    pow_le_one₀ (norm_nonneg _) (twoSupplement_norm n)
  have hrn:=sexticReciprocityPhase_norm r n
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _)
    ((mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) hu).trans ha)).trans hb)).trans hrn

lemma numeratorBadTwist_periodic (u:Eisˣ) (a b:ℕ) (r:Eis)
    (hr:Supported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(72:Eis)}) (numeratorBadTwist u a b r hr) := by
  intro x y hxy
  have h72:(72:Eis)∣x-y:=Ideal.mem_span_singleton.mp hxy
  have h36:x-y∈(Ideal.span {(36:Eis)}:Ideal Eis):=
    Ideal.mem_span_singleton.mpr ((show (36:Eis)∣72 from ⟨2,by norm_num⟩).trans h72)
  have h8:x-y∈(Ideal.span {(8:Eis)}:Ideal Eis):=
    Ideal.mem_span_singleton.mpr ((show (8:Eis)∣72 from ⟨9,by norm_num⟩).trans h72)
  have h4:(4:Eis)∣x-y:=(show (4:Eis)∣72 from ⟨18,by norm_num⟩).trans h72
  change ((unitSupplement u x * (supportedIdealRow lambda x)^a) * (twoSupplement x)^b) *
      sexticReciprocityPhase r x =
    ((unitSupplement u y * (supportedIdealRow lambda y)^a) * (twoSupplement y)^b) *
      sexticReciprocityPhase r y
  rw [unitSupplement_periodic u x y h36,supportedIdealRow_lambda_periodic x y h36,
    twoSupplement_periodic x y h8,sexticReciprocityPhase_congr_right r x y h4]

def movingNumeratorRow (r:Eis) (hr:Supported (Ideal.span {r})) : Eis→*ℂ where
  toFun n:=idealRowHom n (Ideal.span {r})
  map_one' := idealRowHom_one_supported _ hr
  map_mul' a b := idealRowHom_argument_mul a b _

lemma movingNumeratorRow_norm (r:Eis) (hr:Supported (Ideal.span {r})) (n:Eis) :
    ‖movingNumeratorRow r hr n‖≤1 := idealRowHom_norm n _

lemma movingNumeratorRow_periodic (r:Eis) (hr:Supported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {r}) (movingNumeratorRow r hr) :=
  idealRowHom_congr_mod _

theorem idealRowHom_factor_numerator (u:Eisˣ) (a b:ℕ) (r n:Eis)
    (hr:Supported (Ideal.span {r})) (hpr:lambda^2∣r-1)
    (hn:Supported (Ideal.span {n})) (hpn:lambda^2∣n-1) :
    idealRowHom (u.val*lambda^a*(2:Eis)^b*r) (Ideal.span {n})=
      numeratorBadTwist u a b r hr n * movingNumeratorRow r hr n := by
  have hu:unitSupplement u n=idealRowHom u.val (Ideal.span {n}):=by
    change (if Supported (Ideal.span {n}) then _ else 0)=_
    rw [ite_eq_left hn]
  have hrec:=reciprocalRow_eq_idealRowHom r n hr hn hpr hpn
  change sexticReciprocityPhase r n*idealRowHom n (Ideal.span {r})=
    idealRowHom r (Ideal.span {n}) at hrec
  change _=(((unitSupplement u n * (supportedIdealRow lambda n)^a) * (twoSupplement n)^b) *
    sexticReciprocityPhase r n)*idealRowHom n (Ideal.span {r})
  rw [idealRowHom_argument_mul,idealRowHom_argument_mul,idealRowHom_argument_mul,
    idealRowHom_argument_pow _ _ _ hn,idealRowHom_argument_pow _ _ _ hn,
    hu,supportedIdealRow_lambda_primary n hn,←idealRowHom_two_formula n hpn hn,←hrec]
  ring

end CanonicalRowCompletion

end

end OAI
