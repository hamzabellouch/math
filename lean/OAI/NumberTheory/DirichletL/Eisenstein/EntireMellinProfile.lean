import OAI.NumberTheory.DirichletL.Eisenstein.RamifiedTransform

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
open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma finite_mellin_entire {ι : Type*} [Fintype ι] (f : ι→ℝ→ℂ) (weight : ι→ℂ)
    (hf : ∀i,(∀s:ℂ,MellinConvergent (f i) s) ∧ Differentiable ℂ (mellin (f i))) :
    (∀s:ℂ,MellinConvergent (fun v=>∑i,weight i*f i v) s) ∧
      Differentiable ℂ (mellin (fun v=>∑i,weight i*f i v)) := by
  have hs (s : ℂ) (i : ι) : MellinConvergent (fun v=>weight i*f i v) s := by
    simpa only [smul_eq_mul] using (hf i).1 s |>.const_smul (weight i)
  have hsi (s : ℂ) (i : ι) : IntegrableOn (fun v:ℝ=>(v:ℂ)^(s-1)*(weight i*f i v)) (Set.Ioi 0) := by
    simpa only [MellinConvergent,smul_eq_mul] using hs s i
  have he (s : ℂ) : mellin (fun v=>∑i,weight i*f i v) s=∑i,weight i*mellin (f i) s := by
    unfold mellin
    simp only [smul_eq_mul,Finset.mul_sum]
    rw [integral_finsetSum Finset.univ (fun i hi=>hsi s i)]
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [mellin,smul_eq_mul] using mellin_const_smul (f i) s (weight i)
  constructor
  · intro s
    change IntegrableOn (fun v:ℝ=>(v:ℂ)^(s-1)*(∑i,weight i*f i v)) (Set.Ioi 0)
    simpa only [IntegrableOn,Finset.mul_sum] using integrable_finsetSum Finset.univ (fun i hi=>hsi s i)
  · rw [show mellin (fun v=>∑i,weight i*f i v)=(fun s=>∑i,weight i*mellin (f i) s) from funext he]
    exact Differentiable.fun_sum (fun i hi=>(hf i).2.const_mul (weight i))

lemma thetaTwistedCuspProfile_mellin_entire (Ψ : Eis→*ℂ) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] :
    (∀s:ℂ,MellinConvergent (thetaTwistedCuspProfile Ψ c hc) s) ∧
      Differentiable ℂ (mellin (thetaTwistedCuspProfile Ψ c hc)) := by
  apply finite_mellin_entire
  intro h
  have he : thetaFourierTranslation c h=(-3:ℂ)*eisEmbedding (Quotient.out h)/eisEmbedding c := by
    rw [thetaFourierTranslation,TraceLambdaPhase.eisLam_sq]
  rw [he]
  exact conjugateSource_finite_twist_cusp_mellin_entire (Quotient.out h) c hc

theorem completedBesselProfile_mellin_entire_of_periodic
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q) :
    (∀s:ℂ,MellinConvergent (completedBesselProfile Ψ thetaBesselScale) s) ∧
      Differentiable ℂ (mellin (completedBesselProfile Ψ thetaBesselScale)) := by
  have hf := thetaTwistedCuspProfile_mellin_entire Ψ c hc
  have he (v : ℝ) (hv : 0<v) :
      thetaDerivativeScalar⁻¹*thetaTwistedCuspProfile Ψ c hc v=
        completedBesselProfile Ψ thetaBesselScale v := by
    rw [thetaTwistedCuspProfile_eq_completedBesselProfile Ψ Q hΨ c hc hcQ v hv,
      ←mul_assoc,inv_mul_cancel₀ thetaDerivativeScalar_ne_zero,one_mul]
  have hm (s : ℂ) : mellin (completedBesselProfile Ψ thetaBesselScale) s=
      thetaDerivativeScalar⁻¹*mellin (thetaTwistedCuspProfile Ψ c hc) s := by
    have hmul := mellin_const_smul (thetaTwistedCuspProfile Ψ c hc) s thetaDerivativeScalar⁻¹
    simp only [smul_eq_mul] at hmul
    rw [←hmul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    simp only [smul_eq_mul,he v hv]
  constructor
  · intro s
    have hi := (hf.1 s).const_smul thetaDerivativeScalar⁻¹
    apply hi.congr_fun _ measurableSet_Ioi
    intro v hv
    simp only [smul_eq_mul,he v hv]
  · rw [show mellin (completedBesselProfile Ψ thetaBesselScale)=
      (fun s=>thetaDerivativeScalar⁻¹*mellin (thetaTwistedCuspProfile Ψ c hc) s) from funext hm]
    exact hf.2.const_mul _

theorem completedBesselProfile_mellin_entire
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hQ : Q≠⊥)
    (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ) :
    (∀s:ℂ,MellinConvergent (completedBesselProfile Ψ (1/Real.sqrt 27)) s) ∧
      Differentiable ℂ (mellin (completedBesselProfile Ψ (1/Real.sqrt 27))) := by
  have h9 : (Ideal.span {(9:Eis)} : Ideal Eis)≠⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr (by norm_num)
  have hN : Ideal.span {(9:Eis)}*Q≠⊥ := fun hz=>(Ideal.mul_eq_bot.mp hz).elim h9 hQ
  let c := ConcretePrimeRowBridge.idealGenerator (Ideal.span {(9:Eis)}*Q)
  have hc : c≠0 := ConcretePrimeRowBridge.idealGenerator_ne_zero _ hN
  let : Finite (Eis⧸Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (Eis⧸Ideal.span {c}) := Fintype.ofFinite _
  have hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q := by
    rw [ConcretePrimeRowBridge.span_idealGenerator]
  simpa only [thetaBesselScale_eq] using
    completedBesselProfile_mellin_entire_of_periodic Ψ Q hΨ c hc hcQ

end CubicEisenstein

namespace CompletedGauss
open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

lemma mellin_eq_of_positive_eq (F G : ℝ→ℂ) (hFG : ∀v : ℝ,0<v→F v=G v) (s : ℂ) :
    mellin F s=mellin G s := by
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  rw [hFG v hv]

lemma continuedBesselDirichlet_finite_sum {ι : Type*} [Fintype ι]
    (F : ι→ℝ→ℂ) (w : ι→ℂ) (q : ℝ) (s : ℂ)
    (hF : ∀i,MellinConvergent (F i) (2*s)) :
    continuedBesselDirichlet (fun v=>∑i,w i*F i v) q s=
      ∑i,w i*continuedBesselDirichlet (F i) q s := by
  have hi (i : ι) : IntegrableOn (fun v : ℝ=>(v:ℂ)^(2*s-1)*(w i*F i v)) (Set.Ioi 0) := by
    simpa only [MellinConvergent,smul_eq_mul] using (hF i).const_smul (w i)
  have hm : mellin (fun v=>∑i,w i*F i v) (2*s)=∑i,w i*mellin (F i) (2*s) := by
    unfold mellin
    simp only [smul_eq_mul,Finset.mul_sum]
    rw [integral_finsetSum Finset.univ (fun i _=>hi i)]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [mellin,smul_eq_mul] using mellin_const_smul (F i) (2*s) (w i)
  rw [continuedBesselDirichlet,hm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold continuedBesselDirichlet
  ring

lemma besselSmoothingIntegrand_finite_sum {ι : Type*} [Fintype ι]
    (F : ℝ→ℂ) (G : ι→ℝ→ℂ) (w : ι→ℂ)
    (hFG : ∀v : ℝ,0<v→F v=∑i,w i*G i v)
    (q : ℝ) (V : ℝ→ℂ) (X : ℝ) (s : ℂ)
    (hG : ∀i,MellinConvergent (G i) (2*s)) :
    besselSmoothingIntegrand F q V X s=
      ∑i,w i*besselSmoothingIntegrand (G i) q V X s := by
  have hm := mellin_eq_of_positive_eq F (fun v=>∑i,w i*G i v) hFG (2*s)
  have hd : continuedBesselDirichlet F q s=
      continuedBesselDirichlet (fun v=>∑i,w i*G i v) q s := by
    simp only [continuedBesselDirichlet,hm]
  rw [besselSmoothingIntegrand,hd,continuedBesselDirichlet_finite_sum G w q s hG,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold besselSmoothingIntegrand
  ring

theorem besselSmoothingIntegrand_finite_integrable {ι : Type*} [Fintype ι]
    (F : ℝ→ℂ) (G : ι→ℝ→ℂ) (w : ι→ℂ)
    (hFG : ∀v : ℝ,0<v→F v=∑i,w i*G i v)
    (q : ℝ) (V : ℝ→ℂ) (X σ : ℝ)
    (hG : ∀i,∀t : ℝ,MellinConvergent (G i) (2*((σ:ℂ)+t*Complex.I)))
    (hi : ∀i,Integrable (fun t : ℝ=>besselSmoothingIntegrand (G i) q V X ((σ:ℂ)+t*Complex.I))) :
    Integrable (fun t : ℝ=>besselSmoothingIntegrand F q V X ((σ:ℂ)+t*Complex.I)) := by
  have hsum := integrable_finsetSum Finset.univ (fun i _=>(hi i).const_mul (w i))
  apply hsum.congr
  filter_upwards with t
  exact (besselSmoothingIntegrand_finite_sum F G w hFG q V X _ (fun i=>hG i t)).symm

end CompletedGauss

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def unramifiedResidualCoefficient (h:Eis) :ℂ:=cubicBesselNormalizer h*unramifiedGaussResidue h

lemma primeCubicGauss_two_norm (p:Eis) (hp:Prime p) (hpp:lambda^2∣p-1)
    (h:Eis) (hph:¬p∣h) : ‖primeCubicGauss p hp hpp 2 h‖=‖eisEmbedding p‖ := by
  have he:=congrArg norm (primeCubicGauss_one_mul_two p hp hpp h hph)
  rw [norm_mul,primeCubicGauss_two_eq_star,norm_star,Complex.norm_natCast] at he
  have hn:=eisEmbedding_norm_sq_eq_absNorm_span p
  have hg:0≤‖primeCubicGauss p hp hpp 1 h‖:=norm_nonneg _
  have hr:0≤‖eisEmbedding p‖:=norm_nonneg _
  rw [primeCubicGauss_two_eq_star,norm_star]
  nlinarith

lemma unramifiedResidualCoefficient_prime_factor (p:Eis) (hp:Prime p)
    (hpp:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    unramifiedResidualCoefficient (h*p)=
      (primeCubicGauss p hp hpp 2 h/(‖eisEmbedding p‖:ℂ))*unramifiedResidualCoefficient h := by
  rw [unramifiedResidualCoefficient,cubicBesselNormalizer_mul,
    unramifiedGaussResidue_prime_factor p hp hpp h hph,unramifiedResidualCoefficient]
  calc
    _=((‖eisEmbedding p‖:ℂ)^(1/3:ℂ)*(Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ)))*
      primeCubicGauss p hp hpp 2 h*(cubicBesselNormalizer h*unramifiedGaussResidue h):=by ring
    _=_:=by rw [prime_normalizer_powers p hp.ne_zero]; ring

lemma unramifiedResidualCoefficient_prime_norm (p:Eis) (hp:Prime p)
    (hpp:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    ‖unramifiedResidualCoefficient (h*p)‖=‖unramifiedResidualCoefficient h‖ := by
  rw [unramifiedResidualCoefficient_prime_factor p hp hpp h hph,norm_mul,norm_div,
    primeCubicGauss_two_norm p hp hpp h hph,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hp.ne_zero)),one_mul]

theorem unramifiedGaussResidue_primary_cube (b:Eis) (hb:b≠0)
    (hbp:lambda^2∣b-1) (h:Eis) :
    unramifiedGaussResidue (h*b^3)=unramifiedGaussResidue h := by
  obtain ⟨s,hs,hpr⟩:=exists_primary_prime_factorization b hb hbp
  rw [←hs]
  clear hs hb hbp b
  induction s using Multiset.induction_on generalizing h with
  | empty=>simp
  | @cons p s ih=>
    have hp:=hpr p (Multiset.mem_cons_self _ _)
    have hs:∀q∈s,Prime q∧lambda^2∣q-1:=fun q hq=>hpr q (Multiset.mem_cons_of_mem hq)
    rw [Multiset.prod_cons,show h*(p*s.prod)^3=(h*s.prod^3)*p^3 by ring,
      unramifiedGaussResidue_prime_cube p hp.1 hp.2]
    exact ih h hs

lemma unramifiedResidualCoefficient_primary_cube (b:Eis) (hb:b≠0)
    (hbp:lambda^2∣b-1) (h:Eis) :
    unramifiedResidualCoefficient (h*b^3)=
      (‖eisEmbedding b‖:ℂ)*unramifiedResidualCoefficient h := by
  rw [unramifiedResidualCoefficient,cubicBesselNormalizer_mul_cube h b hb,
    unramifiedGaussResidue_primary_cube b hb hbp h,unramifiedResidualCoefficient]
  ring

theorem unramifiedResidualCoefficient_prime_product_norm {ι:Type*}
    (s:Finset ι) (p:ι→Eis) (hp:∀i∈s,Prime (p i))
    (hprimary:∀i∈s,lambda^2∣p i-1)
    (hpair:∀i∈s,∀j∈s,i≠j→IsCoprime (p i) (p j))
    (h:Eis) (hph:∀i∈s,¬p i∣h) :
    ‖unramifiedResidualCoefficient (h*(∏i∈s,p i))‖=‖unramifiedResidualCoefficient h‖ := by
  classical
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert i s hi ih=>
    have hpi:=hp i (Finset.mem_insert_self _ _)
    have hpri:=hprimary i (Finset.mem_insert_self _ _)
    have hps:∀j∈s,Prime (p j):=fun j hj=>hp j (Finset.mem_insert_of_mem hj)
    have hprs:∀j∈s,lambda^2∣p j-1:=fun j hj=>hprimary j (Finset.mem_insert_of_mem hj)
    have hcpi:IsCoprime (p i) (∏j∈s,p j):=IsCoprime.prod_right (fun j hj=>
      hpair i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) (by intro he;subst j;exact hi hj))
    have hpb:¬p i∣h*(∏j∈s,p j):=by
      intro hd
      rcases hpi.dvd_mul.mp hd with hd|hd
      · exact hph i (Finset.mem_insert_self _ _) hd
      · exact hpi.not_isUnit (hcpi.isUnit_of_dvd hd)
    rw [Finset.prod_insert hi,show h*(p i*(∏j∈s,p j))=(h*(∏j∈s,p j))*p i by ring,
      unramifiedResidualCoefficient_prime_norm (p i) hpi hpri _ hpb]
    exact ih hps hprs (fun j hj k hk hjk=>hpair j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk)
      (fun j hj=>hph j (Finset.mem_insert_of_mem hj))

theorem unramifiedResidualCoefficient_squarefree_cube_norm (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) (hsq:Squarefree I)
    (u:Eisˣ) (m:ℕ) :
    ‖unramifiedResidualCoefficient ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖=
      ‖eisEmbedding (primaryGenerator J)‖*‖unramifiedResidualCoefficient (u.val*lambda^m)‖ := by
  rw [unramifiedResidualCoefficient_primary_cube _ hJ (primaryGenerator_spec J hJ).2,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  congr 1
  rw [primaryGenerator_squarefree_support I hI hsq]
  apply unramifiedResidualCoefficient_prime_product_norm
  · exact fun P hP=>primaryPrime_isPrime_of_mem I P hI hP
  · exact fun P hP=>(primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))).2.2.2
  · exact primaryPrime_support_coprime I hI
  · intro P hP hd
    have hp:=primaryPrime_isPrime_of_mem I P hI hP
    have hpp:lambda^2∣primaryPrime P-1:=
      (primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))).2.2.2
    have hc:IsCoprime (u.val*lambda^m) (primaryPrime P):=
      (ramified_primary_coprime u m _ hpp).of_mul_left_right
    exact hp.not_isUnit (hc.symm.isUnit_of_dvd hd)

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def threeRamifiedUnit :Eisˣ:=-(ramifiedOmegaUnit^2)
def traceRamifiedUnit :Eisˣ:=-ramifiedOmegaUnit

lemma three_eq_ramifiedUnit : (3:Eis)=(threeRamifiedUnit:Eis)*lambda^2 := by
  have hw:omega^2=-omega-1:=by linear_combination ramified_omega_relation
  have hl:lambda^2=-3*omega:=by
    change (omega-1)^2=-3*omega
    linear_combination hw
  simp only [threeRamifiedUnit,Units.val_neg,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val,hl]
  calc
    (3:Eis)=3*omega^3:=by rw [omega_primitive.pow_eq_one]; ring
    _=_:=by ring

lemma trace_eq_ramifiedUnit : ramifiedTraceLambda=(traceRamifiedUnit:Eis)*lambda := by
  have hw:=ramified_omega_relation
  simp only [traceRamifiedUnit,Units.val_neg,ramifiedOmegaUnit_val]
  change 1+2*omega=-omega*(omega-1)
  linear_combination hw

def ramifiedSixUnit (side:Bool) :RamifiedSixBranch→Eisˣ
  | .inl _=>threeRamifiedUnit*ramifiedCuspRoot side
  | .inr (.inl _)=>threeRamifiedUnit*(-ramifiedCuspRoot side)⁻¹^4*(-ramifiedCuspRoot side)
  | .inr (.inr (.inl _))=>threeRamifiedUnit*(-ramifiedCuspRoot side)⁻¹^4
  | .inr (.inr (.inr j))=>threeRamifiedUnit*(-ramifiedCuspRoot side)⁻¹^4*
      ramifiedCuspScaleUnit side*traceRamifiedUnit*ramifiedOmegaUnit^j.val

def ramifiedSixPower :RamifiedSixBranch→ℕ
  | .inl _=>2
  | .inr (.inl _)=>2
  | .inr (.inr (.inl _))=>2
  | .inr (.inr (.inr _))=>3

lemma ramifiedSixPower_bounds (i:RamifiedSixBranch) : 2≤ramifiedSixPower i ∧ ramifiedSixPower i≤3 := by
  rcases i with i|i
  · norm_num [ramifiedSixPower]
  rcases i with i|i
  · norm_num [ramifiedSixPower]
  rcases i with i|i <;> norm_num [ramifiedSixPower]

lemma unitCuspUnramifiedIndex_multiplier (u t:Eisˣ) (h:Eis) :
    unitCuspUnramifiedIndex u t h=(3*(↑u⁻¹:Eis)^4*(t:Eis))*h := by
  unfold unitCuspUnramifiedIndex
  have ht:(t:Eis)*(↑t⁻¹:Eis)=1:=by simp
  calc
    _=(3*(↑u⁻¹:Eis)^4*(t:Eis)*h)*((t:Eis)*(↑t⁻¹:Eis)):=by ring
    _=_:=by rw [ht,mul_one]

theorem ramifiedSixIndex_multiplier (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side)) (i:RamifiedSixBranch) :
    ramifiedSixIndex side h hf i=
      ((ramifiedSixUnit side i:Eis)*lambda^(ramifiedSixPower i))*h := by
  rcases i with i|i
  · simp only [ramifiedSixIndex,unitCuspUnramifiedIndex_multiplier,
      ramifiedSixUnit,ramifiedSixPower,Units.val_mul,Units.val_one,inv_one,one_pow]
    rw [three_eq_ramifiedUnit]
    ring
  rcases i with i|i
  · simp only [ramifiedSixIndex,unitCuspUnramifiedIndex_multiplier,
      ramifiedSixUnit,ramifiedSixPower,Units.val_mul,Units.val_pow_eq_pow_val]
    rw [three_eq_ramifiedUnit]
    ring
  rcases i with i|j
  · simp only [ramifiedSixIndex,unitCuspUnramifiedIndex_multiplier,
      ramifiedSixUnit,ramifiedSixPower,Units.val_mul,Units.val_pow_eq_pow_val,Units.val_one,mul_one]
    rw [three_eq_ramifiedUnit]
    ring
  · have hh:=onceCuspFrequencyQuotient_spec (ramifiedCuspScaleUnit side) h hf j
    change 3*((↑(-ramifiedCuspRoot side)⁻¹:Eis)^2*
      (onceCuspScale (ramifiedCuspScaleUnit side)*omega^j.val))^2*
      onceCuspFrequencyQuotient (ramifiedCuspScaleUnit side) h hf j=_
    calc
      _=3*(↑(-ramifiedCuspRoot side)⁻¹:Eis)^4*
          (onceCuspScale (ramifiedCuspScaleUnit side)*omega^j.val)*h:=by
        conv_rhs => rw [hh]
        ring
      _=_:=by
        simp only [ramifiedSixUnit,ramifiedSixPower,Units.val_mul,Units.val_pow_eq_pow_val,
          ramifiedOmegaUnit_val,onceCuspScale]
        rw [three_eq_ramifiedUnit,trace_eq_ramifiedUnit]
        ring

theorem ramifiedBesselValue_prime_power_vanish (side:Bool) (p:Eis) (hp:Prime p)
    (hpp:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (k:ℕ) (hk:k%3=2) :
    ramifiedBesselValue side (h*p^k)=0 := by
  unfold ramifiedBesselValue
  split_ifs with hf
  · have hr:ramifiedArithmeticResidue side (h*p^k) hf=0:=by
      unfold ramifiedArithmeticResidue
      apply Finset.sum_eq_zero
      intro i hi
      rw [ramifiedSixIndex_multiplier]
      have hc:IsCoprime ((ramifiedSixUnit side i:Eis)*lambda^(ramifiedSixPower i)) p:=
        (ramified_primary_coprime (ramifiedSixUnit side i) (ramifiedSixPower i) p hpp).of_mul_left_right
      have hnot:¬p∣((ramifiedSixUnit side i:Eis)*lambda^(ramifiedSixPower i))*h:=by
        intro hd
        rcases hp.dvd_mul.mp hd with hd|hd
        · exact hp.not_isUnit (hc.symm.isUnit_of_dvd hd)
        · exact hph hd
      rw [←mul_assoc,unramifiedGaussResidue_prime_power_table p hp hpp _ hnot,hk]
      norm_num
    rw [hr,mul_zero,zero_div]
  · rfl

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma ramified_norm_third (u:Eisˣ) (m:ℕ) :
    ‖eisEmbedding (u.val*lambda^m)‖^(1/3:ℝ)=(3:ℝ)^((m:ℝ)/6) := by
  have hs:‖eisEmbedding (u.val*lambda^m)‖^2=(3:ℝ)^m:=by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,ramifiedElement_absNorm,Nat.cast_pow,Nat.cast_ofNat]
  calc
    _=(‖eisEmbedding (u.val*lambda^m)‖^2)^(1/6:ℝ):=by
      rw [←Real.rpow_natCast_mul (norm_nonneg _)]
      congr 1
      norm_num
    _=((3:ℝ)^m)^(1/6:ℝ):=by rw [hs]
    _=(3:ℝ)^((m:ℝ)/6):=by
      rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤3)]
      congr 1
      ring

lemma cubicBesselNormalizer_ramified_mul_norm (h:Eis) (u:Eisˣ) (m:ℕ) :
    ‖cubicBesselNormalizer (h*(u.val*lambda^m))‖=
      ‖cubicBesselNormalizer h‖*(3:ℝ)^((m:ℝ)/6) := by
  have hp:0<‖eisEmbedding (u.val*lambda^m)‖:=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (ramifiedElement_ne_zero u m))
  rw [cubicBesselNormalizer_mul,norm_mul]
  have he:=Complex.norm_cpow_eq_rpow_re_of_pos hp (1/3:ℂ)
  have hre:(1/3:ℂ).re=(1/3:ℝ):=by norm_num
  rw [hre,ramified_norm_third] at he
  rw [he]
  ring

def unramifiedCoefficientBaseBound :ℝ:=
  ‖cubicBesselNormalizer 1‖*ramifiedResidueFamilyMass 1

lemma unramifiedCoefficientBaseBound_nonneg :0≤unramifiedCoefficientBaseBound:=
  mul_nonneg (norm_nonneg _) (ramifiedResidueFamilyMass_nonneg _)

lemma unramifiedResidualCoefficient_ramified_bound (u:Eisˣ) (m:ℕ) :
    ‖unramifiedResidualCoefficient (u.val*lambda^m)‖≤
      unramifiedCoefficientBaseBound*(3:ℝ)^((m:ℝ)/6) := by
  have hc:‖cubicBesselNormalizer (u.val*lambda^m)‖=
      ‖cubicBesselNormalizer 1‖*(3:ℝ)^((m:ℝ)/6):=by
    simpa only [one_mul] using cubicBesselNormalizer_ramified_mul_norm 1 u m
  rw [unramifiedResidualCoefficient,norm_mul,hc,unramifiedCoefficientBaseBound]
  have he:=mul_le_mul_of_nonneg_left (unramifiedGaussResidue_unit_lambda_norm_le u m)
    (mul_nonneg (norm_nonneg (cubicBesselNormalizer 1)) (Real.rpow_nonneg (show (0:ℝ)≤3 by norm_num) ((m:ℝ)/6)))
  exact he.trans_eq (by ring)

theorem unramifiedResidualCoefficient_squarefree_cube_bound (I J:Ideal Eis)
    (hI:CompletedGauss.primaryGenerator I≠0) (hJ:CompletedGauss.primaryGenerator J≠0) (hsq:Squarefree I)
    (u:Eisˣ) (m:ℕ) :
    ‖unramifiedResidualCoefficient ((u.val*lambda^m)*CompletedGauss.primaryGenerator I*
      (CompletedGauss.primaryGenerator J)^3)‖≤
      unramifiedCoefficientBaseBound*(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (CompletedGauss.primaryGenerator J)‖ := by
  rw [unramifiedResidualCoefficient_squarefree_cube_norm I J hI hJ hsq u m]
  exact (mul_le_mul_of_nonneg_left (unramifiedResidualCoefficient_ramified_bound u m)
    (norm_nonneg _)).trans_eq (by ring)

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedSixWeight_norm_le_one (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side)) (i:RamifiedSixBranch) :
    ‖ramifiedSixWeight side h hf i (4/3)‖≤1 := by
  rcases i with i|i
  · norm_num [ramifiedSixWeight,norm_mul,breveE_norm]
  rcases i with i|i
  · norm_num [ramifiedSixWeight,norm_mul,breveE_norm]
  rcases i with i|i
  · norm_num [ramifiedSixWeight,norm_mul,breveE_norm]
  · unfold ramifiedSixWeight
    dsimp only
    split_ifs
    · simp only [norm_mul,breveE_norm,mul_one]
      norm_num only [norm_inv,norm_div,norm_one,Complex.norm_ofNat]
      have hw:=ramifiedWeight_norm_scalar 1
      norm_num only [pow_one,Nat.cast_ofNat] at hw
      have hb:=ramifiedDecayRatio_lt_one.le
      nlinarith [norm_nonneg ((3:ℂ)^(-(4/3:ℂ)))]
    · simp

lemma ramifiedSixIndex_squarefree_cube (side:Bool) (u:Eisˣ) (m:ℕ) (n b:Eis)
    (hf:(3:Eis)∣((u.val*lambda^m)*n*b^3)-onceCuspScale (ramifiedCuspScaleUnit side))
    (i:RamifiedSixBranch) :
    ramifiedSixIndex side ((u.val*lambda^m)*n*b^3) hf i=
      (((ramifiedSixUnit side i*u:Eisˣ):Eis)*lambda^(ramifiedSixPower i+m))*n*b^3 := by
  rw [ramifiedSixIndex_multiplier,Units.val_mul,pow_add]
  ring

lemma ramifiedSix_normalized_term_bound (side:Bool) (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) (hsq:Squarefree I)
    (u:Eisˣ) (m:ℕ)
    (hf:(3:Eis)∣((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)-
      onceCuspScale (ramifiedCuspScaleUnit side)) (i:RamifiedSixBranch) :
    ‖cubicBesselNormalizer ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)*
      unramifiedGaussResidue (ramifiedSixIndex side
        ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3) hf i)‖≤
      (unramifiedCoefficientBaseBound*(3:ℝ)^(1/2:ℝ))*(3:ℝ)^((m:ℝ)/6)*
        ‖eisEmbedding (primaryGenerator J)‖ := by
  let h:=(u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3
  let idx:=ramifiedSixIndex side h hf i
  have hc:‖cubicBesselNormalizer idx‖=
      ‖cubicBesselNormalizer h‖*(3:ℝ)^((ramifiedSixPower i:ℝ)/6):=by
    dsimp only [idx]
    rw [ramifiedSixIndex_multiplier,mul_comm]
    exact cubicBesselNormalizer_ramified_mul_norm h (ramifiedSixUnit side i) (ramifiedSixPower i)
  have hp:1≤(3:ℝ)^((ramifiedSixPower i:ℝ)/6):=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hcle:‖cubicBesselNormalizer h‖≤‖cubicBesselNormalizer idx‖:=by
    rw [hc]
    exact le_mul_of_one_le_right (norm_nonneg _) hp
  have hnorm:‖unramifiedResidualCoefficient idx‖≤
      unramifiedCoefficientBaseBound*(3:ℝ)^(((ramifiedSixPower i+m:ℕ):ℝ)/6)*
        ‖eisEmbedding (primaryGenerator J)‖:=by
    dsimp only [idx,h]
    rw [ramifiedSixIndex_squarefree_cube]
    exact unramifiedResidualCoefficient_squarefree_cube_bound I J hI hJ hsq
      (ramifiedSixUnit side i*u) (ramifiedSixPower i+m)
  have hexp:((ramifiedSixPower i+m:ℕ):ℝ)/6≤(m:ℝ)/6+1/2:=by
    have hr:(ramifiedSixPower i:ℝ)≤3:=by exact_mod_cast (ramifiedSixPower_bounds i).2
    push_cast
    linarith
  have hpow:(3:ℝ)^(((ramifiedSixPower i+m:ℕ):ℝ)/6)≤
      (3:ℝ)^((m:ℝ)/6)*(3:ℝ)^(1/2:ℝ):=by
    rw [←Real.rpow_add (by norm_num : (0:ℝ)<3)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  calc
    _≤‖unramifiedResidualCoefficient idx‖:=by
      rw [unramifiedResidualCoefficient,norm_mul,norm_mul]
      exact mul_le_mul_of_nonneg_right hcle (norm_nonneg _)
    _≤unramifiedCoefficientBaseBound*(3:ℝ)^(((ramifiedSixPower i+m:ℕ):ℝ)/6)*
        ‖eisEmbedding (primaryGenerator J)‖:=hnorm
    _≤unramifiedCoefficientBaseBound*((3:ℝ)^((m:ℝ)/6)*(3:ℝ)^(1/2:ℝ))*
        ‖eisEmbedding (primaryGenerator J)‖:=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow unramifiedCoefficientBaseBound_nonneg)
        (norm_nonneg _)
    _=_:=by ring

theorem ramifiedBesselValue_squarefree_cube_bound :
    ∃C:ℝ,0<C ∧ ∀(side:Bool) (I J:Ideal Eis),
      primaryGenerator I≠0→primaryGenerator J≠0→Squarefree I→∀(u:Eisˣ) (m:ℕ),
      ‖ramifiedBesselValue side ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖≤
        C*(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖ := by
  let V:ℂ:=((9*Real.sqrt 3/2:ℝ):ℂ)
  let A:ℝ:=‖(3:ℂ)^(2/3:ℂ)‖*‖V⁻¹‖
  let B:ℝ:=unramifiedCoefficientBaseBound*(3:ℝ)^(1/2:ℝ)
  have hA:0≤A:=mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hB:0≤B:=mul_nonneg unramifiedCoefficientBaseBound_nonneg (Real.rpow_nonneg (by norm_num) _)
  refine ⟨1+6*A*B,by positivity,?_⟩
  intro side I J hI hJ hsq u m
  let h:=(u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3
  let D:ℝ:=B*(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖
  have hD:0≤D:=by dsimp only [D]; positivity
  unfold ramifiedBesselValue
  split_ifs with hf
  · have hs:‖cubicBesselNormalizer h*ramifiedArithmeticResidue side h hf‖≤6*D:=by
      have he:cubicBesselNormalizer h*ramifiedArithmeticResidue side h hf=
          ∑i:RamifiedSixBranch,ramifiedSixWeight side h hf i (4/3)*
            (cubicBesselNormalizer h*unramifiedGaussResidue (ramifiedSixIndex side h hf i)):=by
        rw [ramifiedArithmeticResidue,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [he]
      calc
        _≤∑i:RamifiedSixBranch,‖ramifiedSixWeight side h hf i (4/3)*
            (cubicBesselNormalizer h*unramifiedGaussResidue (ramifiedSixIndex side h hf i))‖:=norm_sum_le _ _
        _≤∑i:RamifiedSixBranch,D:=by
          apply Finset.sum_le_sum
          intro i hi
          rw [norm_mul]
          exact (mul_le_mul_of_nonneg_right (ramifiedSixWeight_norm_le_one side h hf i) (norm_nonneg _)).trans
            (by simpa only [one_mul,D,B,h] using ramifiedSix_normalized_term_bound side I J hI hJ hsq u m hf i)
        _=6*D:=by simp [RamifiedSixBranch]
    have he:‖(3:ℂ)^(2/3:ℂ)*cubicBesselNormalizer h*ramifiedArithmeticResidue side h hf/V‖≤A*(6*D):=by
      rw [div_eq_mul_inv,mul_assoc ((3:ℂ)^(2/3:ℂ)),norm_mul,norm_mul]
      dsimp only [A]
      nlinarith [mul_le_mul_of_nonneg_left hs (norm_nonneg ((3:ℂ)^(2/3:ℂ))),norm_nonneg (V⁻¹)]
    refine he.trans ?_
    dsimp only [A,B,D]
    have hnonneg:0≤(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖:=by positivity
    nlinarith
  · rw [norm_zero]
    positivity

end CubicEisenstein

end

end OAI
