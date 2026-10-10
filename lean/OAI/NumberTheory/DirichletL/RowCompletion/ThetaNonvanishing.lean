import OAI.NumberTheory.DirichletL.Hecke.MobiusEulerCorrection

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

open scoped BigOperators Classical ContDiff Topology
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open ShortDraftHeckeBridge
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open SixthPowerAverage CompactMellinBridge InitialMeanSquare

theorem corrected_weighted_mellin_identity {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (hS : ∀P∈S,Prime P) (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : ∀x,x≤1 ∨ 2≤x→W x=0) (s : ℂ) (hRe : 2<s.re) :
    (χ.LFunction s*(baseChangeChar χ).LFunction s)*
      ((finiteEulerFactor χ S s*SmoothMobiusCorrection.eulerCorrection χ S s)*
        mellin (fun Z : ℝ=>weightedCompactSum χ S W Z⁻¹) (-s))=
      mellin W s := by
  rw [weightedCompactMellin_eq_series χ S W hW hs s hRe]
  have hc:=SmoothMobiusCorrection.full_LSeries_correction χ S hS s hRe
  have hp:=normFiber_LSeries_eq_pair_inverse χ (baseChangeChar χ) (baseChangeWeight χ)
    (normFiberCoeff_baseChange_eq_pairInverseCoeff χ) s
  have he:=pair_inverse_euler_identity χ (baseChangeChar χ) s (by linarith : 1<s.re)
  rw [←hp,hc] at he
  calc
    _=((χ.LFunction s*(baseChangeChar χ).LFunction s)*
      ((finiteEulerFactor χ S s*SmoothMobiusCorrection.eulerCorrection χ S s)*
        LSeries (weightedCoeff χ S) s))*mellin W s := by ring
    _=mellin W s := by rw [he,one_mul]

theorem dirichlet_open_strip_of_theta_models {q₀ : ℕ} [NeZero q₀]
    (χ : DirichletCharacter ℂ q₀)
    (S : Finset (Ideal ActualEisensteinCubic.O))
    (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound)
    (z : ℂ) (hz : (23:ℝ)/24<z.re) (hz1 : z.re<1) : χ.LFunction z≠0 := by
  let W : ℝ→ℂ:=ConcreteCompactWeight.weight z
  have hW : ContDiff ℝ ∞ W:=ConcreteCompactWeight.weight_smooth z
  have hWs : ∀x,x≤1 ∨ 2≤x→W x=0:=ConcreteCompactWeight.weight_support z
  have hM:=weightedCompactMellin_analytic χ S hbad hSp ρ q levelBound hρ hq hlevel hmodels W hW hWs
  have hE:=finiteEulerFactor_analytic χ S hSp ((23:ℝ)/24)
  have hH : AnalyticOnNhd ℂ (SmoothMobiusCorrection.eulerCorrection χ S)
      {s : ℂ | (23:ℝ)/24<s.re} :=
    (SmoothMobiusCorrection.eulerCorrection_analytic χ S).mono (by intro s hs;change 0<s.re;change (23:ℝ)/24<s.re at hs;linarith)
  have hWanalytic:=compact_weight_mellin_analytic W hW hWs ((23:ℝ)/24)
  have hnotboth : χ≠1 ∨ baseChangeChar χ≠1 := by
    by_cases hc : χ=1
    · exact Or.inr (baseChangeChar_ne_one_of_one χ hc)
    · exact Or.inl hc
  have hzneq : z≠1 := by intro he;subst z;norm_num at hz1
  exact (pair_zero_free_of_identity_gt_two χ (baseChangeChar χ) hnotboth
    ((23:ℝ)/24) (by norm_num)
    (fun s=>(finiteEulerFactor χ S s*SmoothMobiusCorrection.eulerCorrection χ S s)*
      mellin (fun Z : ℝ=>weightedCompactSum χ S W Z⁻¹) (-s))
    (mellin W) ((hE.mul hH).mul hM) hWanalytic
    (corrected_weighted_mellin_identity χ S hSp W hW hWs)
    z hz hzneq (ConcreteCompactWeight.weight_mellin_ne_zero z)).1

theorem dirichlet_nonvanishing_of_theta_models {q₀ : ℕ} [NeZero q₀]
    (χ : DirichletCharacter ℂ q₀)
    (S : Finset (Ideal ActualEisensteinCubic.O))
    (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound)
    (z : ℂ) (hz : (23:ℝ)/24<z.re) (hpole : ¬(χ=1 ∧ z=1)) : χ.LFunction z≠0 := by
  by_cases hz1 : z.re<1
  · exact dirichlet_open_strip_of_theta_models χ S hbad hSp ρ q levelBound hρ hq hlevel hmodels z hz hz1
  · exact ShortDraft.dirichlet_target_of_one_le_re q₀ χ z (le_of_not_gt hz1) hpole

theorem dirichletTarget_of_theta_models
    (hmodels : ∀(q₀ : ℕ) [NeZero q₀] (χ : DirichletCharacter ℂ q₀),
      ∃S : Finset (Ideal ActualEisensteinCubic.O),fixedBadPrimes⊆S ∧ (∀P∈S,Prime P) ∧
      ∃ρ q levelBound : ℝ,0<ρ ∧ 1<q ∧ 1≤levelBound ∧
        HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound) :
    ShortDraft.DirichletTarget := by
  intro q₀ _ χ z hz hpole
  obtain ⟨S,hbad,hSp,ρ,q,level,hρ,hq,hl,hm⟩:=hmodels q₀ χ
  exact dirichlet_nonvanishing_of_theta_models χ S hbad hSp ρ q level hρ hq hl hm z hz hpole

end CanonicalRowCompletion

open scoped BigOperators Classical
namespace QuadraticAllOddCRT

section
open ActualEisensteinCubic
open QuadraticGaussRay hiding O
open ActualEisensteinCoordinates hiding O omega
open CanonicalQuadraticSieve hiding O

local instance : (Ideal.span {lambda} : Ideal ActualEisensteinCubic.O).IsMaximal:=lambdaIdeal_maximal

lemma lambda_odd : ringChar (ActualEisensteinCubic.O⧸Ideal.span {lambda})≠2:=
  ActualEisensteinSieve.lambda_residue_odd

lemma lambda_residue : residue lambda=((3:ZMod 4),(1:ZMod 4)) := by
  have h : lambda=eval (-1) 1 := by
    change (ActualEisensteinCubic.omega-1:ActualEisensteinCubic.O)=((-1:ℤ):ActualEisensteinCubic.O)+((1:ℤ):ActualEisensteinCubic.O)*ActualEisensteinCubic.omega
    push_cast
    ring
  rw [h,residue_eval]
  decide

lemma lambda_quadratic_ray_ne_zero : quadraticRayValue (residue lambda)≠0 := by
  apply quadraticRayValue_ne_zero_of_odd
  rw [lambda_residue]
  decide

lemma character_lambda_primary (p : ActualEisensteinCubic.O) (hp : lambda^2∣p-1) :
    character (Ideal.span {lambda}) (Ideal.Quotient.mk (Ideal.span {lambda}) p)=1 := by
  have hm : Ideal.Quotient.mk (Ideal.span {lambda}) p=Ideal.Quotient.mk (Ideal.span {lambda}) (1:ActualEisensteinCubic.O) :=
    Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr
      ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans hp))
  rw [hm,map_one,map_one]

def lambdaQuadraticRay (r : EisensteinEPrimaryPhase.Coord) : ℂ:=
  quadraticRayValue (EisensteinEPrimaryPhase.mul (residue lambda) r)/
    (quadraticRayValue (residue lambda)*quadraticRayValue r)

theorem character_lambda_eq_ray (p : ActualEisensteinCubic.O) (hp : p≠0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda∉Ideal.span {p}) (hc : ringChar (ActualEisensteinCubic.O⧸Ideal.span {p})≠2)
    (hprimary : lambda^2∣p-1) :
    character (Ideal.span {p}) (Ideal.Quotient.mk (Ideal.span {p}) lambda)=
      lambdaQuadraticRay (residue p) := by
  have hcop : IsCoprime (Ideal.span {lambda} : Ideal ActualEisensteinCubic.O) (Ideal.span {p}) := by
    apply Ideal.isCoprime_of_isMaximal
    intro he
    apply hg
    rw [←he]
    exact Ideal.subset_span (by simp)
  have h:=quadratic_ray_cross lambda p PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero hp hcop lambda_odd hc
  rw [character_lambda_primary p hprimary,one_mul] at h
  have hodd : EisensteinEPrimaryPhase.odd (residue p) := by
    have hn : ‖quadraticRayValue (residue p)‖=1 := by
      let pp : Unit→ActualEisensteinCubic.O:=fun _=>p
      have hpp : ∀i,pp i≠0:=fun _=>hp
      have hcp : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {pp i})):=by
        intro i j hij
        exact False.elim (hij (Subsingleton.elim _ _))
      have hh:=FiniteGaussPhase.norm_canonicalProductGauss pp hpp hcp (fun _=>hg) (fun _=>hc)
        (fun _=>3) (by intro i;decide) (by intro i;decide)
      rw [QuadraticGaussRay.canonicalProductGauss_three_eq_rayValue pp hpp hcp (fun _=>hg) (fun _=>hc)] at hh
      simpa [pp] using hh
    exact QuadraticUnitInvariance.odd_of_quadraticRayValue_norm_eq_one _ hn
  unfold lambdaQuadraticRay
  rw [←residue_mul]
  apply (eq_div_iff (mul_ne_zero lambda_quadratic_ray_ne_zero (quadraticRayValue_ne_zero_of_odd _ hodd))).mpr
  simpa only [mul_assoc] using h.symm

end

open ActualEisensteinCubic
open QuadraticGaussRay hiding O
open ActualEisensteinCoordinates hiding O omega

def lambdaQuadraticTable (r : EisensteinEPrimaryPhase.Coord) : ℤ :=
  if ¬EisensteinEPrimaryPhase.odd r then 0
  else if r∈({(0,1),(1,0),(1,2),(1,3),(2,3),(3,3)} : Finset EisensteinEPrimaryPhase.Coord)
    then 1 else -1

lemma lambdaQuadraticTable_mul (r s : EisensteinEPrimaryPhase.Coord) :
    lambdaQuadraticTable (EisensteinEPrimaryPhase.mul r s)=
      lambdaQuadraticTable r*lambdaQuadraticTable s := by
  have h : ∀r s : EisensteinEPrimaryPhase.Coord,
      lambdaQuadraticTable (EisensteinEPrimaryPhase.mul r s)=
        lambdaQuadraticTable r*lambdaQuadraticTable s := by decide
  exact h r s

lemma lambdaQuadraticTable_eq_ray (r : EisensteinEPrimaryPhase.Coord)
    (hr : EisensteinEPrimaryPhase.odd r) :
    (lambdaQuadraticTable r:ℂ)=lambdaQuadraticRay r := by
  have hcmp (a b : ZMod 4) : (a=b) ↔ (a.val=b.val) :=
    (ZMod.val_injective 4).eq_iff.symm
  have hn3 : (-3 : ZMod 4) = 1 := by decide
  rcases r with ⟨a,b⟩
  have hcases : ∀ x : ZMod 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide
  rcases hcases a with rfl | rfl | rfl | rfl <;>
    rcases hcases b with rfl | rfl | rfl | rfl <;>
    norm_num [EisensteinEPrimaryPhase.odd,ZMod.val_zero,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] at hr <;>
    norm_num [lambdaQuadraticTable,lambdaQuadraticRay,lambda_residue,EisensteinEPrimaryPhase.mul,
      EisensteinEPrimaryPhase.odd,quadraticRayValue,breveGaussianFourTerms_formula,
      Prod.mk.injEq,hcmp,hn3,ZMod.val_zero,ZMod.val_one_eq_one_mod,ZMod.val_ofNat,
      ZMod.val_neg_one,ZMod.val_mul,ZMod.val_add,ZMod.val_sub,
      Complex.I_sq,Complex.I_pow_three,Complex.inv_I,zpow_neg] <;>
    ring_nf <;> norm_num [Complex.I_sq,Complex.I_pow_three]
  all_goals
    field_simp [Complex.I_ne_zero]
    change (-2 : ℂ) = Complex.I * (Complex.I ^ (1 : ℤ) + Complex.I ^ (2 - 1 : ℤ))
    norm_num [Complex.I_sq]
    ring_nf
    norm_num [Complex.I_sq]

def lambdaQuadraticCharacter : ActualEisensteinCubic.O→*ℂ where
  toFun n:=(lambdaQuadraticTable (residue n):ℂ)
  map_one' := by
    have h : residue (1:ActualEisensteinCubic.O)=((1:ZMod 4),0):=by
      have h1 : (1:ActualEisensteinCubic.O)=eval 1 0:=by simp [eval]
      rw [h1,residue_eval]
      norm_num
    rw [h]
    exact_mod_cast (show lambdaQuadraticTable ((1:ZMod 4),0)=1 from by decide)
  map_mul' x y := by
    rw [residue_mul,lambdaQuadraticTable_mul]
    push_cast
    rfl

lemma lambdaQuadraticCharacter_periodic (x y : ActualEisensteinCubic.O) (h : (4:ActualEisensteinCubic.O)∣x-y) :
    lambdaQuadraticCharacter x=lambdaQuadraticCharacter y := by
  change (lambdaQuadraticTable (residue x):ℂ)=(lambdaQuadraticTable (residue y):ℂ)
  rw [QuadraticGaussRay.residue_eq_of_four_dvd_sub x y h]

end QuadraticAllOddCRT

open scoped BigOperators Classical
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open CubicJacobiGlobal hiding O
open QuadraticAllOddCRT
open CanonicalQuadraticSieve hiding O
open ConcreteTraceCRT (eisEmbedding)
open UniqueFactorizationMonoid

lemma localRowValue_square (x : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) :
    localRowValue x P^2=eisEmbedding (primeValue P x) := by
  unfold localRowValue primeValue
  split_ifs with h
  · let : P.IsMaximal:=h.1
    change (actualSextic P h.2 (Ideal.Quotient.mk P x))^2=_
    rw [←MulChar.pow_apply' _ (by decide : (2:ℕ)≠0),canonicalSextic_pow_two]
    rfl
  · simp

theorem idealRowHom_square (x : ActualEisensteinCubic.O) (I : Ideal ActualEisensteinCubic.O) :
    idealRowHom x I^2=eisEmbedding (idealSymbol I x) := by
  have hm (s : Multiset (Ideal ActualEisensteinCubic.O)) :
      (s.map (localRowValue x)).prod^2=eisEmbedding ((s.map (fun P=>primeValue P x)).prod) := by
    induction s using Multiset.induction_on with
    | empty=>simp
    | @cons P s ih=>
      simp only [Multiset.map_cons,Multiset.prod_cons,mul_pow,map_mul,localRowValue_square,ih]
  by_cases hI : I=0
  · subst I
    simp only [map_zero,idealSymbol_zero,zero_pow (by decide : (2:ℕ)≠0)]
  · change (if I=0 then 0 else _)^2=eisEmbedding (if I=0 then 0 else _)
    simp only [ite_eq_right hI]
    exact hm _

lemma actualSextic_cube_quadratic (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] (hg : lambda∉P) :
    actualSextic P hg^3=character P := by
  let : Field (ActualEisensteinCubic.O⧸P):=Ideal.Quotient.field P
  let : Fintype (ActualEisensteinCubic.O⧸P):=Fintype.ofFinite _
  obtain ⟨χ,hχ,hχ3⟩ : ∃χ : MulChar (ActualEisensteinCubic.O⧸P) ActualEisensteinCubic.O,
      actualSextic P hg=χ.ringHomComp eisEmbedding ∧
      χ^3=(quadraticChar (ActualEisensteinCubic.O⧸P)).ringHomComp (Int.castRingHom ActualEisensteinCubic.O) :=
    ⟨_,rfl,(sexticChar_powers P hg).2.1⟩
  rw [hχ,MulChar.ringHomComp_pow,hχ3]
  ext x
  change eisEmbedding ((quadraticChar (ActualEisensteinCubic.O⧸P) x:ℤ):ActualEisensteinCubic.O)=((quadraticChar (ActualEisensteinCubic.O⧸P) x:ℤ):ℂ)
  simp

lemma idealRowHom_lambda_prime_cube (p : ActualEisensteinCubic.O) (hp : Prime p)
    (hprimary : lambda^2∣p-1) (hs : Supported (Ideal.span {p})) :
    idealRowHom lambda (Ideal.span {p})^3=lambdaQuadraticCharacter p := by
  let : (Ideal.span {p}).IsMaximal:=PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hmem : Ideal.span {p}∈normalizedFactors (Ideal.span {p}) :=
    (Ideal.mem_normalizedFactors_iff hs.1).mpr ⟨inferInstance,le_rfl⟩
  obtain ⟨hg,hc⟩:=hs.2 _ hmem
  rw [idealRowHom_prime lambda _ hg]
  change (actualSextic _ hg (Ideal.Quotient.mk _ lambda))^3=_
  rw [←MulChar.pow_apply' _ (by decide : (3:ℕ)≠0),actualSextic_cube_quadratic]
  have he:=character_lambda_eq_ray p hp.ne_zero hg hc hprimary
  have ho:=ActualEisensteinCoordinates.odd_residue_iff_not_two_dvd p
  have hs' := (supported_span_iff p).mp hs
  change character _ (Ideal.Quotient.mk _ lambda)=_
  rw [he]
  exact (lambdaQuadraticTable_eq_ray _ (ho.mpr hs'.2)).symm

theorem idealRowHom_lambda_cube (y : ActualEisensteinCubic.O) (hy : lambda^2∣y-1)
    (hs : Supported (Ideal.span {y})) :
    idealRowHom lambda (Ideal.span {y})^3=lambdaQuadraticCharacter y := by
  have hy0 : y≠0:=by
    intro he
    apply hs.1
    simp [he]
  obtain ⟨s,hprod,hfactors⟩:=exists_primary_prime_factorization y hy0 hy
  rw [←hprod] at hs ⊢
  clear hprod hy hy0 y
  induction s using Multiset.induction_on with
  | empty=>
    simp only [Multiset.prod_zero,Ideal.span_singleton_one,←Ideal.one_eq_top,map_one,one_pow]
  | @cons p s ih=>
    have hp:=hfactors p (Multiset.mem_cons_self _ _)
    have htail : ∀q∈s,Prime q ∧ lambda^2∣q-1:=
      fun q hq=>hfactors q (Multiset.mem_cons_of_mem hq)
    have hsplit : Supported (Ideal.span {p}) ∧ Supported (Ideal.span {s.prod}) := by
      simpa only [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,supported_mul_iff] using hs
    rw [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,map_mul,mul_pow,
      idealRowHom_lambda_prime_cube p hp.1 hp.2 hsplit.1,ih hsplit.2 htail,map_mul]

theorem idealRowHom_lambda_formula (y : ActualEisensteinCubic.O) (hy : lambda^2∣y-1)
    (hs : Supported (Ideal.span {y})) :
    idealRowHom lambda (Ideal.span {y})=
      eisEmbedding (CubicRamified.linearRay 1 0 y)^2*lambdaQuadraticCharacter y := by
  have htwo:=idealRowHom_square lambda (Ideal.span {y})
  change idealRowHom lambda (Ideal.span {y})^2=eisEmbedding (symbol lambda y) at htwo
  rw [CubicRamified.symbol_lambda_eq_linearRay y hy] at htwo
  have hthree:=idealRowHom_lambda_cube y hy hs
  have hq : lambdaQuadraticCharacter y^2=1 := by
    change (lambdaQuadraticTable (ActualEisensteinCoordinates.residue y):ℂ)^2=1
    have ho := ActualEisensteinCoordinates.odd_residue_iff_not_two_dvd y |>.mpr ((supported_span_iff y).mp hs).2
    unfold lambdaQuadraticTable
    rw [ite_eq_right (not_not.mpr ho)]
    split_ifs <;> norm_num
  have hsix : idealRowHom lambda (Ideal.span {y})^6=1 := by
    calc
      _ = (idealRowHom lambda (Ideal.span {y})^3)^2:=by ring
      _ = 1:=by rw [hthree,hq]
  calc
    _ = (idealRowHom lambda (Ideal.span {y})^2)^2*(idealRowHom lambda (Ideal.span {y})^3):=by
      calc
        _ = idealRowHom lambda (Ideal.span {y})*idealRowHom lambda (Ideal.span {y})^6:=by rw [hsix,mul_one]
        _ = _:=by ring
    _ = _:=by rw [htwo,hthree]

theorem idealRowHom_lambda_mod_thirty_six (x y : ActualEisensteinCubic.O)
    (hx : lambda^2∣x-1) (hy : lambda^2∣y-1)
    (hsx : Supported (Ideal.span {x})) (hsy : Supported (Ideal.span {y}))
    (hxy : (36:ActualEisensteinCubic.O)∣x-y) :
    idealRowHom lambda (Ideal.span {x})=idealRowHom lambda (Ideal.span {y}) := by
  rw [idealRowHom_lambda_formula x hx hsx,idealRowHom_lambda_formula y hy hsy,
    CubicRamified.linearRay_congr_mod_nine 1 0 x y hx hy ((show (9:ActualEisensteinCubic.O)∣36 from ⟨4,by norm_num⟩).trans hxy),
    lambdaQuadraticCharacter_periodic x y ((show (4:ActualEisensteinCubic.O)∣36 from ⟨9,by norm_num⟩).trans hxy)]

end CanonicalRowCompletion

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma cuspRemainder_absolute_chart (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) (M : SL(2,ActualEisensteinCubic.O)) (z : ℂ) (hz : ‖z‖≤1)
    (v : ℝ) (hv : 1/2≤v) (hv0 : 0<v) :
    Summable (fun r : CuspCosets => ‖cuspRemainderProfile a b s
      (cosetHeight r (integralComplexMatrix M • upperPoint z v hv0))‖) ∧
    (∑'r : CuspCosets,‖cuspRemainderProfile a b s
      (cosetHeight r (integralComplexMatrix M • upperPoint z v hv0))‖)≤eisensteinRemainderBound b s := by
  let G : ((Fin 2×Fin 2)→ℤ)→ℝ := fun n => (max 5 (2*b))^s.re*‖n‖^(-s.re)
  let f : CuspCosets→(Fin 2×Fin 2)→ℤ := fun r => rowCoordinates (translatedCuspRow M r)
  let R : CuspCosets→ℝ := fun r => ‖cuspRemainderProfile a b s
    (cosetHeight r (integralComplexMatrix M • upperPoint z v hv0))‖
  have hg : Summable G := (summable_integer_four_rpow s.re hs).mul_left _
  have hi : Function.Injective f := rowCoordinates_injective.comp (translatedCuspRow_injective M)
  have hb : ∀r,R r≤G (f r) := by
    intro r
    simpa only [norm_mul,norm_inv,norm_cosetCharacter,inv_one,one_mul] using
      translated_remainder_majorant a b s hab (by linarith) (by linarith) M z hz v hv hv0 r
  have hr : Summable R := (hg.comp_injective hi).of_nonneg_of_le (fun _ => norm_nonneg _) hb
  refine ⟨hr,?_⟩
  have hsum : (∑'r,R r)≤∑'n,G n :=
    Summable.tsum_le_tsum_of_inj f hi (fun _ _ => by dsimp [G]; positivity) hb hr hg
  simpa only [G,tsum_mul_left,eisensteinRemainderBound] using hsum

theorem cuspRemainder_absolute_bound (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) (w : HyperbolicSpace) :
    Summable (fun r : CuspCosets => ‖cuspRemainderProfile a b s (cosetHeight r w)‖) ∧
    (∑'r : CuspCosets,‖cuspRemainderProfile a b s (cosetHeight r w)‖)≤eisensteinRemainderBound b s := by
  obtain ⟨M,z,v,hv,hMw,hz,hfloor⟩ := bianchi_reduction_height_floor w
  have hz1 : ‖z‖≤1 := by
    rw [Complex.normSq_eq_norm_sq] at hz
    nlinarith [norm_nonneg z]
  have hv1 : 1/2≤v := by
    have hh := Real.sq_sqrt (by norm_num : (0:ℝ)≤2/3)
    have hh0 := Real.sqrt_nonneg (2/3 : ℝ)
    nlinarith
  have hw : w=integralComplexMatrix M⁻¹ • upperPoint z v hv := by
    rw [←hMw,map_inv,inv_smul_smul]
  rw [hw]
  exact cuspRemainder_absolute_chart a b ha hab s hs M⁻¹ z hz1 v hv1 hv

lemma cuspRemainder_aux_norm (b : ℝ) (s : ℂ) (v : ℝ) (hv : 0<v) (hvb : v≤b) :
    ‖cuspRemainderProfile (b+1) (b+2) s v‖=v^s.re := by
  rw [cuspRemainderProfile,cuspSeedProfile_zero (b+1) (b+2) s v (by linarith) (by linarith),
    sub_zero,positiveHeightPower_eq_cpow s v hv,Complex.norm_cpow_eq_rpow_re_of_pos hv]

lemma cuspRemainder_row_scaled_deriv_aux_bound (a b : ℝ) (hab : a<b) (s : ℂ)
    (C : ℝ) (hC0 : 0≤C) (hC : ∀v,|v*deriv (cuspTransition a b) v|≤C)
    (u : Fin 2→ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    ‖(p 2:ℂ)*deriv (axisSlice (fun q => cuspRemainderProfile a b s (rowHeight u q)) p j) (p j)‖≤
      (‖s‖+C)*‖cuspRemainderProfile (b+1) (b+2) s (rowHeight u p)‖ := by
  have hh := rowHeight_pos u hu p hp
  by_cases hb : rowHeight u p≤b
  · rw [cuspRemainder_aux_norm b s _ hh hb]
    exact cuspRemainder_row_scaled_deriv_bound a b s C hC u hu p hp j
  · have hd := (rowProfile_axis_derivatives (cuspRemainderProfile a b s)
      (cuspRemainderProfile_contDiffAt a b s) u hu p hp j).1
    rw [hd.deriv,cuspRemainderProfile_deriv_zero a b s _ hab hh (lt_of_not_ge hb)]
    simp only [zero_mul,mul_zero,norm_zero]
    exact mul_nonneg (add_nonneg (norm_nonneg s) hC0) (norm_nonneg _)

end

open Filter
open scoped BigOperators Classical Topology ContDiff

def weightedHeightProfile (F : ℝ→ℂ) (r : CuspCosets) (p : SpatialCoordinates) : ℂ :=
  (cosetCharacter r)⁻¹*F (rowHeight (embeddedRow r) p)

lemma weightedHeightProfile_axis_differentiable (F : ℝ→ℂ)
    (hF : ∀v,0<v→ContDiffAt ℝ ∞ F v) (r : CuspCosets)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    DifferentiableAt ℝ (axisSlice (weightedHeightProfile F r) p j) (p j) :=
  ((rowProfile_axis_derivatives F hF (embeddedRow r) (embeddedRow_ne_zero r) p hp j).1.const_mul _).differentiableAt

lemma heightPoincare_axis_termwise (F : ℝ→ℂ) (hzero : ∀v≤1,F v=0)
    (hF : ∀v,0<v→ContDiffAt ℝ ∞ F v)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    Summable (fun r => deriv (axisSlice (weightedHeightProfile F r) p j) (p j)) ∧
    HasDerivAt (axisSlice (heightPoincareField F) p j)
      (∑'r,deriv (axisSlice (weightedHeightProfile F r) p j) (p j)) (p j) := by
  obtain ⟨U,hU,hpU,S,hrows⟩ := locally_finite_high_rows p hp
  have ht : Tendsto (fun t => Function.update p j t) (𝓝 (p j)) (𝓝 p) := by
    simpa only [ContinuousAt,Function.update_eq_self] using
      ((continuous_axis_update p j).continuousAt (x := p j))
  have hn : ∀ᶠt in 𝓝 (p j),Function.update p j t∈U := ht (hU.mem_nhds hpU)
  have hz (r : CuspCosets) (hr : r∉S) :
      deriv (axisSlice (weightedHeightProfile F r) p j) (p j)=0 := by
    have he : axisSlice (weightedHeightProfile F r) p j=ᶠ[𝓝 (p j)] (fun _ => 0) := by
      filter_upwards [hn] with t ht
      change (cosetCharacter r)⁻¹*F (rowHeight (embeddedRow r) (Function.update p j t))=0
      rw [hzero _ ((hrows _ ht).2 r hr).le,mul_zero]
    exact he.deriv_eq.trans (deriv_const _ _)
  refine ⟨summable_of_ne_finset_zero hz,?_⟩
  rw [tsum_eq_sum hz]
  have hd := HasDerivAt.sum (u := S) (fun r hr =>
    (weightedHeightProfile_axis_differentiable F hF r p hp j).hasDerivAt)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hn] with t ht
  simp only [Finset.sum_apply]
  change (∑'r,weightedHeightProfile F r (Function.update p j t))=
    ∑r∈S,weightedHeightProfile F r (Function.update p j t)
  apply tsum_eq_sum
  intro r hr
  change (cosetCharacter r)⁻¹*F (rowHeight (embeddedRow r) (Function.update p j t))=0
  rw [hzero _ ((hrows _ ht).2 r hr).le,mul_zero]

lemma weightedRemainder_axis_deriv (a b : ℝ) (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j)=
      deriv (axisSlice (smoothSummand s r) p j) (p j)-
        deriv (axisSlice (weightedHeightProfile (cuspSeedProfile a b s) r) p j) (p j) := by
  have hn : ∀ᶠt in 𝓝 (p j),0<(Function.update p j t) 2 := by
    apply ((continuous_apply 2).comp (continuous_axis_update p j)).continuousAt.eventually_const_lt
    simpa only [Function.comp_apply,Function.update_eq_self] using hp
  have he : axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j=ᶠ[𝓝 (p j)]
      (fun t => axisSlice (smoothSummand s r) p j t-
        axisSlice (weightedHeightProfile (cuspSeedProfile a b s) r) p j t) := by
    filter_upwards [hn] with t ht
    simp only [axisSlice,weightedHeightProfile,cuspRemainderProfile,smoothSummand]
    rw [rowSmoothPower_eq_height s _ (embeddedRow_ne_zero r) _ ht,
      positiveHeightPower_eq_cpow s _ (rowHeight_pos _ (embeddedRow_ne_zero r) _ ht)]
    ring
  rw [he.deriv_eq]
  exact deriv_sub (smooth_axis_differentiable s r p hp j)
    (weightedHeightProfile_axis_differentiable _ (cuspSeedProfile_contDiffAt a b s) r p hp j)

def eisensteinRemainderField (a b : ℝ) (s : ℂ) (p : SpatialCoordinates) : ℂ :=
  smoothEisenstein s p-smoothCuspSeedField a b s p

theorem eisensteinRemainder_axis_termwise (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    Summable (fun r => deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j)) ∧
    HasDerivAt (axisSlice (eisensteinRemainderField a b s) p j)
      (∑'r,deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j)) (p j) := by
  have hE := eisenstein_axis_termwise s hs p hp j
  have hS := heightPoincare_axis_termwise (cuspSeedProfile a b s)
    (fun v hv => cuspSeedProfile_zero a b s v hab (hv.trans ha.le))
    (cuspSeedProfile_contDiffAt a b s) p hp j
  have hcoeff : (∑'r,deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j))=
      (∑'r,deriv (axisSlice (smoothSummand s r) p j) (p j))-
        ∑'r,deriv (axisSlice (weightedHeightProfile (cuspSeedProfile a b s) r) p j) (p j) := by
    simp_rw [weightedRemainder_axis_deriv a b s _ p hp j]
    exact hE.1.tsum_sub hS.1
  refine ⟨(hE.1.sub hS.1).congr (fun r => (weightedRemainder_axis_deriv a b s r p hp j).symm),?_⟩
  rw [hcoeff]
  apply (hE.2.2.1.sub hS.2).congr_of_eventuallyEq
  have hn : ∀ᶠt in 𝓝 (p j),0<(Function.update p j t) 2 := by
    apply ((continuous_apply 2).comp (continuous_axis_update p j)).continuousAt.eventually_const_lt
    simpa only [Function.comp_apply,Function.update_eq_self] using hp
  filter_upwards [hn] with t ht
  change smoothEisenstein s _-smoothCuspSeedField a b s _=
    smoothEisenstein s _-heightPoincareField (cuspSeedProfile a b s) _
  rw [smoothCuspSeedField_eq a b s ha hab _ ht]

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold

namespace CubicEisenstein

lemma weightedRemainder_scaled_deriv_bound (a b : ℝ) (hab : a<b) (s : ℂ)
    (C : ℝ) (hC0 : 0≤C) (hC : ∀v,|v*deriv (cuspTransition a b) v|≤C)
    (r : CuspCosets) (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    ‖(p 2:ℂ)*deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j)‖≤
      (‖s‖+C)*‖cuspRemainderProfile (b+1) (b+2) s (rowHeight (embeddedRow r) p)‖ := by
  let g : SpatialCoordinates→ℂ:=fun q => cuspRemainderProfile a b s (rowHeight (embeddedRow r) q)
  have hd := (rowProfile_axis_derivatives (cuspRemainderProfile a b s)
    (cuspRemainderProfile_contDiffAt a b s) (embeddedRow r) (embeddedRow_ne_zero r) p hp j).1
  have hw := hd.const_mul (cosetCharacter r)⁻¹
  have he : deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j)=
      (cosetCharacter r)⁻¹*deriv (axisSlice g p j) (p j) := by
    change deriv (fun t => (cosetCharacter r)⁻¹*axisSlice g p j t) (p j)=_
    rw [hw.deriv,hd.deriv]
  rw [he]
  calc
    ‖(p 2:ℂ)*((cosetCharacter r)⁻¹*deriv (axisSlice g p j) (p j))‖
      = ‖(cosetCharacter r)⁻¹*((p 2:ℂ)*deriv (axisSlice g p j) (p j))‖ := by congr 1; ring
    _ = ‖(p 2:ℂ)*deriv (axisSlice g p j) (p j)‖ := by
      rw [norm_mul,norm_inv,norm_cosetCharacter,inv_one,one_mul]
    _ ≤ _ := cuspRemainder_row_scaled_deriv_aux_bound a b hab s C hC0 hC _ (embeddedRow_ne_zero r) p hp j

theorem eisensteinRemainder_scaled_axis_bound (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) :
    ∃B : ℝ,0≤B ∧ ∀p : SpatialCoordinates,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*deriv (axisSlice (eisensteinRemainderField a b s) p j) (p j)‖≤B := by
  obtain ⟨C,hC0,hC⟩ := cuspTransition_euler_bounded a b hab
  refine ⟨(‖s‖+C)*eisensteinRemainderBound (b+2) s,
    mul_nonneg (add_nonneg (norm_nonneg s) hC0) (eisensteinRemainderBound_nonneg _ _),?_⟩
  intro p hp j
  have hA : Summable (fun r : CuspCosets =>
      ‖cuspRemainderProfile (b+1) (b+2) s (rowHeight (embeddedRow r) p)‖) ∧
      (∑'r : CuspCosets,‖cuspRemainderProfile (b+1) (b+2) s (rowHeight (embeddedRow r) p)‖)≤
        eisensteinRemainderBound (b+2) s := by
    simpa only [cosetHeight_upperPoint_rowHeight] using
      cuspRemainder_absolute_bound (b+1) (b+2) (by linarith) (by linarith) s hs
        (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp)
  have hB := hA.1.mul_left (‖s‖+C)
  have hb (r : CuspCosets) := weightedRemainder_scaled_deriv_bound a b hab s C hC0 hC r p hp j
  have hnorm := hB.of_nonneg_of_le (fun r => norm_nonneg
    ((p 2:ℂ)*deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j))) hb
  have ht := eisensteinRemainder_axis_termwise a b ha hab s (by linarith) p hp j
  rw [ht.2.deriv,←tsum_mul_left]
  apply (norm_tsum_le_tsum_norm hnorm).trans
  apply (Summable.tsum_le_tsum hb hnorm hB).trans
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hA.2 (add_nonneg (norm_nonneg s) hC0)

def kernelEisensteinRemainder (a b : ℝ) (s : ℂ) (hs : 2<s.re) : KernelQuotient→ℂ :=
  fun q => kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q

lemma kernelEisensteinRemainder_smooth (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ (kernelEisensteinRemainder a b s hs) :=
  (kernelQuotientEisenstein_contMDiff s hs).sub (kernelQuotientSeed_contMDiff a b s ha hab)

lemma kernelEisensteinRemainder_euclidean_smooth (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) (p : EuclideanSpatial) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (fun q => kernelEisensteinRemainder a b s hs (kernelEuclideanProjection q)) p :=
  ((((kernelEisensteinRemainder_smooth a b ha hab s hs).comp kernelProjection_contMDiff)
    (euclideanToHyperbolic p)).comp p (euclideanToHyperbolic_contMDiffAt p hp)).contDiffAt

lemma kernelEisensteinRemainder_euclidean_eq (a b : ℝ) (s : ℂ) (hs : 2<s.re)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    kernelEisensteinRemainder a b s hs (kernelEuclideanProjection p)=eisensteinRemainderField a b s p.ofLp := by
  unfold kernelEisensteinRemainder kernelEuclideanProjection
  simp only [Function.comp_apply]
  rw [euclideanToHyperbolic_positive p hp,kernelQuotientEisenstein_mk,hyperbolicEisenstein_upperPoint]
  unfold eisensteinRemainderField
  rw [smoothEisenstein_eq_actual s p.ofLp hp,smoothCuspSeedField,dite_eq_left hp]
  simp only [mul_comm Complex.I]
  rfl

theorem kernelEisensteinRemainder_scaled_fderiv_bound (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) :
    ∃B : ℝ,0≤B ∧ ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (fun q => kernelEisensteinRemainder a b s (by linarith)
        (kernelEuclideanProjection q)) p (euclideanCoordinateVector j)‖≤B := by
  obtain ⟨B,hB,hbound⟩ := eisensteinRemainder_scaled_axis_bound a b ha hab s hs
  refine ⟨B,hB,?_⟩
  intro p hp j
  let f : EuclideanSpatial→ℂ:=fun q => kernelEisensteinRemainder a b s (by linarith) (kernelEuclideanProjection q)
  have hf : ∀q,0<q 2→ContDiffAt ℝ ∞ f q := kernelEisensteinRemainder_euclidean_smooth a b ha hab s (by linarith)
  have he : ∀q : SpatialCoordinates,0<q 2→f (WithLp.toLp 2 q)=eisensteinRemainderField a b s q := by
    intro q hq
    exact kernelEisensteinRemainder_euclidean_eq a b s (by linarith) (WithLp.toLp 2 q) hq
  have heq := axisSlice_eventuallyEq_of_positive _ _ he p.ofLp hp j
  change ‖(p 2:ℂ)*fderiv ℝ f p (euclideanCoordinateVector j)‖≤B
  rw [←(euclideanAxisSlice_derivatives f hf p hp j).1,heq.deriv_eq]
  exact hbound p.ofLp hp j

end CubicEisenstein

end

end OAI
