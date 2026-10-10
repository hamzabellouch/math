import OAI.NumberTheory.DirichletL.Eisenstein.UnitNormalization

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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCoefficientClass (IsBaseRayTwist)

def outsideLogEnergy (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O)) (V : ℝ→ℂ) (X K : ℝ) : ℝ :=
  let P:=InitialMeanSquare.outsideSquarefreeIdeals S D
  let hP:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  letI : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span P hP i];infer_instance
  canonicalLogEnergy (poolPrimary P) (poolPrimary_ne_zero P hP) (poolPrimary_coprime P hP)
    (poolPrimary_good P hP) Finset.univ Ψ m labels V X K

theorem outsideLogEnergy_eq_completed
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O))
    (V : ℝ→ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) (X K : ℝ) (hX : 0<X) :
    outsideLogEnergy S D hbad Ψ m labels V X K=
      rowFamilyEnergy labels (fun I z=>outsideCanonicalRow S D hbad Ψ m (idealGenerator I) z
        (radialFromLog V hVs A hV) X) K := by
  exact canonicalLogEnergy_eq_completed_rows S D hbad Ψ m labels V hVs A hV X K hX

def HasCanonicalThetaModels (S : Finset (Ideal ActualEisensteinCubic.O)) (base : ActualEisensteinCubic.O→*ℂ)
    (ρ q levelBound : ℝ) : Prop :=
  ∀(A : ℝ),0≤A → ∀(W : ℝ→ℂ),
    Function.support W⊆Set.Icc (Real.exp (-A)) (Real.exp A) → ContDiff ℝ ∞ W →
    ∀κ : ℝ,0<κ → ∃C : ℝ,0≤C ∧
    ∀(Z K X F θ : ℝ),1≤Z → 1≤K → 0<X → 1≤F → F≤Z^((1:ℝ)/1000) →
    ∀(Ψ : ActualEisensteinCubic.O→*ℂ),IsBaseRayTwist base Ψ → ∀m : ActualEisensteinCubic.O,m≠0 →
    let G : Ideal ActualEisensteinCubic.O:=Ideal.span {m*excludedGenerator S}
    (2*K)*(Ideal.absNorm G:ℝ)≤X*F*Z^(-((1:ℝ)/40)) →
    ∃(rays : ℕ) (lengthScale : ℂ),(rays:ℝ)^2*‖lengthScale‖^2≤C*Z^κ ∧
      ∀u : ActualEisensteinCubic.Oˣ,∀f : idealRange F,∀H∈shortCubeRange (Z^((1:ℝ)/1000)),
        HasExactCompletedDyadicModels rays
          (((firstFrequencyDisk (2*K)).erase 0).image (fun z=>Ideal.span {z})) (2*K)
          (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound f.val (G*f.val)
          (CompletedHeight.normTwistedSource W θ)
          (CompletedUnitRows.unitRowFamily Ψ (m*excludedGenerator S) u f) lengthScale

theorem outsideLogEnergy_terminal_constant
    (V : ℝ→ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) :
    ∃C : ℝ,0≤C ∧ ∀(S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
      (base : ActualEisensteinCubic.O→*ℂ) (Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O))
      (X F K t : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
      (∀u,‖base u‖≤1) → 1<Z → 0≤η → 3000*η≤(1:ℝ)/40 →
      (fixedDepthRank Z K=0 ∨ X≤1) →
      outsideLogEnergy S D hbad (normHeightTwist Ψ t) m labels V X K≤C*(X*F)^2 := by
  have hVc : HasCompactSupport V :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (fun s hs=>abs_le.mp (hV s hs))
  let v : 𝓢(ℝ,ℂ):=hVc.toSchwartzMap hVs
  let M:=SchwartzMap.seminorm ℝ 0 0 v
  refine ⟨canonicalTerminalConstant A M,canonicalTerminalConstant_nonneg A M,?_⟩
  intro S D hbad base Z η Ψ m labels X F K t hstate hbase hZ hη hbudget hstop
  let P:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hP:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span P hP i];infer_instance
  have hinj : Function.Injective (fun i:primePool P=>Ideal.span {poolPrimary P i}) := by
    intro i j he
    exact Subtype.ext (by simpa only [poolPrimary_span P hP] using he)
  exact CanonicalStateCondition.terminal_energy (poolPrimary P) (poolPrimary_ne_zero P hP)
    (poolPrimary_coprime P hP) (poolPrimary_good P hP) (poolPrimary_odd P hP) hinj
    Finset.univ base (∏Q∈S,Q) Z η Ψ m labels X F K hstate hbase hZ hη hbudget
    V A M t (apply_nonneg _ _) (fun s=>SchwartzMap.norm_le_seminorm ℝ v s) hV hstop

end CanonicalRowCompletion

open scoped BigOperators Classical
namespace CompletedGauss

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)

def fractionalThetaPoint (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) : ℂ :=
  eisEmbedding u.val * eisEmbedding lambda^((m:ℤ)-4) * eisEmbedding n * eisEmbedding b^3

lemma embedding_lambda_ne_zero : eisEmbedding lambda≠0 :=
  by
    intro hz
    apply PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero
    apply ConcreteTraceCRT.eisEmbedding_injective
    simpa only [map_zero] using hz

theorem fractionalThetaPoint_clear (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) :
    eisEmbedding lambda^4*fractionalThetaPoint u m n b=
      eisEmbedding (u.val*lambda^m*(n*b^3)) := by
  unfold fractionalThetaPoint
  rw [zpow_sub₀ embedding_lambda_ne_zero]
  simp only [zpow_natCast,map_mul,map_pow]
  field_simp [embedding_lambda_ne_zero]

lemma embedding_lambda_norm_sq : ‖eisEmbedding lambda‖^2=(3:ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span,CubicEisenstein.absNorm_span_lambda]
  norm_num

theorem fractionalThetaPoint_norm_sq (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) :
    ‖fractionalThetaPoint u m n b‖^2=
      (3:ℝ)^((m:ℝ)-4)*‖eisEmbedding n‖^2*(‖eisEmbedding b‖^2)^3 := by
  have hp : (‖eisEmbedding lambda‖^((m:ℤ)-4))^2=(3:ℝ)^((m:ℝ)-4) := by
    calc
      _ = (‖eisEmbedding lambda‖^2)^((m:ℤ)-4) := by
        calc
          _ = ‖eisEmbedding lambda‖^(((m:ℤ)-4)*2):=by rw [zpow_mul]; norm_num
          _ = ‖eisEmbedding lambda‖^((2:ℤ)*((m:ℤ)-4)):=by congr 1; ring
          _ = _:=by rw [zpow_mul]; norm_num
      _ = (3:ℝ)^((m:ℤ)-4):=by rw [embedding_lambda_norm_sq]
      _ = _:=by rw [←Real.rpow_intCast]; norm_num
  simp only [fractionalThetaPoint,norm_mul,norm_zpow,norm_pow,
    GaussGeneratorTransport.norm_eisEmbedding_unit,one_mul,mul_pow,hp]
  ring

theorem fractionalThetaPoint_ne_zero (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O)
    (hn : n≠0) (hb : b≠0) : fractionalThetaPoint u m n b≠0 := by
  unfold fractionalThetaPoint
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero ((u.isUnit.map eisEmbedding).ne_zero) (zpow_ne_zero _ embedding_lambda_ne_zero)
    · intro hz
      apply hn
      apply ConcreteTraceCRT.eisEmbedding_injective
      simpa only [map_zero] using hz
  · apply pow_ne_zero
    intro hz
    apply hb
    apply ConcreteTraceCRT.eisEmbedding_injective
    simpa only [map_zero] using hz

end

section
open ActualEisensteinCubic CompletedDyadic LocalReflectionBrackets
open ConcreteTraceCRT (eisEmbedding)

theorem fractional_cusp_coefficient (d ζ : ℂ) (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O)
    (hn : n≠0) (hb : b≠0) :
    ζ*(d/((‖fractionalThetaPoint u m n b‖:ℝ):ℂ)) =
      (4/3:ℂ)*(81*ζ)*(normalizedCuspAmplitude d ((m:ℝ)-4) (‖eisEmbedding b‖^2) /
        ((4*ramifiedScale completedRamifiedInitial completedRamifiedStep m*
          ‖eisEmbedding n‖*‖eisEmbedding b‖^2:ℝ):ℂ)) := by
  have hn0 : 0<‖eisEmbedding n‖:=norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hn)
  have hb0 : 0<‖eisEmbedding b‖:=norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hb)
  have hh:=normalized_cusp_coefficient_nat d ζ m (‖eisEmbedding n‖^2) (‖eisEmbedding b‖^2)
    (sq_pos_of_pos hn0) (sq_pos_of_pos hb0)
  rw [←fractionalThetaPoint_norm_sq u m n b,Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _)] at hh
  exact hh

def normalizedThetaAmplitude (d : ℂ→ℂ) (vartheta : ActualEisensteinCubic.O→ℂ)
    (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) : ℂ :=
  normalizedCuspAmplitude (d (fractionalThetaPoint u m n b)) ((m:ℝ)-4) (‖eisEmbedding b‖^2) *
    (fractionalThetaPoint u m n b/(‖fractionalThetaPoint u m n b‖:ℂ)) *
    vartheta (u.val*lambda^m*(n*b^3))

theorem normalizedThetaAmplitude_norm (d : ℂ→ℂ) (vartheta : ActualEisensteinCubic.O→ℂ)
    (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) (hn : n≠0) (hb : b≠0)
    (hd : ‖d (fractionalThetaPoint u m n b)‖≤
      27*(3:ℝ)^(((m:ℝ)-4)/6)*‖eisEmbedding b‖)
    (hv : ‖vartheta (u.val*lambda^m*(n*b^3))‖≤1) :
    ‖normalizedThetaAmplitude d vartheta u m n b‖≤1 := by
  have hb0 : 0<‖eisEmbedding b‖:=norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hb)
  have hμ : fractionalThetaPoint u m n b≠0:=fractionalThetaPoint_ne_zero u m n b hn hb
  have ha:=normalizedCuspAmplitude_norm (d (fractionalThetaPoint u m n b)) ((m:ℝ)-4)
    (‖eisEmbedding b‖^2) (sq_pos_of_pos hb0) (by simpa only [Real.sqrt_sq (norm_nonneg _)] using hd)
  have hu : ‖fractionalThetaPoint u m n b/(‖fractionalThetaPoint u m n b‖:ℂ)‖=1 := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),div_self]
    exact norm_ne_zero_iff.mpr hμ
  simp only [normalizedThetaAmplitude,norm_mul,hu,mul_one]
  exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans hv

theorem cusp_summand_eq_local_branches {ι : Type*} [Fintype ι]
    (P : ι→Ideal ActualEisensteinCubic.O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (j : ι→ℕ)
    (d : ℂ→ℂ) (vartheta : ActualEisensteinCubic.O→ℂ) (ζ : ℂ)
    (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) (hn : n≠0) (hb : b≠0) :
    (ζ*(d (fractionalThetaPoint u m n b)/(‖fractionalThetaPoint u m n b‖:ℂ)))*
      (fractionalThetaPoint u m n b/(‖fractionalThetaPoint u m n b‖:ℂ))*
      vartheta (u.val*lambda^m*(n*b^3))*
      (∏i,bracket (actualSextic (P i) (hg i)) (j i)
        (Ideal.Quotient.mk (P i) (u.val*lambda^m*(n*b^3)))) =
    (4/3:ℂ)*(81*ζ)*ramifiedBranchPhase P hg j u m*
      ∑e : ι→Fin 3,
        (normalizedThetaAmplitude d vartheta u m n b*reflectedBranch P hg j e n b)/
          ((4*ramifiedScale completedRamifiedInitial completedRamifiedStep m*
            ‖eisEmbedding n‖*‖eisEmbedding b‖^2:ℝ):ℂ) := by
  rw [fractional_cusp_coefficient (d (fractionalThetaPoint u m n b)) ζ u m n b hn hb,
    ramified_bracket_full_expansion]
  simp only [normalizedThetaAmplitude,Finset.mul_sum,]
  apply Finset.sum_congr rfl
  intro e he
  ring

end

open ActualEisensteinCubic LocalReflectionBrackets
open ConcreteTraceCRT (eisEmbedding)

def paperLambda : ActualEisensteinCubic.O := 1+2*omega

def paperLambdaUnit : ActualEisensteinCubic.Oˣ where
  val := -omega
  inv := -omega^2
  val_inv := by
    calc
      (-omega)*(-omega^2)=omega^3:=by ring
      _=1:=omega_primitive.pow_eq_one
  inv_val := by
    calc
      (-omega^2)*(-omega)=omega^3:=by ring
      _=1:=omega_primitive.pow_eq_one

lemma paperLambdaUnit_six : (paperLambdaUnit.val:ActualEisensteinCubic.O)^6=1 := by
  change (-omega)^6=1
  calc
    (-omega)^6=(omega^3)^2:=by ring
    _=1:=by rw [omega_primitive.pow_eq_one,one_pow]

lemma paperLambda_eq : paperLambda=paperLambdaUnit.val*lambda := by
  change 1+2*omega=(-omega)*lambda
  change (1+2*omega:ActualEisensteinCubic.O)=(-omega)*(omega-1)
  have hw:=omega_primitive.geom_sum_eq_zero (by decide : 1<(3:ℕ))
  norm_num [Finset.sum_range_succ] at hw
  linear_combination hw

lemma paperLambda_embedding_ne_zero : eisEmbedding paperLambda≠0 := by
  rw [paperLambda_eq,map_mul]
  exact mul_ne_zero ((paperLambdaUnit.isUnit.map eisEmbedding).ne_zero) embedding_lambda_ne_zero

def paperFractionalThetaPoint (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) : ℂ :=
  eisEmbedding u.val*eisEmbedding paperLambda^((m:ℤ)-4)*eisEmbedding n*eisEmbedding b^3

def paperUnitReindex (m : ℕ) : ActualEisensteinCubic.Oˣ ≃ ActualEisensteinCubic.Oˣ := Equiv.mulRight (paperLambdaUnit^(m+2))

lemma paperUnitReindex_apply (m : ℕ) (u : ActualEisensteinCubic.Oˣ) :
    paperUnitReindex m u=u*paperLambdaUnit^(m+2):=rfl

theorem paperFractionalThetaPoint_eq (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) :
    paperFractionalThetaPoint u m n b=
      fractionalThetaPoint (paperUnitReindex m u) m n b := by
  have ht : eisEmbedding paperLambdaUnit.val≠0:=(paperLambdaUnit.isUnit.map eisEmbedding).ne_zero
  have ht6 : eisEmbedding paperLambdaUnit.val^6=1:=by
    rw [←map_pow,paperLambdaUnit_six,map_one]
  have hp : eisEmbedding paperLambdaUnit.val^((m:ℤ)-4)=eisEmbedding paperLambdaUnit.val^(m+2) := by
    rw [show (m:ℤ)-4=((m+2:ℕ):ℤ)-6 by omega,zpow_sub₀ ht]
    norm_num only [zpow_natCast,zpow_ofNat,ht6,div_one]
  simp only [paperFractionalThetaPoint,fractionalThetaPoint,paperUnitReindex_apply,
    Units.val_mul,Units.val_pow_eq_pow_val,map_mul,map_pow,paperLambda_eq,mul_zpow,hp]
  ring

theorem paperFractionalThetaPoint_clear (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) :
    eisEmbedding paperLambda^4*paperFractionalThetaPoint u m n b=
      eisEmbedding (u.val*paperLambda^m*(n*b^3)) := by
  unfold paperFractionalThetaPoint
  rw [zpow_sub₀ paperLambda_embedding_ne_zero]
  simp only [zpow_natCast,map_mul,map_pow]
  field_simp [paperLambda_embedding_ne_zero]

theorem paperFractionalThetaPoint_norm_sq (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) :
    ‖paperFractionalThetaPoint u m n b‖^2=
      (3:ℝ)^((m:ℝ)-4)*‖eisEmbedding n‖^2*(‖eisEmbedding b‖^2)^3 := by
  rw [paperFractionalThetaPoint_eq,fractionalThetaPoint_norm_sq]

theorem paperIntegralArgument_eq (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) :
    u.val*paperLambda^m*(n*b^3)=paperLambdaUnit.val^4*
      ((paperUnitReindex m u).val*lambda^m*(n*b^3)) := by
  apply ConcreteTraceCRT.eisEmbedding_injective
  rw [←paperFractionalThetaPoint_clear,paperFractionalThetaPoint_eq,
    paperLambda_eq,map_mul,mul_pow]
  rw [map_mul,map_pow,←fractionalThetaPoint_clear]
  ring

theorem paperBracket_transport (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] (hg : lambda∉P)
    (j : ℕ) (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) :
    bracket (actualSextic P hg) j (Ideal.Quotient.mk P (u.val*paperLambda^m*(n*b^3))) =
      unitArgumentFactor (actualSextic P hg) j (Ideal.Quotient.mk P (paperLambdaUnit.val^4))*
      bracket (actualSextic P hg) j
        (Ideal.Quotient.mk P ((paperUnitReindex m u).val*lambda^m*(n*b^3))) := by
  rw [paperIntegralArgument_eq,map_mul]
  apply bracket_mul_unit
  exact ((paperLambdaUnit.isUnit.pow 4).map (Ideal.Quotient.mk P)).ne_zero

lemma paperLambdaUnit_four : paperLambdaUnit.val^4=omega := by
  change (-omega)^4=omega
  calc
    _=omega^3*omega:=by ring
    _=omega:=by rw [omega_primitive.pow_eq_one,one_mul]

theorem paperBracket_one_transport (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] (hg : lambda∉P)
    (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) :
    bracket (actualSextic P hg) 1 (Ideal.Quotient.mk P (u.val*paperLambda^m*(n*b^3))) =
      bracket (actualSextic P hg) 1
        (Ideal.Quotient.mk P ((paperUnitReindex m u).val*lambda^m*(n*b^3))) := by
  rw [paperBracket_transport,paperLambdaUnit_four]
  have hv : (actualSextic P hg (Ideal.Quotient.mk P omega))^3=1 := by
    rw [←map_pow,←map_pow,omega_primitive.pow_eq_one,map_one,map_one]
  have hf : unitArgumentFactor (actualSextic P hg) 1 (Ideal.Quotient.mk P omega)=1 := by
    simp only [unitArgumentFactor,show (1:ℕ)≠4 by decide,ite_false]
    rw [show (1:ℕ)+2=3 by rfl,MulChar.inv_apply_eq_inv',MulChar.pow_apply' _ (by decide : (3:ℕ)≠0),hv,inv_one]
  rw [hf,one_mul]

end CompletedGauss

open scoped BigOperators Classical SchwartzMap ContDiff
namespace CanonicalCubeSeparation

lemma columnWindowRadius_exp (A : ℝ) (hA : 0≤A) :
    columnWindowRadius (Real.exp (-A)) (Real.exp A)=2*A+3 := by
  rw [columnWindowRadius,Real.log_exp,Real.log_exp,abs_neg,abs_of_nonneg hA]
  ring

theorem fixed_reopening_profiles (A : ℝ) (hA : 0≤A) :
    ∃g V : 𝓢(ℝ,ℂ), HasCompactSupport (g:ℝ→ℂ) ∧ HasCompactSupport (V:ℝ→ℂ) ∧
      (∀u,|u|≤columnWindowRadius (Real.exp (-A)) (Real.exp A)→g u=1) ∧
      (∀u,g u≠0→|u|≤2*A+4) ∧
      (∀u,g u≠0→V u=1) ∧
      (∀u,V u≠0→|u|≤2*A+5) := by
  obtain ⟨g,hgc,hgs,hgone,hgsupp,hgzero⟩:=FourierBridge.exists_complex_smooth_cutoff (2*A+3) (by linarith)
  obtain ⟨v,hvc,hvs,hvone,hvsupp,hvzero⟩:=FourierBridge.exists_complex_smooth_cutoff (2*A+4) (by linarith)
  let gs : 𝓢(ℝ,ℂ):=hgc.toSchwartzMap hgs
  let vs : 𝓢(ℝ,ℂ):=hvc.toSchwartzMap hvs
  have hgbound : ∀u,g u≠0→|u|≤2*A+4 := by
    intro u hu
    have hh:=abs_le.mpr (hgsupp (subset_tsupport g hu))
    linarith
  refine ⟨gs,vs,hgc,hvc,?_,hgbound,?_,?_⟩
  · intro u hu
    exact hgone u (by simpa only [columnWindowRadius_exp A hA] using hu)
  · intro u hu
    exact hvone u (hgbound u hu)
  · intro u hu
    have hh:=abs_le.mpr (hvsupp (subset_tsupport v hu))
    linarith

lemma fixed_reopening_child_radius (A : ℝ) : (2*A+4)+7=2*A+11 := by ring

end CanonicalCubeSeparation

namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open ConcreteTraceCRT (eisEmbedding)

theorem canonicalShortState_geometry (S : Finset (Ideal ActualEisensteinCubic.O))
    (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : ActualEisensteinCubic.O→*ℂ) (Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F K : ℝ)
    (hstate : CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K)
    (hZ : 1≤Z) (hZbig : Real.exp 9000≤Z) (hη : 0≤η)
    (hbudget : 3000*η≤(1:ℝ)/80)
    (hfixed : 2*‖eisEmbedding (excludedGenerator S)‖^2≤Z^((1:ℝ)/80)) :
    let G:=Ideal.span {m*excludedGenerator S}
    G≠0 ∧ (∀P∈fixedBadPrimes,P∣G) ∧ labels⊆idealRange F ∧
      X*F≤Z^3 ∧ (2*K)*(Ideal.absNorm G:ℝ)≤X*F*Z^(-((1:ℝ)/40)) := by
  have hprod : (∏P∈S,P)≠0:=Finset.prod_ne_zero_iff.mpr (fun P hP=>(hSp P hP).ne_zero)
  have he : excludedGenerator S≠0:=idealGenerator_ne_zero _ hprod
  have hG : (Ideal.span {m*excludedGenerator S}:Ideal ActualEisensteinCubic.O)≠0:=
    Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero hstate.mask_ne_zero he)
  have hpG : ∀P∈fixedBadPrimes,P∣Ideal.span {m*excludedGenerator S} := by
    intro P hP
    apply Ideal.dvd_iff_le.mpr
    apply Ideal.span_le.mpr
    exact Set.singleton_subset_iff.mpr (P.mul_mem_left m (excludedGenerator_mem S (hbad hP)))
  have hlabels : labels⊆idealRange F:=canonicalLabels_subset_idealRange base (∏P∈S,P) Z η Ψ m labels X F K hstate
    (fun P hP=>Finset.dvd_prod_of_mem (fun Q:Ideal ActualEisensteinCubic.O=>Q) (hbad hP))
  have hmass : X*F≤Z^3:=hstate.mass_le.trans (canonicalRankMass_global Z hZbig _)
  refine ⟨hG,hpG,hlabels,hmass,?_⟩
  have hZ0 : 0<Z:=zero_lt_one.trans_le hZ
  have hXF : 0≤X*F:=mul_nonneg hstate.column_pos.le (zero_le_one.trans hstate.label_ge_one)
  have hm : (3:ℝ)/80≤canonicalRankMargin ((1:ℝ)/20) η (fixedDepthRank Z K) :=
    (by linarith : (3:ℝ)/80≤(1:ℝ)/20-3000*η).trans (canonicalRankMargin_lower _ η hη _)
  have hi : K*‖eisEmbedding m‖^2≤(X*F)*Z^(-((3:ℝ)/80)):=
    hstate.invariant.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (neg_le_neg hm)) hXF)
  rw [←eisEmbedding_norm_sq_eq_absNorm_span,map_mul,norm_mul,mul_pow]
  calc
    (2*K)*(‖eisEmbedding m‖^2*‖eisEmbedding (excludedGenerator S)‖^2)=
        (2*‖eisEmbedding (excludedGenerator S)‖^2)*(K*‖eisEmbedding m‖^2):=by ring
    _ ≤ Z^((1:ℝ)/80)*((X*F)*Z^(-((3:ℝ)/80))):=
      mul_le_mul hfixed hi (mul_nonneg (zero_le_one.trans hstate.row_ge_one) (sq_nonneg _)) (by positivity)
    _ = (X*F)*(Z^((1:ℝ)/80)*Z^(-((3:ℝ)/80))):=by ring
    _ = _:=by rw [←Real.rpow_add hZ0]; norm_num

theorem canonicalShortState_uniform_twist
    (a b : ℝ) (ha : 0<a) (ε ρ q levelBound : ℝ)
    (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃d : ℕ,∀W : ℝ→ℂ,Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
    ∃C : ℝ,0≤C ∧ ∀(θ : ℝ) (rays : ℕ) (S : Finset (Ideal ActualEisensteinCubic.O)),
    (∀P∈S,Prime P) → fixedBadPrimes⊆S →
    ∀(base : ActualEisensteinCubic.O→*ℂ) (Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F K : ℝ),
    CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
    (∀x,‖base x‖≤1) → 1≤Z → Real.exp 9000≤Z → 0≤η → 3000*η≤(1:ℝ)/80 →
    2*‖eisEmbedding (excludedGenerator S)‖^2≤Z^((1:ℝ)/80) → ∀lengthScale : ℂ,
    (F<Z^((1:ℝ)/1000) → ∀u : ActualEisensteinCubic.Oˣ,∀f : idealRange F,∀H∈shortCubeRange (Z^((1:ℝ)/1000)),
      HasExactCompletedDyadicModels rays (((firstFrequencyDisk (2*K)).erase 0).image (fun z=>Ideal.span {z})) (2*K)
        (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound f.val ((Ideal.span {m*excludedGenerator S})*f.val)
        (CompletedHeight.normTwistedSource W θ)
        (CompletedUnitRows.unitRowFamily Ψ (m*excludedGenerator S) u f) lengthScale) →
    2*X*rowFamilyEnergy labels (fun I z=>shortCompletedSum
      (rowTwist (normHeightTwist Ψ θ) (m*excludedGenerator S) (idealGenerator I) z)
      W X (if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0)) K≤
    (C*(1+‖θ‖)^d)*(rays:ℝ)^2*‖lengthScale‖^2*(X*F)^2*Z^(7*ε-(1:ℝ)/40) := by
  obtain ⟨d,hbound⟩:=canonicalShortEnergy_normalized_uniform_twist a b ha ε ρ q levelBound hε hρ hq hlevel
  refine ⟨d,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hb⟩:=hbound W hs hW
  refine ⟨C,hC,?_⟩
  intro θ rays S hSp hbad base Z η Ψ m labels X F K hstate hbase hZ hZbig hη hbudget hfixed lengthScale hmodels
  by_cases hF : F<Z^((1:ℝ)/1000)
  · rw [ite_eq_left hF]
    obtain ⟨hG,hpG,hlabels,hmass,hmargin⟩:=canonicalShortState_geometry S hSp hbad base Z η Ψ m labels X F K
      hstate hZ hZbig hη hbudget hfixed
    exact hb θ rays Z K X F hZ hstate.row_ge_one hstate.label_ge_one hF.le hstate.column_pos hmass
      (Ideal.span {m*excludedGenerator S}) hG hpG hmargin labels hlabels Ψ
      (fun x=>hstate.coefficient.norm_le hbase x) (m*excludedGenerator S) lengthScale (hmodels hF)
  · rw [ite_eq_right hF,rowFamilyEnergy_eq_sum labels _ K (zero_lt_one.trans_le hstate.row_ge_one)]
    have hz (I : Ideal ActualEisensteinCubic.O) (z : ActualEisensteinCubic.O) : shortCompletedSum
        (rowTwist (normHeightTwist Ψ θ) (m*excludedGenerator S) (idealGenerator I) z) W X 0=0:=
      shortCompletedSum_nonpos _ _ _ _ le_rfl
    simp only [hz,norm_zero,zero_pow (by decide : (2:ℕ)≠0),mul_zero,Finset.sum_const_zero]
    positivity

end CanonicalRowCompletion

namespace CanonicalCubeSeparation

def radiusIter (A : ℝ) : ℕ→ℝ
  | 0=>A
  | n+1=>radiusIter (2*A+11) n

@[simp] theorem radiusIter_zero (A : ℝ) : radiusIter A 0=A:=rfl
@[simp] theorem radiusIter_succ (A : ℝ) (n : ℕ) :
    radiusIter A (n+1)=radiusIter (2*A+11) n:=rfl

theorem radiusIter_mono_base (n : ℕ) : Monotone (fun A:ℝ=>radiusIter A n) := by
  induction n with
  | zero=>intro A B h;exact h
  | succ n ih=>intro A B h;exact ih (by linarith : 2*A+11≤2*B+11)

theorem radiusIter_nonneg (A : ℝ) (hA : 0≤A) (n : ℕ) : 0≤radiusIter A n := by
  induction n generalizing A with
  | zero=>exact hA
  | succ n ih=>exact ih (2*A+11) (by linarith)

theorem radiusIter_mono_depth (A : ℝ) (hA : 0≤A) : Monotone (radiusIter A) := by
  apply monotone_nat_of_le_succ
  intro n
  exact radiusIter_mono_base n (by linarith : A≤2*A+11)

theorem le_radiusIter (A : ℝ) (hA : 0≤A) (n : ℕ) : A≤radiusIter A n :=
  radiusIter_mono_depth A hA (Nat.zero_le n)

theorem radiusIter_child_le (A : ℝ) (hA : 0≤A) (s r : ℕ) (hs : s<r) :
    radiusIter (2*A+11) s≤radiusIter A r :=
  radiusIter_mono_depth A hA (Nat.succ_le_of_lt hs)

theorem common_pool_parent (A Z X D : ℝ) (r : ℕ) (hA : 0≤A)
    (_hZ : 0≤Z) (hX : 0≤X) (hXZ : X≤Z^3)
    (hD : Real.exp (radiusIter A r)*Z^3≤D) : Real.exp A*X≤D := by
  exact (mul_le_mul (Real.exp_le_exp.mpr (le_radiusIter A hA r)) hXZ hX
    (Real.exp_pos _).le).trans hD

theorem common_pool_child (A Z D : ℝ) (s r : ℕ) (hA : 0≤A)
    (hZ : 0≤Z) (hs : s<r) (hD : Real.exp (radiusIter A r)*Z^3≤D) :
    Real.exp (radiusIter (2*A+11) s)*Z^3≤D :=
  (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (radiusIter_child_le A hA s r hs))
    (pow_nonneg hZ _)).trans hD

end CanonicalCubeSeparation

open scoped BigOperators Classical
namespace QuadraticAllOddCRT
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisTraceModChar finite_quotient_span)
open FiniteGaussPhase hiding O

def character (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] : MulChar (ActualEisensteinCubic.O⧸P) ℂ := by
  letI : Field (ActualEisensteinCubic.O⧸P):=Ideal.Quotient.field P
  letI : Fintype (ActualEisensteinCubic.O⧸P):=Fintype.ofFinite _
  exact (quadraticChar (ActualEisensteinCubic.O⧸P)).ringHomComp (Int.castRingHom ℂ)

theorem normalized_prime_eq_square_sum (p : ActualEisensteinCubic.O) (hp : p≠0)
    [(Ideal.span {p}).IsMaximal] (hc : ringChar (ActualEisensteinCubic.O⧸Ideal.span {p})≠2) :
    ConcreteBreveE.normalizedTraceGauss p hp (character (Ideal.span {p}))=
      quadraticGammaO p hp := by
  let : Field (ActualEisensteinCubic.O⧸Ideal.span {p}):=Ideal.Quotient.field _
  let : Fintype (ActualEisensteinCubic.O⧸Ideal.span {p}):=Fintype.ofFinite _
  let ψ:=eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates p hp
  have hψ:ψ≠1:=by
    have hprim:=GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp
    simpa only [AddChar.mulShift_one] using hprim (a:=1) one_ne_zero
  change gaussSum (character (Ideal.span {p})) ψ/(‖eisEmbedding p‖:ℂ)=
    (∑x:ActualEisensteinCubic.O⧸Ideal.span {p},ψ (x^2))/(‖eisEmbedding p‖:ℂ)
  congr 1
  exact ShortDraftQuadraticGauss.quadratic_gauss_as_square_phase ψ hc hψ

theorem normalized_product_eq_square_sum {ι : Type*} [Fintype ι]
    (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2) :
    normalizedProductTraceGauss p hp hcop (fun i=>character (Ideal.span {p i}))=
      quadraticGammaO (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)) := by
  let c:=∏i,p i
  have hc0:c≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  let : Finite (ActualEisensteinCubic.O⧸Ideal.span {c}):=finite_quotient_span hc0
  let : Fintype (ActualEisensteinCubic.O⧸Ideal.span {c}):=Fintype.ofFinite _
  let (i:ι) : Fintype (ActualEisensteinCubic.O⧸Ideal.span {p i}):=Fintype.ofFinite _
  let (i:ι) : Field (ActualEisensteinCubic.O⧸Ideal.span {p i}):=Ideal.Quotient.field _
  let e:=productElementCRT p hcop
  let ψ:=eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc0
  change (∑x:ActualEisensteinCubic.O⧸Ideal.span {c},(∏i,character (Ideal.span {p i}) (e x i))*ψ x)/(‖eisEmbedding c‖:ℂ)=
    (∑x:ActualEisensteinCubic.O⧸Ideal.span {c},ψ (x^2))/(‖eisEmbedding c‖:ℂ)
  congr 1
  exact IdealGaussCRT.quadratic_gauss_finite_crt_eq_square_sum
    (fun i=>ActualEisensteinCubic.O⧸Ideal.span {p i}) e ψ (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc0) hc

theorem quadraticGamma_product {ι : Type*} [Fintype ι]
    (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2) :
    quadraticGammaO (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))=
      ∏i,character (Ideal.span {p i}) (Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i))*
        quadraticGammaO (p i) (hp i) := by
  rw [←normalized_product_eq_square_sum p hp hcop hc,normalizedProductTraceGauss_crt]
  apply Finset.prod_congr rfl
  intro i hi
  rw [normalized_prime_eq_square_sum _ _ (hc i)]

end QuadraticAllOddCRT

end

end OAI
