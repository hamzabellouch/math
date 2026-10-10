import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicVolume
import OAI.NumberTheory.DirichletL.CubicSieve.UniformTransfer

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

namespace CanonicalQuadraticSieve

theorem list_prod_le_power (xs : List ℝ) (U : ℝ) (hU : 0≤U)
    (hxs : ∀x∈xs, 0≤x ∧ x≤U) : xs.prod≤U^xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hxs x (by simp)
    have ht : ∀y∈xs, 0≤y ∧ y≤U := fun y hy => hxs y (by simp [hy])
    simp only [List.prod_cons,List.length_cons,pow_succ]
    have hp : 0≤xs.prod := List.prod_nonneg (fun y hy => (ht y hy).1)
    exact (mul_le_mul hx.2 (ih ht) hp hU).trans_eq (mul_comm _ _)

theorem list_prod_budget (xs budget : List ℝ) (U : ℝ) (hU : 1≤U)
    (hbudget : ∀x∈budget, 0≤x ∧ x≤U) (hxs : ∀x∈xs, x∈budget) (hlen : xs.length≤8) :
    xs.prod≤U^8 := by
  apply (list_prod_le_power xs U (by linarith) (fun x hx => hbudget x (hxs x hx))).trans
  exact pow_le_pow_right₀ hU hlen

theorem poisson_nine_terms_box
    (d lk ln f e vh vz dv uh du lat cd cs ct cp M N T a b eD eS tail U S : ℝ)
    (hU : 1≤U) (hS : 0≤S)
    (hbudget : ∀x∈([d,lk,ln,f,e,vh,vz,dv,uh,du,lat,cd,cs,ct,cp] : List ℝ), 0≤x ∧ x≤U)
    (hM : 0≤M) (hN : 0≤N) (hT : 1≤T) (ha : 0≤a)
    (hMS : M≤S) (hNS : N≤S) (hTa : T*a≤S)
    (hb : 0≤b ∧ b≤S) (hED : 0≤eD ∧ eD≤S) (hES : 0≤eS ∧ eS≤S)
    (htail : 0≤tail ∧ tail≤S) :
    d*lk*(8*vh*ln^2*f*e*(M+a) + 8*vz*ln^2*f*e*(M+2*T*a) +
      8*ln^2*lat*dv*f*e*(M+2*T*a) + 65536*cd*eD) +
    1536*d*ct*tail +
    lk*(2*uh*d*ln^2*f*e*(4*N/T+a) + 2*d*ln^2*lat*du*f*e*(N+2*T*a) +
      32768*cs*eS) + uh*d^2*cp*b ≤ 262144*U^8*S := by
  let budget : List ℝ := [d,lk,ln,f,e,vh,vz,dv,uh,du,lat,cd,cs,ct,cp]
  have hp (xs : List ℝ) (hx : ∀x∈xs, x∈budget) (hn : xs.length≤8) : xs.prod≤U^8 :=
    list_prod_budget xs budget U hU hbudget hx hn
  have hc1 : d*lk*vh*ln^2*f*e≤U^8 := by
    have hh := hp [d,lk,vh,ln,ln,f,e] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have hc2 : d*lk*vz*ln^2*f*e≤U^8 := by
    have hh := hp [d,lk,vz,ln,ln,f,e] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have hc3 : d*lk*ln^2*lat*dv*f*e≤U^8 := by
    have hh := hp [d,lk,ln,ln,lat,dv,f,e] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have hc4 : d*lk*cd≤U^8 := by
    have hh := hp [d,lk,cd] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,mul_assoc] using hh
  have hc5 : d*ct≤U^8 := by
    have hh := hp [d,ct] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,mul_assoc] using hh
  have hc6 : lk*uh*d*ln^2*f*e≤U^8 := by
    have hh := hp [lk,uh,d,ln,ln,f,e] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have hc7 : lk*d*ln^2*lat*du*f*e≤U^8 := by
    have hh := hp [lk,d,ln,ln,lat,du,f,e] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have hc8 : lk*cs≤U^8 := by
    have hh := hp [lk,cs] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,mul_assoc] using hh
  have hc9 : uh*d^2*cp≤U^8 := by
    have hh := hp [uh,d,d,cp] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have haS : a≤S := (by nlinarith only [ha, hT] : a≤T*a).trans hTa
  have hdiv : N/T≤N := div_le_self hN hT
  have h1 : M+a≤2*S := by linarith only [hMS, haS]
  have h2 : M+2*T*a≤3*S := by nlinarith only [hMS, hTa]
  have h3 : M+2*T*a≤3*S := h2
  have h6 : 4*N/T+a≤5*S := by rw [mul_div_assoc]; linarith only [hdiv, hNS, haS]
  have h7 : N+2*T*a≤3*S := by nlinarith only [hNS, hTa]
  have hU8 : 0≤U^8 := by positivity
  have ht1 := mul_le_mul hc1 h1 (by positivity : 0≤M+a) hU8
  have ht2 := mul_le_mul hc2 h2 (by positivity : 0≤M+2*T*a) hU8
  have ht3 := mul_le_mul hc3 h3 (by positivity : 0≤M+2*T*a) hU8
  have ht4 := mul_le_mul hc4 hED.2 hED.1 hU8
  have ht5 := mul_le_mul hc5 htail.2 htail.1 hU8
  have ht6 := mul_le_mul hc6 h6 (by positivity : 0≤4*N/T+a) hU8
  have ht7 := mul_le_mul hc7 h7 (by positivity : 0≤N+2*T*a) hU8
  have ht8 := mul_le_mul hc8 hES.2 hES.1 hU8
  have ht9 := mul_le_mul hc9 hb.2 hb.1 hU8
  nlinarith only [ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, mul_nonneg hU8 hS]

open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy EisensteinSchwartzPoisson

def poissonUnitBudget
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε)
    (G : Ideal O) (K N : ℝ) (W : 𝓢(ℝ,ℂ)) : List ℝ :=
  [(IdealMobiusDivisorSum.idealDivisors G).card,
   (columnDyadicLength K+1:ℕ), (columnDyadicLength N+1:ℕ),
   256*(supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2,
   divisorExponentConstant hexp deltaLoss hδ*((2*K)*N)^deltaLoss,
   ‖paperRadialFourier (quadraticTransformedSquareProfile W) 0‖,
   ‖quadraticTransformedSquareProfile W 0‖,
   dualMiddleDecayConstant (quadraticTransformedSquareProfile W),
   ‖paperRadialFourier (quadraticSquareProfile W) 0‖,
   originalMiddleDecayConstant (quadraticSquareProfile W),
   nonzeroLatticeEnvelopeConstant,
   supportConstant ε hε*(N*N)^ε*(CD*sD.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W)),
   supportConstant ε hε*((Ideal.absNorm G:ℝ)*(N*N))^ε*(CS*sS.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)),
   CT*sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W,
   supportConstant ε hε*N^ε*CP*(K*N)^deltaLoss]

theorem poissonComparisonMajorant_unit_box
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ) (l A : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε)
    (G : Ideal O) (K N M T U S : ℝ) (W : 𝓢(ℝ,ℂ))
    (hK : 0≤K) (hN : 0<N) (hM : 0≤M) (hT : 1≤T) (hU : 1≤U) (hS : 0≤S)
    (hbudget : ∀x∈poissonUnitBudget sD sS sT CD CS CT CP hexp deltaLoss hδ ε hε G K N W, 0≤x ∧ x≤U)
    (hMS : M≤S) (hNS : N≤S) (hmid : T*Real.sqrt M*(2*K)^(α-1/2)≤S)
    (hpr : Real.sqrt (M/K)*N+Real.sqrt M*K^(α-1/2)≤S)
    (hED : K*M/T^l≤S) (hES : K*N/T^l≤S)
    (htail : M/((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*
      (1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A)≤S) :
    poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε G K N M T
      (fun _ : Unit => (1:ℂ)) W ≤ 262144*U^8*S := by
  have hh := poisson_nine_terms_box
    ((IdealMobiusDivisorSum.idealDivisors G).card:ℝ)
    (columnDyadicLength K+1:ℕ) (columnDyadicLength N+1:ℕ)
    (256*(supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2)
    (divisorExponentConstant hexp deltaLoss hδ*((2*K)*N)^deltaLoss)
    ‖paperRadialFourier (quadraticTransformedSquareProfile W) 0‖
    ‖quadraticTransformedSquareProfile W 0‖
    (dualMiddleDecayConstant (quadraticTransformedSquareProfile W))
    ‖paperRadialFourier (quadraticSquareProfile W) 0‖
    (originalMiddleDecayConstant (quadraticSquareProfile W)) nonzeroLatticeEnvelopeConstant
    (supportConstant ε hε*(N*N)^ε*(CD*sD.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W)))
    (supportConstant ε hε*((Ideal.absNorm G:ℝ)*(N*N))^ε*(CS*sS.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)))
    (CT*sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)
    (supportConstant ε hε*N^ε*CP*(K*N)^deltaLoss)
    M N T (Real.sqrt M*(2*K)^(α-1/2))
    (Real.sqrt (M/K)*N+Real.sqrt M*K^(α-1/2))
    (K*M/T^l) (K*N/T^l)
    (M/((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*(1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A))
    U S hU hS hbudget hM hN.le hT (by positivity) hMS hNS
    (by simpa only [mul_assoc] using hmid) ⟨by positivity,hpr⟩
    ⟨by positivity,hED⟩ ⟨by positivity,hES⟩ ⟨by positivity,htail⟩
  convert hh using 1
  unfold poissonComparisonMajorant retainedDualMajorant sourcePrincipalMajorant
    smallPrincipalMajorant dualMiddleMajorant
  simp only [divisorEnergyFactor_diagonal,Fintype.sum_unique,norm_one,one_pow,
    mul_one,one_mul,div_one]
  field_simp
  ; ring

end CanonicalQuadraticSieve

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in

theorem globalBin_mask_bound (B F : ℝ) (hB : 0 < B) (hF : 1 ≤ F)
    (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) (m : O)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    ‖eisEmbedding (fixedTripleMask m (globalSecondFixedTriple p x))‖^2 ≤
      ‖eisEmbedding m‖^2*(Real.exp 1)^2*globalPooledDelta B F (globalScaleIndex p side x) := by
  let j := globalScaleIndex p side x
  have hb0 := (cube_label_norm_bounds p hp x.cube.support x.cube.leftExponent x.cube.rightExponent
    x.cube.leftBit x.cube.rightBit x.cube.support_pos B hB.le hb₁ hb₂).2.1
  have he : ‖eisEmbedding (fixedTripleMask m (globalSecondFixedTriple p x))‖^2 =
      ‖eisEmbedding (globalSecondMask p m x)‖^2 := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,eisEmbedding_norm_sq_eq_absNorm_span,globalSecondMask_span]
  rw [he]
  have ht := (globalScaleIndex_bounds p hp side x hk 2).2
  have hr := (globalScaleIndex_bounds p hp side x hk 3).2
  change primeProductNorm p x.firstCommon ≤ globalLogRep j 2*Real.exp 1 at ht
  change primeProductNorm p (x.source.sourceCommon\x.source.divisor) ≤ globalLogRep j 3*Real.exp 1 at hr
  have ht0 := (FirstPassCubeLabels.primeProductNorm_pos p hp x.firstCommon).le
  have hr0 := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.source.sourceCommon\x.source.divisor)).le
  have hj2 := (globalLogRep_pos j 2).le
  have hj3 := (globalLogRep_pos j 3).le
  have ha := globalLogRep_ge_one j 0
  change ‖eisEmbedding ((m*_*_)*∏ i∈x.firstCommon,p i)‖^2 ≤ _
  rw [SecondPassIntegration.restored_child_mask_norm]
  calc
    _ ≤ ‖eisEmbedding m‖^2*B*(globalLogRep j 3*Real.exp 1)*(globalLogRep j 2*Real.exp 1) := by gcongr
    _ ≤ ‖eisEmbedding m‖^2*(B*F*globalLogRep j 0)*(globalLogRep j 3*Real.exp 1)*(globalLogRep j 2*Real.exp 1) := by
      gcongr
      calc
        B = B*1*1 := by ring
        _ ≤ _ := by gcongr
    _ = _ := by unfold globalPooledDelta;ring

include hp in

theorem globalBin_invariant (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 1 ≤ F) (side : Bool) (x : GlobalSecondData ι)
    (hk : x.source.frequency ≠ 0) (m : O)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    let j := globalScaleIndex p side x
    (globalLogRep j 8*Real.exp 1)*‖eisEmbedding (fixedTripleMask m (globalSecondFixedTriple p x))‖^2 /
      (globalPooledColumnScale ell j*globalPooledLabelScale j) ≤
    (globalBinRadial ell (globalPooledRowScale K ell B F j) j/(Real.exp 1)^2)*
      (K*‖eisEmbedding m‖^2/((ell*B^3)*F)) := by
  dsimp only
  let j := globalScaleIndex p side x
  have hm := globalBin_mask_bound p hp B F hB hF side x hk m hb₁ hb₂
  have hcol := globalPooledColumnScale_pos ell hell j
  have hlab : 0 < globalPooledLabelScale j := zero_lt_one.trans_le (globalPooledLabelScale_ge_one j)
  have hk8 := globalLogRep_pos j 8
  have hF0 : 0 < F := zero_lt_one.trans_le hF
  calc
    _ ≤ (globalLogRep j 8*Real.exp 1)*
        (‖eisEmbedding m‖^2*(Real.exp 1)^2*globalPooledDelta B F j)/
        (globalPooledColumnScale ell j*globalPooledLabelScale j) := by gcongr
    _ = _ := by
      have h (i : Fin 10) := (globalLogRep_pos j i).ne'
      have he : Real.exp 4=(Real.exp 1)^4 := by simp
      dsimp only [j] at h ⊢
      unfold globalPooledColumnScale globalPooledLabelScale globalPooledDelta globalPooledRowScale globalBinRadial
      rw [he]
      unfold globalPooledColumnScale
      field_simp [h]

include hp in
theorem globalBin_invariant_small_padding (Z η K ell B F : ℝ) (hZ : 1 < Z)
    (hK : 0 < K) (hell : 0 < ell) (hB : 0 < B) (hF : 1 ≤ F)
    (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) (m : O)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hpad : globalBinRadial ell (globalPooledRowScale K ell B F (globalScaleIndex p side x))
      (globalScaleIndex p side x) ≤ Z^η) :
    let j := globalScaleIndex p side x
    (globalLogRep j 8*Real.exp 1)*‖eisEmbedding (fixedTripleMask m (globalSecondFixedTriple p x))‖^2 /
      (globalPooledColumnScale ell j*globalPooledLabelScale j) ≤
    Z^η*(K*‖eisEmbedding m‖^2/((ell*B^3)*F)) := by
  dsimp only
  apply (globalBin_invariant p hp K ell B F hK hell hB hF side x hk m hb₁ hb₂).trans
  have hz0 : 0 < Z := zero_lt_one.trans hZ
  have hpow : 0 ≤ Z^η := (Real.rpow_pos_of_pos hz0 η).le
  have he : 1 ≤ (Real.exp 1)^2 := one_le_pow₀ (Real.one_le_exp (by norm_num))
  have hr : globalBinRadial ell (globalPooledRowScale K ell B F (globalScaleIndex p side x))
      (globalScaleIndex p side x)/(Real.exp 1)^2 ≤ Z^η :=
    (div_le_iff₀ (sq_pos_of_pos (Real.exp_pos 1))).mpr (hpad.trans (le_mul_of_one_le_right hpow he))
  apply mul_le_mul_of_nonneg_right hr
  positivity

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open SecondPassIntegration (densityChildEnergy)
open ConcreteTraceCRT (eisEmbedding)

def globalBinTriples {ι : Type*} [DecidableEq ι] (p : ι → O)
    (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex) : Finset (Ideal O × Ideal O × Ideal O) :=
  (globalLogSector p s side j).image (globalSecondFixedTriple p)

def globalBinLossScale (B : ℝ) (j : GlobalLogIndex) : ℝ :=
  globalPooledLabelScale j*(B*(Real.sqrt (globalLogRep j 9)*Real.exp 1)/globalLogRep j 4)

def globalDescentWeight (C ε θ₁ θ₂ K ell B F : ℝ) (A J : ℕ) (j : GlobalLogIndex)
    (ray : SecondRayIndex) (q : Ideal O × Ideal O × Ideal O) : ℝ :=
  C*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2)*globalBinFirstCoefficient K ell B F j *
    globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j *
    (globalPooledLabelScale j*Ideal.absNorm q.1)^ε /
    (1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^A *
    (globalPooledColumnScale ell j*globalPooledLabelScale j)

theorem globalPooledRowScale_pos (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) (j : GlobalLogIndex) : 0 < globalPooledRowScale K ell B F j := by
  have h1 := globalLogRep_pos j 1
  have h4 := globalLogRep_pos j 4
  have h5 := globalLogRep_pos j 5
  unfold globalPooledRowScale
  positivity

theorem globalBinFirstCoefficient_nonneg (K ell B F : ℝ) (hK : 0 ≤ K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) (j : GlobalLogIndex) : 0 ≤ globalBinFirstCoefficient K ell B F j := by
  have h5 := globalLogRep_pos j 5
  have hs := Real.sqrt_pos.mpr (globalLogRep_pos j 9)
  unfold globalBinFirstCoefficient
  positivity

theorem globalDescentWeight_nonneg (C ε θ₁ θ₂ K ell B F : ℝ) (A J : ℕ) (j : GlobalLogIndex)
    (ray : SecondRayIndex) (q : Ideal O × Ideal O × Ideal O)
    (hC : 0 ≤ C) (hK : 0 < K) (hell : 0 < ell) (hB : 0 < B) (hF : 0 < F) :
    0 ≤ globalDescentWeight C ε θ₁ θ₂ K ell B F A J j ray q := by
  have hfirst := globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF j
  have hrow := globalPooledRowScale_pos K ell B F hK hell hB hF j
  have hrad := globalBinRadial_pos ell (globalPooledRowScale K ell B F j) hell hrow j
  have hcol := globalPooledColumnScale_pos ell hell j
  have hlab := (zero_lt_one.trans_le (globalPooledLabelScale_ge_one j)).le
  have h0 := (globalLogRep_pos j 0).le
  have h1 := (globalLogRep_pos j 1).le
  have h2 := (globalLogRep_pos j 2).le
  have h3 := (globalLogRep_pos j 3).le
  unfold globalDescentWeight globalPooledOuterBound
  positivity

theorem globalPositiveBin_transfer (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ i,0 ≤ M i) (hV : ∀ i x,V i x ≠ 0 → |x| ≤ M i)
    (hVc : ∀ i,HasCompactSupport (V i)) (hVs : ∀ i,Continuous (V i)) (A J : ℕ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (θ₁ θ₂ K ell B F : ℝ) (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex)
      (pool : Finset ι) (Ψ : O →* ℂ) (m : O),
      0 < K → 0 < ell → 0 < B → 0 < F → (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,x.source.frequency ≠ 0) →
      globalBinFirstCoefficient K ell B F j *
      ‖∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        globalArithmeticBinSource p hp hcop hg s side q j pool Ψ m ray
          (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂)
          W V ell (globalPooledRowScale K ell B F j)‖ ≤
      ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        globalDescentWeight C ε θ₁ θ₂ K ell B F A J j ray q *
        (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
          (fixedTripleMask m q) (globalArithmeticTargets p s side q j) (V 5) (V 6)
          (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J /
          (globalPooledColumnScale ell j*globalPooledLabelScale j)) := by
  obtain ⟨C,hC,htrans⟩ := full_uniform_globalArithmeticBin_twisted_transfer ε hε A₁ A₂ W V M hM hV hVc hVs A J
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hcop hg hinj hc θ₁ θ₂ K ell B F s side j pool Ψ m hK hell hB hF hΨ hs hk
  have hy := globalPooledRowScale_pos K ell B F hK hell hB hF j
  have hfirst := globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF j
  have hmass : globalPooledColumnScale ell j*globalPooledLabelScale j ≠ 0 :=
    (mul_pos (globalPooledColumnScale_pos ell hell j) (zero_lt_one.trans_le (globalPooledLabelScale_ge_one j))).ne'
  calc
    _ ≤ globalBinFirstCoefficient K ell B F j *
        ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        ‖globalArithmeticBinSource p hp hcop hg s side q j pool Ψ m ray
          (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂)
          W V ell (globalPooledRowScale K ell B F j)‖ := by
      apply mul_le_mul_of_nonneg_left _ hfirst
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro ray hray
      exact norm_sum_le _ _
    _ = ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        globalBinFirstCoefficient K ell B F j *
        ‖globalArithmeticBinSource p hp hcop hg s side q j pool Ψ m ray
          (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂)
          W V ell (globalPooledRowScale K ell B F j)‖ := by simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro ray hray
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨x,hx,hqx⟩ := Finset.mem_image.mp hq
      have hq0 : q.1 ≠ ⊥ := by
        rw [← hqx]
        exact (globalSecondFixedTriple_nonzero p hp x).1
      have ht := htrans p hp hcop hg hinj hc θ₁ θ₂ s side q j pool Ψ m ray ell
        (globalPooledRowScale K ell B F j) hell hy hq0 hΨ hs hk
      have ht' := mul_le_mul_of_nonneg_left ht hfirst
      apply ht'.trans_eq
      have hc0 := (globalPooledColumnScale_pos ell hell j).ne'
      have hl0 := (zero_lt_one.trans_le (globalPooledLabelScale_ge_one j)).ne'
      unfold globalDescentWeight
      field_simp

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem globalBinTriples_label_bound (B : ℝ) (hB : 0 < B) (side : Bool)
    (s : Finset (GlobalSecondData ι)) (j : GlobalLogIndex)
    (hk : ∀ x∈s,x.source.frequency ≠ 0)
    (hb₁ : ∀ x∈s,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ∀ x∈s,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (q : Ideal O × Ideal O × Ideal O) (hq : q∈globalBinTriples p s side j) :
    (Ideal.absNorm q.1 : ℝ) ≤ B*(Real.sqrt (globalLogRep j 9)*Real.exp 1)/globalLogRep j 4 := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hxs,hj⟩ := Finset.mem_filter.mp hx
  have h := (globalBin_triple_bounds p hp B hB side x (hk x hxs) (hb₁ x hxs) (hb₂ x hxs)).1
  rwa [hj] at h

include hp in

theorem globalDescentWeight_mass (C ε θ₁ θ₂ K ell B F : ℝ) (A J : ℕ)
    (hC : 0 ≤ C) (hε : 0 < ε) (hK : 0 < K) (hell : 0 < ell) (hB : 0 < B) (hF : 0 < F)
    (side : Bool) (s : Finset (GlobalSecondData ι)) (j : GlobalLogIndex)
    (hk : ∀ x∈s,x.source.frequency ≠ 0)
    (hb₁ : ∀ x∈s,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ∀ x∈s,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    (∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
      globalDescentWeight C ε θ₁ θ₂ K ell B F A J j ray q *
        (globalPooledColumnScale ell j*globalPooledLabelScale j)) ≤
    (C*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2)*(globalBinLossScale B j)^ε /
      (1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^A) *
      (128^3*(Real.exp 1)^18*(512*32^2))*((ell*B^3)*F) := by
  let Mchild := globalPooledColumnScale ell j*globalPooledLabelScale j
  let D := C*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2)*(globalBinLossScale B j)^ε /
      (1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^A
  have hmass : 0 < Mchild := mul_pos (globalPooledColumnScale_pos ell hell j)
    (zero_lt_one.trans_le (globalPooledLabelScale_ge_one j))
  have hY := globalPooledRowScale_pos K ell B F hK hell hB hF j
  have hR := globalBinRadial_pos ell (globalPooledRowScale K ell B F j) hell hY j
  have hfirst := globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF j
  have hL : 0 < globalPooledLabelScale j := zero_lt_one.trans_le (globalPooledLabelScale_ge_one j)
  have h0 := (globalLogRep_pos j 0).le
  have h1 := (globalLogRep_pos j 1).le
  have h2 := (globalLogRep_pos j 2).le
  have h3 := (globalLogRep_pos j 3).le
  have h4 := (globalLogRep_pos j 4).le
  have hD : 0 ≤ D := by unfold D globalBinLossScale;positivity
  have hcount : ((globalBinTriples p s side j).card : ℝ) ≤ 128^3*(Real.exp 1)^3*globalBinTripleRange B j := by
    apply globalBin_triple_count p hp B hB side (globalLogSector p s side j) j
    · intro x hx;exact (Finset.mem_filter.mp hx).2
    · intro x hx;exact hk x (Finset.mem_filter.mp hx).1
    · intro x hx;exact hb₁ x (Finset.mem_filter.mp hx).1
    · intro x hx;exact hb₂ x (Finset.mem_filter.mp hx).1
  have hterm (ray : SecondRayIndex) :
      (∑ q∈globalBinTriples p s side j,globalDescentWeight C ε θ₁ θ₂ K ell B F A J j ray q*Mchild) ≤
      D*(128^3*(Real.exp 1)^18*((ell*B^3)*F))*‖secondRayCoefficient ray‖ := by
    have ho : 0 ≤ globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j := by
      unfold globalPooledOuterBound;positivity
    calc
      _ ≤ ∑ q∈globalBinTriples p s side j,
          D*globalBinFirstCoefficient K ell B F j*globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j*Mchild^2 := by
        apply Finset.sum_le_sum
        intro q hq
        have hloss : (globalPooledLabelScale j*Ideal.absNorm q.1)^ε ≤ (globalBinLossScale B j)^ε :=
          Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left
            (globalBinTriples_label_bound p hp B hB side s j hk hb₁ hb₂ q hq) hL.le) hε.le
        unfold globalDescentWeight D
        calc
          _ ≤ C*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2)*globalBinFirstCoefficient K ell B F j *
              globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j *
              (globalBinLossScale B j)^ε /(1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^A *Mchild*Mchild := by
                gcongr
          _ = _ := by ring
      _ = ((globalBinTriples p s side j).card : ℝ)*
          (D*globalBinFirstCoefficient K ell B F j*globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j*Mchild^2) := by simp
      _ ≤ (128^3*(Real.exp 1)^3*globalBinTripleRange B j)*
          (D*globalBinFirstCoefficient K ell B F j*globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j*Mchild^2) := by
        gcongr
      _ = D*(globalBinChildCharge B F j*Mchild)*‖secondRayCoefficient ray‖ := by
        have hc := globalBin_complete_cost K ell B F hK hell hB hF j ray
        change globalBinFirstCoefficient K ell B F j * _ * Mchild * _ = _ at hc
        calc
          _ = D*(globalBinFirstCoefficient K ell B F j *
              globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j *Mchild *
              (128^3*(Real.exp 1)^3*globalBinTripleRange B j))*Mchild := by ring
          _ = _ := by rw [hc];ring
      _ = _ := by rw [show globalBinChildCharge B F j*Mchild=128^3*(Real.exp 1)^18*((ell*B^3)*F) from globalBin_mass_balance ell B F hB hF j]
  calc
    _ ≤ ∑ ray : SecondRayIndex,D*(128^3*(Real.exp 1)^18*((ell*B^3)*F))*‖secondRayCoefficient ray‖ :=
      Finset.sum_le_sum (fun ray _ => hterm ray)
    _ = D*(128^3*(Real.exp 1)^18*((ell*B^3)*F))*(∑ ray : SecondRayIndex,‖secondRayCoefficient ray‖) := by rw [Finset.mul_sum]
    _ ≤ D*(128^3*(Real.exp 1)^18*((ell*B^3)*F))*(512*32^2) := by
      apply mul_le_mul_of_nonneg_left secondRayCoefficient_mass
      positivity
    _ = _ := by dsimp only [D];ring

end SecondPassArithmetic

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix

namespace CubicEisenstein

def matrixGram (g : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ :=
  (g : Matrix (Fin 2) (Fin 2) ℂ)*star (g : Matrix (Fin 2) (Fin 2) ℂ)

lemma matrixGram_right_unitary (g k : SL(2,ℂ)) (hk : k∈compactSubgroup) :
    matrixGram (g*k)=matrixGram g := by
  have hku : (k : Matrix (Fin 2) (Fin 2) ℂ)*star (k : Matrix (Fin 2) (Fin 2) ℂ)=1 :=
    Matrix.mem_unitaryGroup_iff.mp hk
  unfold matrixGram
  simp only [Matrix.SpecialLinearGroup.coe_mul,star_mul]
  calc
    _ = (g : Matrix (Fin 2) (Fin 2) ℂ)*
        ((k : Matrix (Fin 2) (Fin 2) ℂ)*star (k : Matrix (Fin 2) (Fin 2) ℂ))*
        star (g : Matrix (Fin 2) (Fin 2) ℂ) := by noncomm_ring
    _ = _ := by rw [hku]; simp

def hyperbolicGram : HyperbolicSpace → Matrix (Fin 2) (Fin 2) ℂ :=
  Quotient.lift matrixGram (by
    intro g h hgh
    have hk : g⁻¹*h∈compactSubgroup := QuotientGroup.leftRel_apply.mp hgh
    have hh : h=g*(g⁻¹*h) := by group
    rw [hh]
    exact (matrixGram_right_unitary g (g⁻¹*h) hk).symm)

lemma hyperbolicGram_continuous : Continuous hyperbolicGram := by
  apply Continuous.quotient_lift
  exact continuous_complexSL_coe.mul continuous_complexSL_coe.star

lemma hyperbolicGram_injective : Function.Injective hyperbolicGram := by
  intro w w' hw
  induction w using Quotient.inductionOn with | _ g =>
    induction w' using Quotient.inductionOn with | _ h =>
      change matrixGram g=matrixGram h at hw
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      change (g⁻¹*h:SL(2,ℂ))∈compactSubgroup
      apply Matrix.mem_unitaryGroup_iff.mpr
      have hgi : ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*
          (g:Matrix (Fin 2) (Fin 2) ℂ)=1 :=
        congrArg (fun x : SL(2,ℂ) => (x:Matrix (Fin 2) (Fin 2) ℂ)) (inv_mul_cancel g)
      have hgis : star (g:Matrix (Fin 2) (Fin 2) ℂ)*
          star ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)=1 := by
        simpa only [star_mul,star_one] using congrArg star hgi
      simp only [Matrix.SpecialLinearGroup.coe_mul,star_mul]
      calc
        _ = ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*matrixGram h*
            star ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ) := by unfold matrixGram; noncomm_ring
        _ = ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*matrixGram g*
            star ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ) := by rw [hw]
        _ = (((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*(g:Matrix (Fin 2) (Fin 2) ℂ))*
            (star (g:Matrix (Fin 2) (Fin 2) ℂ)*star ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)) := by
          unfold matrixGram
          noncomm_ring
        _ = 1 := by rw [hgi,hgis]; simp

instance hyperbolicT2Space : T2Space HyperbolicSpace :=
  T2Space.of_injective_continuous hyperbolicGram_injective hyperbolicGram_continuous

def complexMatrixRow (g : SL(2,ℂ)) (i : Fin 2) : Fin 2 → ℂ := fun j => g i j

lemma complexMatrixRow_mul (g h : SL(2,ℂ)) (i : Fin 2) :
    complexMatrixRow (g*h) i=rowOperator h (complexMatrixRow g i) := by
  funext j
  simp only [complexMatrixRow,rowOperator_apply,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply,Matrix.vecMul,dotProduct]

def matrixFrobenius (g : SL(2,ℂ)) : ℝ :=
  rowEnergy (complexMatrixRow g 0)+rowEnergy (complexMatrixRow g 1)

lemma matrixFrobenius_right_unitary (g k : SL(2,ℂ)) (hk : k∈compactSubgroup) :
    matrixFrobenius (g*k)=matrixFrobenius g := by
  simp only [matrixFrobenius,complexMatrixRow_mul,rowEnergy_unitary k hk]

def hyperbolicFrobenius : HyperbolicSpace → ℝ :=
  Quotient.lift matrixFrobenius (by
    intro g h hgh
    have hk : g⁻¹*h∈compactSubgroup := QuotientGroup.leftRel_apply.mp hgh
    have hh : h=g*(g⁻¹*h) := by group
    rw [hh]
    exact (matrixFrobenius_right_unitary g (g⁻¹*h) hk).symm)

lemma matrixFrobenius_continuous : Continuous matrixFrobenius := by
  have he (i j : Fin 2) : Continuous (fun g : SL(2,ℂ) => g i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_complexSL_coe)
  unfold matrixFrobenius rowEnergy complexMatrixRow
  exact ((he 0 0).norm.pow 2 |>.add ((he 0 1).norm.pow 2)).add
    ((he 1 0).norm.pow 2 |>.add ((he 1 1).norm.pow 2))

lemma hyperbolicFrobenius_continuous : Continuous hyperbolicFrobenius :=
  matrixFrobenius_continuous.quotient_lift _

end CubicEisenstein

end

end OAI
