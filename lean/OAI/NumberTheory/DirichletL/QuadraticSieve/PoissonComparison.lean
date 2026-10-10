import OAI.NumberTheory.DirichletL.CubicSieve.ScaleCaps

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

section

theorem hasSieveExponent_one_of_approximation
    (happrox : ∀ η : ℝ, 0<η → ∃ α : ℝ, α≤1+η ∧ HasSieveExponent α) :
    HasSieveExponent 1 := by
  intro ε hε
  have he : 0<ε/2 := by positivity
  obtain ⟨α,hα,h⟩ := happrox (ε/2) he
  obtain ⟨C,hC,hbound⟩ := h (ε/2) he
  refine ⟨C,hC,?_⟩
  intro M N hM hN
  have hM0 : 0≤M := by linarith
  have hN0 : 0<N := by linarith
  have hMN : 1≤M*N := by nlinarith
  have hNmn : N≤M*N := by nlinarith
  have hQ : 1≤(M*N)^(ε/2) := Real.one_le_rpow hMN he.le
  have hnα : N^α ≤ (M*N)^(ε/2)*N := by
    calc
      _ ≤ N^(1+ε/2) := Real.rpow_le_rpow_of_exponent_le hN hα
      _ = N*N^(ε/2) := by rw [Real.rpow_add hN0,Real.rpow_one]
      _ ≤ N*(M*N)^(ε/2) := by gcongr
      _ = _ := mul_comm _ _
  have hsum : M+N^α ≤ (M*N)^(ε/2)*(M+N) := by
    nlinarith [mul_le_mul_of_nonneg_right hQ hM0]
  calc
    _ ≤ C*(M*N)^(ε/2)*(M+N^α) := hbound M N hM hN
    _ ≤ C*(M*N)^(ε/2)*((M*N)^(ε/2)*(M+N)) := by gcongr
    _ = C*(M*N)^ε*(M+N^(1:ℝ)) := by
      rw [Real.rpow_one]
      have hp : (M*N)^(ε/2)*(M*N)^(ε/2) = (M*N)^ε := by
        rw [← Real.rpow_add (by positivity : 0<M*N)]
        congr 1
        ring
      calc
        _ = C*((M*N)^(ε/2)*(M*N)^(ε/2))*(M+N) := by ring
        _ = _ := by rw [hp]

def bootstrapExponent (n : ℕ) : ℝ := 1+1/((n:ℝ)+1)

theorem bootstrapExponent_gt_one (n : ℕ) : 1<bootstrapExponent n := by
  unfold bootstrapExponent
  have h : (0:ℝ)<1/((n:ℝ)+1) := by positivity
  linarith

theorem bootstrapExponent_le_two (n : ℕ) : bootstrapExponent n≤2 := by
  have h : 1/((n:ℝ)+1)≤(1:ℝ) := by
    apply (div_le_one (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  unfold bootstrapExponent
  linarith

theorem bootstrapExponent_step (n : ℕ) :
    bootstrapExponent (n+1) = 2-1/bootstrapExponent n := by
  unfold bootstrapExponent
  push_cast
  field_simp
  ring

theorem hasSieveExponent_one_of_improvement
    (himprove : ∀ α : ℝ, 1<α → α≤2 → HasSieveExponent α → HasSieveExponent (2-1/α)) :
    HasSieveExponent 1 := by
  have hn : ∀ n : ℕ, HasSieveExponent (bootstrapExponent n) := by
    intro n
    induction n with
    | zero => norm_num [bootstrapExponent]; exact hasSieveExponent_two
    | succ n ih =>
      rw [bootstrapExponent_step]
      exact himprove _ (bootstrapExponent_gt_one n) (bootstrapExponent_le_two n) ih
  apply hasSieveExponent_one_of_approximation
  intro η hη
  obtain ⟨n,hnη⟩ := exists_nat_one_div_lt hη
  refine ⟨bootstrapExponent n,?_,hn n⟩
  unfold bootstrapExponent
  linarith

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

def divisorTwist {n : Type} (cols : n → Ideal O) (a : n → ℂ) (q : Ideal O) : n → ℂ :=
  fun j => a j*quadraticRow (cols j) (idealGenerator q)

def centeredRetainedDual {n : Type} [Fintype n] [DecidableEq n]
    (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ) (M K : ℝ) (q : Ideal O) : ℂ :=
  (6:ℂ)*retainedDualPrincipalSum (quadraticTransformedSquareProfile W)
    (fun I : squarefreeIdealRange K => I.val) cols (divisorTwist cols a q) M (Ideal.absNorm q:ℝ) -
  paperRadialFourier (quadraticTransformedSquareProfile W) 0 *
    unrestrictedPrincipalDensity (fun I : squarefreeIdealRange K => I.val) cols cols
      (divisorTwist cols a q) (divisorTwist cols a q) (M/(Ideal.absNorm q:ℝ))

def centeredMaskedSource {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ) (M K : ℝ) : ℂ :=
  maskedPrincipalSourceSum G (quadraticSquareProfile W)
    (fun I : coprimeSquarefreeRange G K => I.val) cols a M -
  paperRadialFourier (quadraticSquareProfile W) 0 *
    maskedSourceDensity G (fun I : coprimeSquarefreeRange G K => I.val) cols a M

def maskedPoissonDifference {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ) (M K : ℝ) : ℂ :=
  maskedDualFamily G cols a W M - (6:ℂ)⁻¹ *
    maskedPrincipalSourceSum G (quadraticSquareProfile W)
      (fun I : coprimeSquarefreeRange G K => I.val) cols a M

lemma finite_centering_identity {ι : Type*} (S : Finset ι) (w R D : ι → ℂ) (c h : ℂ) :
    (∑ q∈S, w q*(c*R q-h*D q)) = c*(∑ q∈S,w q*R q)-h*(∑ q∈S,w q*D q) := by
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  ring

theorem maskedPoissonDifference_centered {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (hG : G≠0) (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ)
    (M K : ℝ) (hM : 0<M) (hcols : ∀ j, Admissible (cols j))
    (hray : ∀ j k, columnRay (cols j)=columnRay (cols k))
    (hGc : ∀ j, IsCoprime G (cols j)) (hbad : ∀ P∈fixedBadPrimes, P∣G) :
    (6:ℂ)*maskedPoissonDifference G W cols a M K =
      (∑ q∈idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q) +
      (6:ℂ)*maskedDualTailFamily G cols a W M K - centeredMaskedSource G W cols a M K +
      paperRadialFourier (quadraticSquareProfile W) 0 *
        ((Real.sqrt M:ℂ)*actualPrincipalDifference cols (densityColumn cols a) G K) := by
  rw [←actual_source_dual_density_cancellation cols a G hG M K hM.le hcols hray hGc hbad]
  unfold maskedPoissonDifference centeredRetainedDual centeredMaskedSource divisorTwist
  rw [maskedDualFamily_retained G hG cols a W M K hM hcols hray]
  simp only [quadraticSquareProfile_principal_equal]
  rw [finite_centering_identity]
  ring

theorem maskedPoissonDifference_norm_le {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (hG : G≠0) (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ)
    (M K : ℝ) (hM : 0<M) (hcols : ∀ j, Admissible (cols j))
    (hray : ∀ j k, columnRay (cols j)=columnRay (cols k))
    (hGc : ∀ j, IsCoprime G (cols j)) (hbad : ∀ P∈fixedBadPrimes, P∣G) :
    ‖(6:ℂ)*maskedPoissonDifference G W cols a M K‖ ≤
      (∑ q∈idealDivisors G, ‖centeredRetainedDual W cols a M K q‖) +
      6*‖maskedDualTailFamily G cols a W M K‖ + ‖centeredMaskedSource G W cols a M K‖ +
      ‖paperRadialFourier (quadraticSquareProfile W) 0‖ *
        ‖(Real.sqrt M:ℂ)*actualPrincipalDifference cols (densityColumn cols a) G K‖ := by
  rw [maskedPoissonDifference_centered G hG W cols a M K hM hcols hray hGc hbad]
  have hs : ‖∑ q∈idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q‖ ≤
      ∑ q∈idealDivisors G, ‖centeredRetainedDual W cols a M K q‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro q hq
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (QuadraticInitialBound.norm_ideal_moebius_le_one q)
  calc
    _ ≤ (‖∑ q∈idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q‖ +
        ‖(6:ℂ)*maskedDualTailFamily G cols a W M K‖) + ‖centeredMaskedSource G W cols a M K‖ +
        ‖paperRadialFourier (quadraticSquareProfile W) 0 *
          ((Real.sqrt M:ℂ)*actualPrincipalDifference cols (densityColumn cols a) G K)‖ := by
      have h1 := norm_add_le
        ((∑ q∈idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q) +
          (6:ℂ)*maskedDualTailFamily G cols a W M K - centeredMaskedSource G W cols a M K)
        (paperRadialFourier (quadraticSquareProfile W) 0 *
          ((Real.sqrt M:ℂ)*actualPrincipalDifference cols (densityColumn cols a) G K))
      have h2 := norm_sub_le
        ((∑ q∈idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q) +
          (6:ℂ)*maskedDualTailFamily G cols a W M K) (centeredMaskedSource G W cols a M K)
      have h3 := norm_add_le
        (∑ q∈idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q)
        ((6:ℂ)*maskedDualTailFamily G cols a W M K)
      linarith
    _ ≤ _ := by
      simp only [norm_mul]
      norm_num
      gcongr

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
open IdealCoprimeSieveOperator

theorem divisorTwist_norm_le {n : Type} (cols : n → Ideal O) (a : n → ℂ)
    (q : Ideal O) (j : n) : ‖divisorTwist cols a q j‖≤‖a j‖ := by
  rw [divisorTwist,norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)

theorem retainedDualMajorant_coefficient_scale_le {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (hC : 0≤C) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (B N M F T : ℝ) (a a' : n → ℂ) (W : 𝓢(ℝ,ℂ))
    (hB : 0≤B) (hN : 0<N) (hM : 0≤M) (hF : 1≤F) (hT : 0≤T)
    (ha : ∀j, ‖a' j‖≤‖a j‖) :
    retainedDualMajorant s C l hexp deltaLoss hδ ε hε B N M F T a' W ≤
      retainedDualMajorant s C l hexp deltaLoss hδ ε hε B N M 1 T a W := by
  have he := divisorEnergyFactor_mono_coefficients ε hε N a a' a a' ha ha
  have he0 := divisorEnergyFactor_nonneg ε hε N a' a'
  have he1 := divisorEnergyFactor_nonneg ε hε N a a
  have hea : (∑j, ‖a' j‖^2)≤∑j, ‖a j‖^2 :=
    Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (ha j) 2)
  have hs := (supportConstant_pos ε hε).le
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  have hlat := nonzeroLatticeEnvelopeConstant_nonneg
  have hW := dualMiddleDecayConstant_nonneg W
  have hF0 : 0<F := by linarith
  have hMF : M/F≤M := div_le_self hM hF
  have hNF : N≤F*N := by nlinarith
  have hMN : 2*M/(F*N)≤2*M/N :=
    div_le_div_of_nonneg_left (by positivity) hN hNF
  unfold retainedDualMajorant smallPrincipalMajorant dualMiddleMajorant
  simp only [div_one,one_mul]
  gcongr

theorem centeredRetainedDual_sum_bound (l : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] {α : ℝ} (hexp : HasSieveExponent α), 1/2≤α →
      ∀ (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) (G : Ideal O), G≠0 →
      ∀ (K N M T : ℝ), 1≤K → 1≤N → 0<M → 4≤T →
      ∀ (cols : n → Ideal O), Function.Injective cols →
        (∀j, Admissible (cols j) ∧ N/2≤(Ideal.absNorm (cols j):ℝ) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
        (∀j k, columnRay (cols j)=columnRay (cols k)) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)),
        (∑q∈idealDivisors G, ‖centeredRetainedDual W cols a M K q‖) ≤
          (idealDivisors G).card*(columnDyadicLength K+1:ℕ)*
            retainedDualMajorant s C l hexp deltaLoss hδ ε hε (2*K) N M 1 T a (quadraticTransformedSquareProfile W) := by
  obtain ⟨s,C,hC,hbound⟩ := retained_dual_principal_global l
  refine ⟨s,C,hC,?_⟩
  intro n _ _ α hexp hα deltaLoss hδ ε hε G hG K N M T hK hN hM hT cols hc hcols hray a W
  classical
  have hqbound (q : Ideal O) (hq : q∈idealDivisors G) :
      ‖centeredRetainedDual W cols a M K q‖ ≤
        (columnDyadicLength K+1:ℕ)*
          retainedDualMajorant s C l hexp deltaLoss hδ ε hε (2*K) N M 1 T a (quadraticTransformedSquareProfile W) := by
    have hqd := (mem_idealDivisors hG).mp hq
    have hq0 : q≠0 := by intro hz; rw [hz,zero_dvd_iff] at hqd; exact hG hqd
    have hq1 : 1≤(Ideal.absNorm q:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hq0 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hh := hbound hexp hα deltaLoss hδ ε hε K N M (Ideal.absNorm q:ℝ) T hK hN hM
      (by linarith) hT cols hc hcols hray (divisorTwist cols a q) (quadraticTransformedSquareProfile W)
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact retainedDualMajorant_coefficient_scale_le s C hC.le l hexp deltaLoss hδ ε hε
      (2*K) N M (Ideal.absNorm q:ℝ) T a (divisorTwist cols a q) (quadraticTransformedSquareProfile W)
      (by linarith) (by linarith) hM.le hq1 (by linarith) (divisorTwist_norm_le cols a q)
  calc
    _ ≤ ∑_q∈idealDivisors G, (columnDyadicLength K+1:ℕ)*
        retainedDualMajorant s C l hexp deltaLoss hδ ε hε (2*K) N M 1 T a (quadraticTransformedSquareProfile W) :=
      Finset.sum_le_sum hqbound
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

end

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
open IdealCoprimeSieveOperator

def poissonComparisonMajorant {n : Type} [Fintype n]
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ) (l A : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε)
    (G : Ideal O) (K N M T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  (idealDivisors G).card*(columnDyadicLength K+1:ℕ)*
    retainedDualMajorant sD CD l hexp deltaLoss hδ ε hε (2*K) N M 1 T a (quadraticTransformedSquareProfile W) +
  6*(256*M*(idealDivisors G).card*
    ((CT*sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
      ((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*
        (1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A))*∑j, ‖a j‖^2) +
  (columnDyadicLength K+1:ℕ)*
    sourcePrincipalMajorant sS CS l hexp deltaLoss hδ ε hε G (2*K) N M T a (quadraticSquareProfile W) +
  ‖paperRadialFourier (quadraticSquareProfile W) 0‖ *
    (((idealDivisors G).card:ℝ)^2*(supportConstant ε hε*N^ε)*CP*(K*N)^deltaLoss*
      (Real.sqrt (M/K)*N+Real.sqrt M*K^(α-1/2))*∑j, ‖a j‖^2)

theorem HasSieveExponent.masked_poisson_complete {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2≤α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (l A : ℕ) :
    ∃ (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ),
      0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CP ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] (ε : ℝ) (hε : 0<ε)
        (G : Ideal O), Squarefree G → (∀P∈fixedBadPrimes,P∣G) →
      ∀ (K N M T : ℝ), 1≤K → 1≤N → 1≤M → 4≤T →
      ∀ (cols : n → Ideal O), Function.Injective cols →
        (∀j, Admissible (cols j) ∧ N/2≤(Ideal.absNorm (cols j):ℝ) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
        (∀j k, columnRay (cols j)=columnRay (cols k)) → (∀j, IsCoprime G (cols j)) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)), W 0=0 →
        ‖(6:ℂ)*maskedPoissonDifference G W cols a M K‖ ≤
          poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε G K N M T a W := by
  obtain ⟨sD,CD,hCD,hdual⟩ := centeredRetainedDual_sum_bound l
  obtain ⟨sS,CS,hCS,hsource⟩ := masked_source_principal_global l
  obtain ⟨sT,CT,hCT,htail⟩ := maskedDualTailFamily_bound A
  obtain ⟨CP,hCP,hprincipal⟩ := hexp.actual_principal_difference deltaLoss hδ
  refine ⟨sD,sS,sT,CD,CS,CT,CP,hCD,hCS,hCT,hCP,?_⟩
  intro n _ _ ε hε G hG hbad K N M T hK hN hM hT cols hc hcols hray hGc a W hW
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hcols0 : ∀j, Admissible (cols j) := fun j => (hcols j).1
  have hcolsu : ∀j, Admissible (cols j) ∧ (Ideal.absNorm (cols j):ℝ)≤N :=
    fun j => ⟨(hcols j).1,(hcols j).2.2⟩
  have hd := hdual hexp hα deltaLoss hδ ε hε G hG.ne_zero K N M T hK hN hM0 hT cols hc hcols hray a W
  have hs := hsource hexp hα deltaLoss hδ ε hε G hG K N M T hK hN hM0 hT
    (coprimeSquarefreeRange G K)
    (fun I hI => mem_idealRange.mp (coprimeSquarefreeRange_subset_idealRange G hbad K hI))
    cols hc hcolsu hGc a (quadraticSquareProfile W)
    (by simpa only [quadraticSquareProfile_apply,zero_pow (by decide : 2≠0)] using hW)
  have ht := htail G cols a W M N K hG.ne_zero hc hM0 hN (by linarith)
    (fun j => ⟨(hcols j).1.1,(hcols j).2⟩)
  have hp := hprincipal cols hc M N K hM hN hK hcolsu hray
    (densityColumn cols a) G hG hbad ε hε
  have he := densityColumn_energy_le cols a (fun j => (hcols j).1.1)
  have hsupp := (supportConstant_pos ε hε).le
  have hp' : ‖(Real.sqrt M:ℂ)*actualPrincipalDifference cols (densityColumn cols a) G K‖ ≤
      ((idealDivisors G).card:ℝ)^2*(supportConstant ε hε*N^ε)*CP*(K*N)^deltaLoss*
        (Real.sqrt (M/K)*N+Real.sqrt M*K^(α-1/2))*∑j, ‖a j‖^2 := by
    apply hp.trans
    gcongr
  have hmain := maskedPoissonDifference_norm_le G hG.ne_zero W cols a M K hM0 hcols0 hray hGc hbad
  apply hmain.trans
  change _ ≤ _+_+_+_
  have hs' : ‖centeredMaskedSource G W cols a M K‖ ≤
      (columnDyadicLength K+1:ℕ)*sourcePrincipalMajorant sS CS l hexp deltaLoss hδ ε hε G (2*K) N M T a
        (quadraticSquareProfile W) := hs
  exact add_le_add (add_le_add (add_le_add hd (mul_le_mul_of_nonneg_left ht (by norm_num))) hs')
    (mul_le_mul_of_nonneg_left hp' (norm_nonneg _))

end
section

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum
open DivisorBlockCauchy

theorem gcdRaySupport_energy_eq {n : Type} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) :
    (∑j : gcdRaySupport cols a D c, ‖a j.val‖^2) =
      ∑j, if D∣cols j ∧ columnRay (cols j)=c then ‖a j‖^2 else 0 := by
  classical
  rw [Finset.sum_coe_sort (gcdRaySupport cols a D c) (fun j => ‖a j‖^2)]
  simp only [gcdRaySupport,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hz : a j=0
  · simp only [hz,norm_zero,ne_eq,not_true_eq_false,and_false,ite_self,zero_pow (by decide : 2≠0)]
  · simp only [hz,ne_eq,not_false_eq_true,and_true]

theorem gcdRaySupport_energy_ray_sum {n : Type} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (D : Ideal O) :
    (∑c : EisensteinEPrimaryPhase.Coord, ∑j : gcdRaySupport cols a D c, ‖a j.val‖^2) =
      ∑j, ‖if D∣cols j then a j else 0‖^2 := by
  classical
  simp_rw [gcdRaySupport_energy_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hd : D∣cols j
  · simp only [hd,true_and,ite_true]
    rw [Finset.sum_eq_single (columnRay (cols j))]
    · simp only [ite_true]
    · intro c hc hne
      exact ite_eq_right (Ne.symm hne)
    · simp
  · simp only [hd,false_and,ite_false,Finset.sum_const_zero,norm_zero,zero_pow (by decide : 2≠0)]

theorem gcdRaySupport_energy_divisor_sum {n : Type} [Fintype n]
    (ε : ℝ) (hε : 0<ε) (S : Finset (Ideal O)) (cols : n → Ideal O)
    (hcols : ∀j, cols j≠0) (a : n → ℂ) (X : ℝ)
    (hX : ∀j, a j≠0 → (Ideal.absNorm (cols j):ℝ)≤X) :
    (∑c : EisensteinEPrimaryPhase.Coord, ∑D∈S,
      ∑j : gcdRaySupport cols a D c, ‖a j.val‖^2) ≤
      (divisorConstant ε hε*X^ε)*∑j, ‖a j‖^2 := by
  classical
  rw [Finset.sum_comm]
  simp_rw [gcdRaySupport_energy_ray_sum]
  apply (divisor_mask_energy S cols hcols a).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hz : a j=0
  · simp only [hz,norm_zero,zero_pow (by decide : 2≠0),mul_zero,le_refl]
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply ((IdealDivisorBound.ideal_divisor_small_power ε hε).choose_spec.2 (cols j) (hcols j)).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (hX j hz) hε.le) (divisorConstant_pos ε hε).le

theorem gcdRaySupport_weighted_sum_bound {n : Type} [Fintype n]
    (ε : ℝ) (hε : 0<ε) (S : Finset (Ideal O)) (cols : n → Ideal O)
    (hcols : ∀j, cols j≠0) (a : n → ℂ) (X C : ℝ) (hC : 0≤C)
    (hX : ∀j, a j≠0 → (Ideal.absNorm (cols j):ℝ)≤X)
    (F : Ideal O → EisensteinEPrimaryPhase.Coord → ℝ)
    (hF : ∀D∈S, ∀c, F D c≤C*∑j : gcdRaySupport cols a D c, ‖a j.val‖^2) :
    (∑c : EisensteinEPrimaryPhase.Coord, ∑D∈S, F D c) ≤
      C*(divisorConstant ε hε*X^ε)*∑j, ‖a j‖^2 := by
  calc
    _ ≤ ∑c : EisensteinEPrimaryPhase.Coord, ∑D∈S,
        C*∑j : gcdRaySupport cols a D c, ‖a j.val‖^2 :=
      Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun D hD => hF D hD c))
    _ = C*(∑c : EisensteinEPrimaryPhase.Coord, ∑D∈S,
        ∑j : gcdRaySupport cols a D c, ‖a j.val‖^2) := by simp only [Finset.mul_sum]
    _ ≤ C*((divisorConstant ε hε*X^ε)*∑j, ‖a j‖^2) :=
      mul_le_mul_of_nonneg_left (gcdRaySupport_energy_divisor_sum ε hε S cols hcols a X hX) hC
    _ = _ := by ring

end

open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy

theorem divisorEnergyFactor_diagonal {n : Type*} [Fintype n]
    (ε : ℝ) (hε : 0<ε) (N : ℝ) (a : n → ℂ) :
    divisorEnergyFactor ε hε N a a =
      (256*(supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2)*∑j, ‖a j‖^2 := by
  unfold divisorEnergyFactor
  have hs : 0≤∑j, ‖a j‖^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [mul_assoc _ (Real.sqrt _) (Real.sqrt _),Real.mul_self_sqrt hs]

theorem poissonComparisonMajorant_energy_factor {n : Type} [Fintype n]
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ) (l A : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε)
    (G : Ideal O) (K N M T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) :
    poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε G K N M T a W =
      poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε G K N M T
        (fun _ : Unit => (1:ℂ)) W * ∑j, ‖a j‖^2 := by
  unfold poissonComparisonMajorant retainedDualMajorant sourcePrincipalMajorant
    smallPrincipalMajorant dualMiddleMajorant
  simp only [divisorEnergyFactor_diagonal,Fintype.sum_unique,norm_one,one_pow,mul_one]
  ring

end CanonicalQuadraticSieve

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalSecondOuterWeight (Ψ : O →* ℂ) (m : O) (z : SecondRayIndex)
    (ell Y : ℝ) (side : Bool) (x : GlobalSecondData ι) : ℂ :=
  let X := globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon
  let b0 := b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
  let c := secondBaseLabel p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor)
  (primeProductNorm p x.firstCommon : ℂ)⁻¹ *
    (secondNormalizedExpansionWeight p hp hcop hg Ψ (m*b0) c d z X Y x.source *
      (secondExpansionScale p X r (expansionSupportData x.common x.firstDivisor x.source) : ℂ)⁻¹)

theorem globalSecondOuterWeight_squarefree
    (Ψ : O →* ℂ) (m : O) (z : SecondRayIndex) (ell Y : ℝ) (side : Bool)
    (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (h : globalSecondOuterWeight p hp hcop hg Ψ m z ell Y side x ≠ 0) :
    Squarefree (SecondPassFiber.newLabel (globalSecondTuple p x)) := by
  apply actualSecondLabel_squarefree_of_weight p hp hcop hg x.cube.support x.common
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit hx.2.2.1 Ψ
    (m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor) z x.source hx.2.1
  intro hw
  unfold secondArithmeticWeight at hw
  rcases mul_eq_zero.mp hw with hA|hB
  · apply h
    simp only [globalSecondOuterWeight,secondNormalizedExpansionWeight,secondBaseLabel,hA,mul_zero,zero_mul]
  · apply h
    simp only [globalSecondOuterWeight,secondNormalizedExpansionWeight,secondBaseLabel,hB,mul_zero,zero_mul]

theorem globalSecondOuterWeight_norm_le
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (Ψ : O →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (z : SecondRayIndex)
    (ell Y : ℝ) (hell : 0 < ell) (hY : 0 ≤ Y) (side : Bool) (x : GlobalSecondData ι) :
    ‖globalSecondOuterWeight p hp hcop hg Ψ m z ell Y side x‖ ≤
      (Y*primeProductNorm p x.firstCommon*primeProductNorm p (x.source.sourceCommon\x.source.divisor)/
        (globalFirstColumnScale p ell x side)^2)*‖secondRayCoefficient z‖ := by
  have ht := FirstPassCubeLabels.primeProductNorm_pos p hp x.firstCommon
  have hX := globalFirstColumnScale_pos p hp ell hell x side
  have hh := secondNormalizedExpansionWeight_norm_le p hp hcop hg hinj hc x.common x.firstDivisor
    Ψ (m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)
    (secondBaseLabel p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor))
    z (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) Y (div_pos hX ht) hY x.source (hΨ _) (hΨ _)
  rw [primeSubsetGenerator_norm_eq_productNorm] at hh
  unfold globalSecondOuterWeight
  dsimp only
  rw [norm_mul,norm_inv,Complex.norm_of_nonneg ht.le]
  apply (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr ht.le)).trans_eq
  field_simp

def globalPooledOuterBound (z : SecondRayIndex) (ell Y : ℝ) (j : GlobalLogIndex) : ℝ :=
  (Y*(Real.exp 1)^6*globalLogRep j 2*globalLogRep j 3*(globalLogRep j 0)^2*(globalLogRep j 1)^2/ell^2)*
    ‖secondRayCoefficient z‖

theorem globalSecondOuterWeight_bin_bound
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (Ψ : O →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (z : SecondRayIndex)
    (ell Y : ℝ) (hell : 0 < ell) (hY : 0 ≤ Y) (side : Bool) (x : GlobalSecondData ι)
    (hk : x.source.frequency ≠ 0) :
    ‖globalSecondOuterWeight p hp hcop hg Ψ m z ell Y side x‖ ≤
      globalPooledOuterBound z ell Y (globalScaleIndex p side x) := by
  apply (globalSecondOuterWeight_norm_le p hp hcop hg hinj hc Ψ hΨ m z ell Y hell hY side x).trans
  let j := globalScaleIndex p side x
  have ha := (globalScaleIndex_bounds p hp side x hk 0).2
  have hc' := (globalScaleIndex_bounds p hp side x hk 1).2
  have ht := (globalScaleIndex_bounds p hp side x hk 2).2
  have hr := (globalScaleIndex_bounds p hp side x hk 3).2
  change primeProductNorm p (x.cube.sideDivisor side) ≤ globalLogRep j 0*Real.exp 1 at ha
  change primeProductNorm p x.common ≤ globalLogRep j 1*Real.exp 1 at hc'
  change primeProductNorm p x.firstCommon ≤ globalLogRep j 2*Real.exp 1 at ht
  change primeProductNorm p (x.source.sourceCommon\x.source.divisor) ≤ globalLogRep j 3*Real.exp 1 at hr
  have hn : Y*primeProductNorm p x.firstCommon*primeProductNorm p (x.source.sourceCommon\x.source.divisor)/
      (globalFirstColumnScale p ell x side)^2 =
      Y*primeProductNorm p x.firstCommon*primeProductNorm p (x.source.sourceCommon\x.source.divisor)*
        (primeProductNorm p (x.cube.sideDivisor side))^2*(primeProductNorm p x.common)^2/ell^2 := by
    have hA := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.cube.sideDivisor side)).ne'
    have hC := (FirstPassCubeLabels.primeProductNorm_pos p hp x.common).ne'
    unfold globalFirstColumnScale
    field_simp

  rw [hn]
  have h0 := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.cube.sideDivisor side)).le
  have h1 := (FirstPassCubeLabels.primeProductNorm_pos p hp x.common).le
  have h2 := (FirstPassCubeLabels.primeProductNorm_pos p hp x.firstCommon).le
  have h3 := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.source.sourceCommon\x.source.divisor)).le
  have hr0 := (globalLogRep_pos j 0).le
  have hr1 := (globalLogRep_pos j 1).le
  have hr2 := (globalLogRep_pos j 2).le
  have hr3 := (globalLogRep_pos j 3).le
  calc
    _ ≤ (Y*(globalLogRep j 2*Real.exp 1)*(globalLogRep j 3*Real.exp 1)*
      (globalLogRep j 0*Real.exp 1)^2*(globalLogRep j 1*Real.exp 1)^2/ell^2)*‖secondRayCoefficient z‖ := by gcongr
    _ = _ := by unfold globalPooledOuterBound;ring

end SecondPassArithmetic

end

end OAI
