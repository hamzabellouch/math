import OAI.NumberTheory.DirichletL.QuadraticSieve.GlobalBinLoss

namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

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

section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy EisensteinSchwartzPoisson

theorem list_exists_positive_bound (xs : List ℝ) :
    ∃ H : ℝ, 1≤H ∧ ∀x∈xs, x≤H := by
  induction xs with
  | nil => exact ⟨1,le_rfl,by simp⟩
  | cons x xs ih =>
    obtain ⟨H,hH,hxs⟩ := ih
    refine ⟨max H x, hH.trans (le_max_left _ _), ?_⟩
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact le_max_right _ _
    · exact (hxs y hy).trans (le_max_left _ _)

def poissonPrimitiveConstants
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ)
    {α : ℝ} (hexp : HasSieveExponent α) (η : ℝ) (hη : 0<η)
    (D : ℝ) (W : 𝓢(ℝ,ℂ)) : List ℝ :=
  [divisorConstant η hη, 2+1/(η*Real.log 2), 256,
   supportConstant η hη, divisorExponentConstant hexp η hη,
   ‖paperRadialFourier (quadraticTransformedSquareProfile W) 0‖,
   ‖quadraticTransformedSquareProfile W 0‖,
   dualMiddleDecayConstant (quadraticTransformedSquareProfile W),
   ‖paperRadialFourier (quadraticSquareProfile W) 0‖,
   originalMiddleDecayConstant (quadraticSquareProfile W),
   nonzeroLatticeEnvelopeConstant, CD, CS, CT, CP,
   sD.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W),
   sS.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W),
   sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W, D^η]

theorem poissonPrimitiveConstants_nonneg
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ)
    (hCD : 0≤CD) (hCS : 0≤CS) (hCT : 0≤CT) (hCP : 0≤CP)
    {α : ℝ} (hexp : HasSieveExponent α) (η : ℝ) (hη : 0<η)
    (D : ℝ) (hD : 0≤D) (W : 𝓢(ℝ,ℂ)) :
    ∀x∈poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W, 0≤x := by
  intro x hx
  simp only [poissonPrimitiveConstants,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact (divisorConstant_pos η hη).le
  · have : 0<Real.log 2 := Real.log_pos (by norm_num); positivity
  · norm_num
  · exact (supportConstant_pos η hη).le
  · exact (divisorExponentConstant_pos hexp η hη).le
  · positivity
  · positivity
  · exact dualMiddleDecayConstant_nonneg _
  · positivity
  · exact originalMiddleDecayConstant_nonneg _
  · exact nonzeroLatticeEnvelopeConstant_nonneg
  · exact hCD
  · exact hCS
  · exact hCT
  · exact hCP
  · positivity
  · positivity
  · positivity
  · exact Real.rpow_nonneg hD _

theorem poissonUnitBudget_power_envelope
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ)
    (hCD : 0≤CD) (hCS : 0≤CS) (hCT : 0≤CT) (hCP : 0≤CP)
    {α : ℝ} (hexp : HasSieveExponent α) (η : ℝ) (hη : 0<η)
    (G : Ideal O) (hG : G≠0) (K N P D H : ℝ) (W : 𝓢(ℝ,ℂ))
    (hK : 1≤K) (hN : 1≤N) (hP : 1≤P) (hD : 1≤D) (hH : 1≤H)
    (hconst : ∀x∈poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W, x≤H)
    (hscales : ∀x∈([(Ideal.absNorm G:ℝ), K,N,(2*K)*N,N*N,
      (Ideal.absNorm G:ℝ)*(N*N),K*N] : List ℝ), 0≤x ∧ x≤D*P^4) :
    ∀x∈poissonUnitBudget sD sS sT CD CS CT CP hexp η hη η hη G K N W,
      0≤x ∧ x≤(H*P^(4*η))^8 := by
  let V := H*P^(4*η)
  have hP0 : 0<P := by linarith
  have hR : 1≤P^(4*η) := Real.one_le_rpow hP (by positivity)
  have hV : 1≤V := by dsimp [V]; nlinarith
  have hCV (x : ℝ)
      (hx : x∈poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W) :
      0≤x ∧ x≤V := by
    refine ⟨poissonPrimitiveConstants_nonneg sD sS sT CD CS CT CP hCD hCS hCT hCP
      hexp η hη D (by linarith) W x hx, ?_⟩
    have hh := hconst x hx
    dsimp [V]
    nlinarith
  have hpow (x : ℝ)
      (hx : x∈([(Ideal.absNorm G:ℝ),K,N,(2*K)*N,N*N,
        (Ideal.absNorm G:ℝ)*(N*N),K*N] : List ℝ)) : 0≤x^η ∧ x^η≤V := by
    have hx0 := (hscales x hx).1
    refine ⟨Real.rpow_nonneg hx0 _, ?_⟩
    have hDpow : D^η≤H := hconst _ (by simp [poissonPrimitiveConstants])
    calc
      _ ≤ (D*P^4)^η := Real.rpow_le_rpow hx0 (hscales x hx).2 hη.le
      _ = D^η*P^(4*η) := by
        rw [Real.mul_rpow (by linarith : 0≤D) (by positivity : 0≤P^4)]
        congr 1
        rw [←Real.rpow_natCast,←Real.rpow_mul hP0.le]
        norm_num
      _ ≤ V := mul_le_mul_of_nonneg_right hDpow (by positivity)
  let prims := poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W ++
    [(Ideal.absNorm G:ℝ)^η,K^η,N^η,((2*K)*N)^η,(N*N)^η,
      ((Ideal.absNorm G:ℝ)*(N*N))^η,(K*N)^η]
  have hprims : ∀x∈prims, 0≤x ∧ x≤V := by
    intro x hx
    simp only [prims,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with hx|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact hCV x hx
    all_goals exact hpow _ (by simp)
  have hp (xs : List ℝ) (hx : ∀x∈xs, x∈prims) (hn : xs.length≤8) : xs.prod≤V^8 :=
    list_prod_budget xs prims V hV hprims hx hn
  have hp1 (x : ℝ) (hx : x∈prims) : x≤V^8 := by
    simpa using hp [x] (by simpa using hx) (by simp)
  intro x hx
  simp only [poissonUnitBudget,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · refine ⟨by positivity, ?_⟩
    apply ((IdealDivisorBound.ideal_divisor_small_power η hη).choose_spec.2 G hG).trans
    have hh := hp [divisorConstant η hη,(Ideal.absNorm G:ℝ)^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · refine ⟨by positivity, ?_⟩
    apply (show (columnDyadicLength K+1:ℕ) ≤ (2+1/(η*Real.log 2))*K^η by
      simpa only [Nat.cast_add,Nat.cast_one] using columnDyadicLength_small_power η hη K hK).trans
    have hh := hp [2+1/(η*Real.log 2),K^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · refine ⟨by positivity, ?_⟩
    apply (show (columnDyadicLength N+1:ℕ) ≤ (2+1/(η*Real.log 2))*N^η by
      simpa only [Nat.cast_add,Nat.cast_one] using columnDyadicLength_small_power η hη N hN).trans
    have hh := hp [2+1/(η*Real.log 2),N^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [256,supportConstant η hη,divisorConstant η hη,N^η,N^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [divisorExponentConstant hexp η hη,((2*K)*N)^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [‖paperRadialFourier (quadraticTransformedSquareProfile W) 0‖] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [‖quadraticTransformedSquareProfile W 0‖] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · refine ⟨dualMiddleDecayConstant_nonneg _, ?_⟩
    have hh := hp [dualMiddleDecayConstant (quadraticTransformedSquareProfile W)] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [‖paperRadialFourier (quadraticSquareProfile W) 0‖] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · refine ⟨originalMiddleDecayConstant_nonneg _, ?_⟩
    have hh := hp [originalMiddleDecayConstant (quadraticSquareProfile W)] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · refine ⟨nonzeroLatticeEnvelopeConstant_nonneg, ?_⟩
    have hh := hp [nonzeroLatticeEnvelopeConstant] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [supportConstant η hη,(N*N)^η,CD,sD.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W)] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [supportConstant η hη,((Ideal.absNorm G:ℝ)*(N*N))^η,CS,sS.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [CT,sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [supportConstant η hη,N^η,CP,(K*N)^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh

end

section

theorem selectedPoisson_upper (C C1 M X η : ℝ)
    (hC : 4≤C) (hCC : C≤C1) (hM : 1≤M) (hX : 1≤X)
    (hη : 0≤η) (hη1 : η≤1) :
    4≤selectedPoissonT C M X η ∧
    (M*X)^η≤selectedPoissonT C M X η ∧
    selectedPoissonK C M X η≤C1*(M*X)^3 := by
  have hC10 : 0≤C1 := by linarith
  have hM0 : 0<M := by linarith
  have hX0 : 0<X := by linarith
  have hP : 1≤M*X := by nlinarith
  have hP0 : 0<M*X := by positivity
  have hR : 1≤(M*X)^η := Real.one_le_rpow hP hη
  have hT : 4≤selectedPoissonT C M X η := by dsimp [selectedPoissonT]; nlinarith
  refine ⟨hT,by dsimp [selectedPoissonT]; nlinarith,?_⟩
  have hXP : X≤M*X := by nlinarith
  have hfrac : X^2/M≤(M*X)^2 :=
    (div_le_self (sq_nonneg _) hM).trans (pow_le_pow_left₀ hX0.le hXP 2)
  have hrpow : (M*X)^η≤M*X := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP hη1
  calc
    selectedPoissonK C M X η = C*(M*X)^η*(X^2/M) := by
      unfold selectedPoissonK selectedPoissonT
      ring
    _ ≤ C1*(M*X)*(M*X)^2 := by gcongr
    _ = C1*(M*X)^3 := by ring

theorem poisson_seven_scale_bounds (g K N P B C1 : ℝ)
    (hP : 1≤P) (hB : 1≤B) (hC1 : 1≤C1)
    (hg0 : 0≤g) (hK0 : 0≤K) (hN0 : 0≤N)
    (hg : g≤B*P) (hK : K≤C1*P^3) (hN : N≤P) :
    ∀x∈([g,K,N,(2*K)*N,N*N,g*(N*N),K*N] : List ℝ),
      0≤x ∧ x≤(2*C1+B)*P^4 := by
  have hP0 : 0≤P := by linarith
  have hD : 1≤2*C1+B := by linarith
  have hp14 : P≤P^4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hP (show 1≤4 by omega)
  have hp24 : P^2≤P^4 := pow_le_pow_right₀ hP (by omega)
  have hp34 : P^3≤P^4 := pow_le_pow_right₀ hP (by omega)
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · refine ⟨hg0, hg.trans ?_⟩
    calc
      B*P ≤ B*P^4 := by gcongr
      _ ≤ (2*C1+B)*P^4 := by gcongr; linarith
  · refine ⟨hK0,hK.trans ?_⟩
    calc
      C1*P^3 ≤ C1*P^4 := by gcongr
      _ ≤ (2*C1+B)*P^4 := by gcongr; linarith
  · refine ⟨hN0,hN.trans (hp14.trans ?_)⟩
    nlinarith [show 0≤P^4 by positivity]
  · refine ⟨by positivity,?_⟩
    calc
      2*K*N ≤ 2*(C1*P^3)*P := by gcongr
      _ = (2*C1)*P^4 := by ring
      _ ≤ (2*C1+B)*P^4 := by gcongr; linarith
  · refine ⟨by positivity,?_⟩
    calc
      N*N ≤ P*P := by gcongr
      _ = P^2 := by ring
      _ ≤ P^4 := hp24
      _ ≤ (2*C1+B)*P^4 := by nlinarith [show 0≤P^4 by positivity]
  · refine ⟨by positivity,?_⟩
    calc
      g*(N*N) ≤ (B*P)*(P*P) := by gcongr
      _ = B*P^3 := by ring
      _ ≤ B*P^4 := by gcongr
      _ ≤ (2*C1+B)*P^4 := by gcongr; linarith
  · refine ⟨by positivity,?_⟩
    calc
      K*N ≤ (C1*P^3)*P := by gcongr
      _ = C1*P^4 := by ring
      _ ≤ (2*C1+B)*P^4 := by gcongr; linarith

theorem power_cutoff_dominates (P T η : ℝ) (l : ℕ)
    (hP : 1≤P) (hT : P^η≤T) (hpow : 4≤η*l) :
    P^4≤T^l := by
  have hp0 : 0<P := by linarith
  calc
    P^4 = P^(4:ℝ) := by rw [Real.rpow_ofNat]
    _ ≤ P^(η*l) := Real.rpow_le_rpow_of_exponent_le hP hpow
    _ = (P^η)^l := by rw [Real.rpow_mul hp0.le,Real.rpow_natCast]
    _ ≤ T^l := pow_le_pow_left₀ (Real.rpow_nonneg hp0.le _) hT l

theorem poisson_truncation_small (P T η K M N C1 : ℝ) (l : ℕ)
    (hP : 1≤P) (hT : P^η≤T) (hpow : 4≤η*l)
    (_hK : 0≤K) (hM : 0≤M) (hN : 0≤N) (hC1 : 0≤C1)
    (hKP : K≤C1*P^3) (hMP : M≤P) (hNP : N≤P) :
    K*M/T^l≤C1 ∧ K*N/T^l≤C1 := by
  have hp0 : 0<P := by linarith
  have htpos : 0<T := lt_of_lt_of_le (Real.rpow_pos_of_pos hp0 _) hT
  have hcut := power_cutoff_dominates P T η l hP hT hpow
  have hb (Y : ℝ) (hY : 0≤Y) (hYP : Y≤P) : K*Y/T^l≤C1 := by
    apply (div_le_iff₀ (pow_pos htpos _)).mpr
    calc
      K*Y ≤ (C1*P^3)*P := by gcongr
      _ = C1*P^4 := by ring
      _ ≤ C1*T^l := by gcongr
  exact ⟨hb M hM hMP,hb N hN hNP⟩

theorem poisson_tail_abstract (B P t K η M : ℝ) (A : ℕ)
    (hB : 1≤B) (hP : 1≤P) (hM : 0≤M)
    (ht : 1/(B*P^2)≤t) (hu : P^η≤1+t*K) (hA : 4≤η*A) :
    M/((min 1 t)^2*(1+t*K)^A)≤B^2*M := by
  have hB0 : 0<B := by linarith
  have hP0 : 0<P := by linarith
  have hBP : 1≤B*P^2 := by nlinarith [sq_nonneg (P-1)]
  have hinv : 1/(B*P^2)≤1 := (div_le_one (by positivity)).mpr hBP
  have htlo : 1/(B*P^2)≤min 1 t := le_min hinv ht
  have htpos : 0<min 1 t := lt_of_lt_of_le (by positivity) htlo
  have hup : 0<1+t*K := lt_of_lt_of_le (Real.rpow_pos_of_pos hP0 _) hu
  have hpow := power_cutoff_dominates P (1+t*K) η A hP hu hA
  have hprod : 1/B^2≤(min 1 t)^2*(1+t*K)^A := by
    calc
      1/B^2 = (1/(B*P^2))^2*P^4 := by field_simp
      _ ≤ (min 1 t)^2*(1+t*K)^A := by gcongr
  apply (div_le_iff₀ (by positivity : 0<(min 1 t)^2*(1+t*K)^A)).mpr
  have hh := mul_le_mul_of_nonneg_left hprod (show 0≤B^2*M by positivity)
  have he : (B^2*M)*(1/B^2)=M := by field_simp
  rw [he] at hh
  exact hh

theorem selectedPoisson_tail_shape (C B M X q η : ℝ) (A : ℕ)
    (hC : B≤C) (hB : 1≤B) (hM : 1≤M) (hX : 1≤X)
    (hq : 1≤q) (_hη : 0≤η) (hA : 4≤η*A) :
    M/((min 1 (M/((B*q)*(X/q)*(X/q))))^2*
      (1+(M/((B*q)*(X/q)*(X/q)))*selectedPoissonK C M X η)^A)≤B^2*M := by
  have hB0 : 0<B := by linarith
  have hM0 : 0<M := by linarith
  have hX0 : 0<X := by linarith
  have hq0 : 0<q := by linarith
  have hC0 : 0<C := by linarith
  have hP : 1≤M*X := by nlinarith
  have hXP : X≤M*X := by nlinarith
  have hMQ : 1≤M*q := by nlinarith
  have hEq : M/((B*q)*(X/q)*(X/q))=M*q/(B*X^2) := by field_simp
  have ht : 1/(B*(M*X)^2)≤M/((B*q)*(X/q)*(X/q)) := by
    rw [hEq]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    calc
      1*(B*X^2) ≤ B*(M*X)^2 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX0.le hXP 2) hB0.le
      _ ≤ (M*q)*(B*(M*X)^2) := by nlinarith [show 0≤B*(M*X)^2 by positivity]
  have hu : (M*X)^η≤1+(M/((B*q)*(X/q)*(X/q)))*selectedPoissonK C M X η := by
    rw [selectedPoisson_radial_identity C B M X q η hM0 hX0 hq0 hB0]
    have hp : 0≤(M*X)^η := Real.rpow_nonneg (by positivity) _
    have hb : (M*X)^η≤selectedPoissonT C M X η*q/B := by
      apply (le_div_iff₀ hB0).mpr
      dsimp [selectedPoissonT]
      calc
        (M*X)^η*B = B*(M*X)^η := by ring
        _ ≤ C*(M*X)^η := mul_le_mul_of_nonneg_right hC hp
        _ ≤ C*(M*X)^η*q := le_mul_of_one_le_right (by positivity) hq
    linarith
  exact poisson_tail_abstract B (M*X) _ _ η M A hB hP hM0.le ht hu hA

theorem selectedPoisson_principal_shape (C M X N η α : ℝ)
    (hC : 4≤C) (hM : 1≤M) (hX : 1≤X) (hN : 0≤N) (hNX : N≤X)
    (hη : 0≤η) (hα : 1/2≤α) :
    Real.sqrt (M/selectedPoissonK C M X η)*N+
      Real.sqrt M*(selectedPoissonK C M X η)^(α-1/2) ≤
    M+selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) := by
  have hM0 : 0<M := by linarith
  have hX0 : 0<X := by linarith
  have hP : 1≤M*X := by nlinarith
  have hpow : 1≤(M*X)^η := Real.one_le_rpow hP hη
  have hT : 1≤selectedPoissonT C M X η := by dsimp [selectedPoissonT]; nlinarith
  have hT0 : 0<selectedPoissonT C M X η := by linarith
  have hK0 : 0<selectedPoissonK C M X η := by unfold selectedPoissonK; positivity
  have hfrac : M/selectedPoissonK C M X η≤(M/X)^2 := by
    apply (div_le_iff₀ hK0).mpr
    have he : (M/X)^2*selectedPoissonK C M X η=M*selectedPoissonT C M X η := by
      unfold selectedPoissonK
      field_simp
    rw [he]
    nlinarith
  have hsqrt : Real.sqrt (M/selectedPoissonK C M X η)≤M/X := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,hfrac⟩
  have hfirst : Real.sqrt (M/selectedPoissonK C M X η)*N≤M := by
    calc
      _ ≤ (M/X)*X := by gcongr
      _ = M := by field_simp
  have hsecond : Real.sqrt M*(selectedPoissonK C M X η)^(α-1/2) ≤
      selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) := by
    calc
      _ ≤ Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) := by
        gcongr ; linarith
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hT
          (show 0≤Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) by positivity)
        nlinarith
  exact add_le_add hfirst hsecond

end

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy EisensteinSchwartzPoisson

def poissonShape (M X α : ℝ) : ℝ := M+X+X^(2*α-1)*M^(1-α)
def poissonShapeConstant (B C1 : ℝ) : ℝ := 2+4*C1^3+B^2+C1

theorem poisson_envelope_identity (H C P η Z : ℝ) (hP : 0<P) :
    262144*((H*P^(4*η))^8)^8*(C*P^(3*η)*Z) =
      (262144*H^64*C)*P^(259*η)*Z := by
  have hp : (P^(4*η))^64*P^(3*η)=P^(259*η) := by
    calc
      _ = P^((4*η)*64)*P^(3*η) := by rw [Real.rpow_mul hP.le (4*η) 64,Real.rpow_ofNat]
      _ = P^((4*η)*64+3*η) := (Real.rpow_add hP _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ = (262144*H^64*C)*((P^(4*η))^64*P^(3*η))*Z := by ring
    _ = _ := by rw [hp]

theorem poissonComparisonMajorant_selected_power
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2≤α) (hα2 : α≤2)
    (η : ℝ) (hη : 0<η) (hη1 : η≤1) (l A : ℕ)
    (hl : 4≤η*l) (hA : 4≤η*A)
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ)
    (hCD : 0≤CD) (hCS : 0≤CS) (hCT : 0≤CT) (hCP : 0≤CP)
    (B C1 : ℝ) (hB : 1≤B) (hC1 : 1≤C1) (W : 𝓢(ℝ,ℂ)) :
    ∃ Cfinal : ℝ, 0<Cfinal ∧
      ∀ (C M X q : ℝ) (G : Ideal O), 4≤C → B≤C → C≤C1 →
        1≤M → 1≤X → 1≤q → q≤X → G≠0 → (Ideal.absNorm G:ℝ)=B*q →
        1≤selectedPoissonK C M X η →
      poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp η hη η hη G
        (selectedPoissonK C M X η) (X/q) M (selectedPoissonT C M X η)
        (fun _ : Unit => (1:ℂ)) W ≤
        Cfinal*(M*X)^(259*η)*poissonShape M X α := by
  let D := 2*C1+B
  have hD : 1≤D := by dsimp [D]; linarith only [hC1,hB]
  obtain ⟨H,hH,hconst⟩ := list_exists_positive_bound
    (poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W)
  let Cshape := poissonShapeConstant B C1
  have hC10 : 0≤C1 := le_trans zero_le_one hC1
  have hCs : 1≤Cshape := by
    dsimp [Cshape,poissonShapeConstant]
    nlinarith only [hC10,pow_nonneg hC10 3,sq_nonneg B]
  have hCsC : C1≤Cshape := by
    dsimp [Cshape,poissonShapeConstant]
    nlinarith only [pow_nonneg hC10 3,sq_nonneg B]
  have hCsB : B^2≤Cshape := by
    dsimp [Cshape,poissonShapeConstant]
    nlinarith only [hC10,pow_nonneg hC10 3]
  have hCsMid : 1+4*C1^3≤Cshape := by
    dsimp [Cshape,poissonShapeConstant]
    nlinarith only [hC10,sq_nonneg B]
  refine ⟨262144*H^64*Cshape,by positivity,?_⟩
  intro C M X q G hC hBC hCC hM hX hq hqX hG hGN hK
  have hM0 : 0<M := lt_of_lt_of_le zero_lt_one hM
  have hX0 : 0<X := lt_of_lt_of_le zero_lt_one hX
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hP : 1≤M*X := by nlinarith only [hM,hX]
  have hP0 : 0<M*X := by positivity
  have hMP : M≤M*X := by nlinarith only [hM,hX]
  have hXP : X≤M*X := by nlinarith only [hM,hX]
  have hN : 1≤X/q := (le_div_iff₀ hq0).mpr (by simpa using hqX)
  have hNX : X/q≤X := div_le_self hX0.le hq
  have hNP : X/q≤M*X := hNX.trans hXP
  obtain ⟨hT,hTP,hKP⟩ := selectedPoisson_upper C C1 M X η hC hCC hM hX hη.le hη1
  have hKg : 0≤selectedPoissonK C M X η := le_trans zero_le_one hK
  have hg : (Ideal.absNorm G:ℝ)≤B*(M*X) := by rw [hGN]; gcongr; exact hqX.trans hXP
  have hb := poissonUnitBudget_power_envelope sD sS sT CD CS CT CP hCD hCS hCT hCP
    hexp η hη G hG (selectedPoissonK C M X η) (X/q) (M*X) D H W
    hK hN hP hD hH hconst
    (poisson_seven_scale_bounds (Ideal.absNorm G:ℝ) (selectedPoissonK C M X η) (X/q)
      (M*X) B C1 hP hB hC1 (Nat.cast_nonneg _) hKg (by positivity) hg hKP hNP)
  let R := (M*X)^(3*η)
  have hR : 1≤R := Real.one_le_rpow hP (by positivity)
  let Z := X^(2*α-1)*M^(1-α)
  have hZ : 0≤Z := by dsimp [Z]; positivity
  let S := Cshape*R*poissonShape M X α
  have hshape : 1≤poissonShape M X α := by
    change 1≤M+X+Z
    linarith only [hM,hX,hZ]
  have hshape0 : 0≤poissonShape M X α := le_trans zero_le_one hshape
  have hMshape : M≤poissonShape M X α := by
    change M≤M+X+Z
    linarith only [hX,hZ]
  have hXshape : X≤poissonShape M X α := by
    change X≤M+X+Z
    linarith only [hM,hZ]
  have hZshape : Z≤poissonShape M X α := by
    change Z≤M+X+Z
    linarith only [hM,hX]
  have hRshape : 1≤R*poissonShape M X α := by nlinarith only [hR,hshape]
  have hshapeS : poissonShape M X α≤S := by
    calc
      poissonShape M X α ≤ R*poissonShape M X α := le_mul_of_one_le_left hshape0 hR
      _ ≤ Cshape*(R*poissonShape M X α) :=
        le_mul_of_one_le_left (mul_nonneg (by linarith only [hR]) hshape0) hCs
      _ = S := by dsimp [S]; ring
  have hMS : M≤S := hMshape.trans hshapeS
  have hNS : X/q≤S := hNX.trans (hXshape.trans hshapeS)
  have hMiddle : selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) ≤
      4*C1^3*R*poissonShape M X α := by
    apply (selectedPoisson_middle_bound C M X η α hC hM hX hη.le hα2).trans
    change 4*C^3*R*Z≤4*C1^3*R*poissonShape M X α
    gcongr
  have hmidS : selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2)≤S :=
    hMiddle.trans (by dsimp [S]; gcongr; linarith only [hCsMid])
  have hprS : Real.sqrt (M/selectedPoissonK C M X η)*(X/q)+
      Real.sqrt M*(selectedPoissonK C M X η)^(α-1/2)≤S := by
    apply (selectedPoisson_principal_shape C M X (X/q) η α hC hM hX (by positivity) hNX hη.le hα).trans
    calc
      M+selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2)
          ≤ poissonShape M X α+4*C1^3*R*poissonShape M X α := add_le_add hMshape hMiddle
      _ ≤ R*poissonShape M X α+4*C1^3*R*poissonShape M X α :=
        add_le_add (le_mul_of_one_le_left hshape0 hR) (le_refl _)
      _ = (1+4*C1^3)*R*poissonShape M X α := by ring
      _ ≤ S := by dsimp [S]; gcongr
  obtain ⟨hED,hES⟩ := poisson_truncation_small (M*X) (selectedPoissonT C M X η) η
    (selectedPoissonK C M X η) M (X/q) C1 l hP hTP hl hKg hM0.le (by positivity) hC10 hKP hMP hNP
  have hC1S : C1≤S := by
    calc
      C1 ≤ Cshape := hCsC
      _ ≤ Cshape*(R*poissonShape M X α) := le_mul_of_one_le_right (by positivity) hRshape
      _ = S := by dsimp [S]; ring
  have htailS : M/((min 1 (M/((Ideal.absNorm G:ℝ)*(X/q)*(X/q))))^2*
      (1+(M/((Ideal.absNorm G:ℝ)*(X/q)*(X/q)))*selectedPoissonK C M X η)^A)≤S := by
    rw [hGN]
    apply (selectedPoisson_tail_shape C B M X q η A hBC hB hM hX hq hη.le hA).trans
    calc
      B^2*M ≤ B^2*(R*poissonShape M X α) := by
        gcongr
        exact hMshape.trans (le_mul_of_one_le_left hshape0 hR)
      _ ≤ Cshape*(R*poissonShape M X α) := by gcongr
      _ = S := by dsimp [S]; ring
  have hV : 1≤H*(M*X)^(4*η) := by
    have hh := Real.one_le_rpow hP (show 0≤4*η by positivity)
    nlinarith only [hH,hh]
  have hU : 1≤(H*(M*X)^(4*η))^8 := one_le_pow₀ hV
  apply (poissonComparisonMajorant_unit_box sD sS sT CD CS CT CP l A hexp η hη η hη G
    (selectedPoissonK C M X η) (X/q) M (selectedPoissonT C M X η)
    ((H*(M*X)^(4*η))^8) S W hKg (by positivity) hM0.le (by linarith only [hT]) hU (by dsimp [S]; positivity)
    hb hMS hNS hmidS hprS (hED.trans hC1S) (hES.trans hC1S) htailS).trans_eq
  exact poisson_envelope_identity H Cshape (M*X) η (poissonShape M X α) hP0

end CanonicalQuadraticSieve

end

end OAI
