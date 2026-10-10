import OAI.NumberTheory.DirichletL.MeanSquare.HighRadialBounds
import OAI.NumberTheory.DirichletL.CubicSieve.PaddedPassage

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

namespace InitialMeanSquare

section

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)

def initialHighRadialCost {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (s : SecondRayIndex → Finset ι → SecondLogIndex → Finset (SecondExpansionData ι))
    (B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ)
    (Z H U Kmax ε θ : ℝ) (V₁ V₂ : ℝ → ℂ) : ℝ :=
  ∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p F U,∑ j ∈ secondLogBinBox U Kmax,
    if Z^θ < initialRadial Z H (primeProductNorm p R) j then
      initialRestrictedBinCost p hp hcop hg F R Ψ m ray (s ray R j) Z H ε j V₁ V₂ (B ray R j)
    else 0

section
variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
  (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hc hinj in

theorem initial_high_radial_sum (F : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O)
    (K : Finset ι → Finset ι → Finset O) (Z H U Kmax M ε θ A Vmax Cs : ℝ)
    (hZ : 0 < Z) (hH : 1 ≤ H) (hε : ε ≤ 1)
    (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax) (hCs : 0 ≤ Cs)
    (s : SecondRayIndex → Finset ι → SecondLogIndex → Finset (SecondExpansionData ι))
    (hs : ∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,
      s ray R j ⊆ secondLogSector p ∅ F K R Z M j)
    (V₁ V₂ : ℝ → ℂ)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ) (J N : ℕ)
    (hB : ∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,∀ q,0 ≤ B ray R j q)
    (hdec : ∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,∀ q,
      (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2)*B ray R j q ≤
      Cs*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) :
    initialHighRadialCost p hp hcop hg F Ψ m s B Z H U Kmax ε θ V₁ V₂ ≤
      (initialHighRadialConstant A Vmax Cs*Z^4/(Z^θ)^N)*initialRayMass*
        ((secondLogBinBox U Kmax).card : ℝ)*(128*Real.exp 1*(normLogBin U+1 : ℝ)) := by
  have hconstant := initialHighRadialConstant_nonneg A Vmax Cs hCs
  have hzpow : 0 < Z^θ := Real.rpow_pos_of_pos hZ _
  unfold initialHighRadialCost
  apply initial_harmonic_aggregation p hinj F U Kmax _ (by positivity)
  intro ray R hR j hj
  split_ifs with hh
  · have hc' := initial_subbin_cost_radial_decay p hp hcop hg hc hinj F R Ψ hΨ m ray K
      Z H M ε A Vmax Cs hZ hH hε hA hVmax hCs j (s ray R j) (hs ray R hR j hj)
      V₁ V₂ hV₁ hV₂ hs₁ hs₂ (B ray R j) J N (hB ray R hR j hj) (hdec ray R hR j hj)
    have hRp := FirstPassCubeLabels.primeProductNorm_pos p hp R
    have hd : (Z^θ)^N ≤ (1+initialRadial Z H (primeProductNorm p R) j)^N :=
      pow_le_pow_left₀ hzpow.le (by linarith) N
    have hnum : 0 ≤ initialHighRadialConstant A Vmax Cs*Z^4/primeProductNorm p R*
        ‖secondRayCoefficient ray‖ := by positivity
    apply hc'.trans
    calc
      _ ≤ (initialHighRadialConstant A Vmax Cs*Z^4/primeProductNorm p R*
        ‖secondRayCoefficient ray‖)/(Z^θ)^N :=
        div_le_div_of_nonneg_left hnum (pow_pos hzpow _) hd
      _ = _ := by ring
  · have hRp := FirstPassCubeLabels.primeProductNorm_pos p hp R
    positivity

end

theorem initial_log_harmonic_polynomial :
    ∃ C : ℝ,0 < C ∧ ∀ (Y U Kmax : ℝ),1 ≤ Y → 0 < U → 0 < Kmax → U ≤ Y → Kmax ≤ Y →
      ((secondLogBinBox U Kmax).card : ℝ)*(128*Real.exp 1*(normLogBin U+1 : ℝ)) ≤ C*Y^2 := by
  obtain ⟨C,hC,hbound⟩ := initial_log_box_small_power 1 (by norm_num)
  refine ⟨C*(256*Real.exp 1),by positivity,?_⟩
  intro Y U Kmax hY hU hK hUY hKY
  have hc := hbound Y U Kmax hY hU hK hUY hKY
  rw [Real.rpow_one] at hc
  have hu := normLogBin_le_log_upper U Y hU hUY hY
  have hl := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hY)
  have hlog : (normLogBin U : ℝ)+1 ≤ 2*Y := by linarith
  have hh : 128*Real.exp 1*(normLogBin U+1 : ℝ) ≤ (256*Real.exp 1)*Y := by
    have he := Real.exp_pos (1:ℝ)
    nlinarith
  have hnon : 0 ≤ 128*Real.exp 1*(normLogBin U+1 : ℝ) := by positivity
  calc
    _ ≤ (C*Y)*((256*Real.exp 1)*Y) := mul_le_mul hc hh hnon (by positivity)
    _ = _ := by ring

theorem initial_high_radial_order (θ τ : ℝ) (hθ : 0 < θ) :
    ∃ N : ℕ,38+τ ≤ θ*(N : ℝ) := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((38+τ)/θ)
  refine ⟨N,?_⟩
  have hh := (div_lt_iff₀ hθ).mp hN
  linarith

theorem initial_high_radial_negligible (θ τ A Vmax Cs Ccap : ℝ) (N : ℕ)
    (hN : 38+τ ≤ θ*(N : ℝ)) (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax)
    (hCs : 0 ≤ Cs) (hcap : 1 ≤ Ccap) :
    ∃ C : ℝ,0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
      [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (F : Finset ι) (Ψ : O →* ℂ) (_hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O)
      (K : Finset ι → Finset ι → Finset O) (Z H U Kmax M ε : ℝ),
      1 ≤ Z → 1 ≤ H → 0 < U → 0 < Kmax → ε ≤ 1 →
      U ≤ Ccap*Z^17 → Kmax ≤ Ccap*Z^17 →
      ∀ (s : SecondRayIndex → Finset ι → SecondLogIndex → Finset (SecondExpansionData ι)),
      (∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,
        s ray R j ⊆ secondLogSector p ∅ F K R Z M j) →
      ∀ (V₁ V₂ : ℝ → ℂ),
      (∀ t,‖V₁ t‖ ≤ Vmax) → (∀ t,‖V₂ t‖ ≤ Vmax) →
      (∀ t,V₁ t ≠ 0 → |t| ≤ A) → (∀ t,V₂ t ≠ 0 → |t| ≤ A) →
      ∀ (B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ) (J : ℕ),
      (∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,∀ q,0 ≤ B ray R j q) →
      (∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,∀ q,
        (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2)*B ray R j q ≤
        Cs*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) →
      initialHighRadialCost p hp hcop hg F Ψ m s B Z H U Kmax ε θ V₁ V₂ ≤ C*Z^(-τ) := by
  obtain ⟨Clog,hClog,hlog⟩ := initial_log_harmonic_polynomial
  let Cbase := initialHighRadialConstant A Vmax Cs*initialRayMass*Clog*Ccap^2
  have hfixed := initialHighRadialConstant_nonneg A Vmax Cs hCs
  have hray := initialRayMass_nonneg
  have hbase : 0 ≤ Cbase := by
    dsimp [Cbase]
    exact mul_nonneg (mul_nonneg (mul_nonneg hfixed initialRayMass_nonneg) hClog.le) (sq_nonneg _)
  refine ⟨Cbase+1,by linarith,?_⟩
  intro ι _ p hp _ hcop hg hc hinj F Ψ hΨ m K Z H U Kmax M ε hZ hH hU hK hε hUcap hKcap
    s hs V₁ V₂ hV₁ hV₂ hs₁ hs₂ B J hB hdec
  have hZ0 := zero_lt_one.trans_le hZ
  have hy : 1 ≤ Ccap*Z^17 := one_le_mul_of_one_le_of_one_le hcap (one_le_pow₀ hZ)
  have hlogs := hlog (Ccap*Z^17) U Kmax hy hU hK hUcap hKcap
  have hb := initial_high_radial_sum p hp hcop hg hc hinj F Ψ hΨ m K Z H U Kmax M ε θ
    A Vmax Cs hZ0 hH hε hA hVmax hCs s hs V₁ V₂ hV₁ hV₂ hs₁ hs₂ B J N hB hdec
  have hscalar : Z^(38 : ℕ)/(Z^θ)^N ≤ Z^(-τ) := by
    have he : Z^(38 : ℕ)/(Z^θ)^N=Z^((38 : ℝ)-θ*(N : ℝ)) := by
      rw [Real.rpow_sub hZ0,Real.rpow_mul_natCast hZ0.le]
      norm_cast
    rw [he]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  calc
    _ ≤ (initialHighRadialConstant A Vmax Cs*Z^4/(Z^θ)^N)*initialRayMass*
        ((secondLogBinBox U Kmax).card : ℝ)*(128*Real.exp 1*(normLogBin U+1 : ℝ)) := hb
    _ = ((initialHighRadialConstant A Vmax Cs*Z^4/(Z^θ)^N)*initialRayMass)*
        (((secondLogBinBox U Kmax).card : ℝ)*(128*Real.exp 1*(normLogBin U+1 : ℝ))) := by ring
    _ ≤ ((initialHighRadialConstant A Vmax Cs*Z^4/(Z^θ)^N)*initialRayMass)*
        (Clog*(Ccap*Z^17)^2) := mul_le_mul_of_nonneg_left hlogs (by positivity)
    _ = Cbase*(Z^(38 : ℕ)/(Z^θ)^N) := by dsimp [Cbase]; ring
    _ ≤ Cbase*Z^(-τ) := mul_le_mul_of_nonneg_left hscalar hbase
    _ ≤ (Cbase+1)*Z^(-τ) := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hZ0.le _)

end

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

theorem initialErrorFrequencyBound_le (a b Z H : ℝ) (hZ : 1 ≤ Z) (hH : 1 ≤ H) :
    initialErrorFrequencyBound a b Z H ≤
      48*(1+Real.exp (initialErrorWindow a b))^16*Z^16 := by
  let Q := 1+Z*Real.exp (initialErrorWindow a b)
  have hZ0 := zero_lt_one.trans_le hZ
  have hH0 := zero_lt_one.trans_le hH
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    have hh : 0 ≤ Z*Real.exp (initialErrorWindow a b) := by positivity
    linarith
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have h3 : Q^3/H ≤ Q^3 := div_le_self (pow_nonneg hQ0 _) hH
  have hinner : 1+Q^3/H ≤ 2*Q^3 := by linarith [one_le_pow₀ hQ (n := 3)]
  have hT : initialTailHeight Z H (initialErrorWindow a b) ≤ 2*Q^5 := by
    change Q^2*(1+Q^3/H) ≤ 2*Q^5
    calc
      _ ≤ Q^2*(2*Q^3) := mul_le_mul_of_nonneg_left hinner (sq_nonneg Q)
      _ = _ := by ring
  have hT0 : 0 ≤ initialTailHeight Z H (initialErrorWindow a b) :=
    (initialTailHeight_pos Z H _ hZ0 hH0).le
  have hv : initialTailHeight Z H (initialErrorWindow a b)*Q^3/H ≤ 2*Q^8 := by
    calc
      _ ≤ initialTailHeight Z H (initialErrorWindow a b)*Q^3 :=
        div_le_self (mul_nonneg hT0 (pow_nonneg hQ0 _)) hH
      _ ≤ (2*Q^5)*Q^3 := mul_le_mul_of_nonneg_right hT (pow_nonneg hQ0 _)
      _ = _ := by ring
  have hv2 : initialTailHeight Z H (initialErrorWindow a b)*Q^3/H+2 ≤ 4*Q^8 := by
    linarith [one_le_pow₀ hQ (n := 8)]
  have hb : initialErrorFrequencyBound a b Z H ≤ 48*Q^16 := by
    unfold initialErrorFrequencyBound
    change 3*(initialTailHeight Z H (initialErrorWindow a b)*Q^3/H+2)^2 ≤ _
    calc
      _ ≤ 3*(4*Q^8)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hv2 2) (by norm_num)
      _ = _ := by ring
  have hQZ : Q ≤ (1+Real.exp (initialErrorWindow a b))*Z := by
    dsimp [Q]
    nlinarith
  calc
    _ ≤ 48*Q^16 := hb
    _ ≤ 48*((1+Real.exp (initialErrorWindow a b))*Z)^16 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hQ0 hQZ 16) (by norm_num)
    _ = _ := by rw [mul_pow]; ring

def initialErrorRowBound (a b Z H : ℝ) : ℝ :=
  Z*Real.exp (initialErrorWindow a b)*initialErrorFrequencyBound a b Z H

lemma initialErrorRowBound_pos (a b Z H : ℝ) (hZ : 0 < Z) (hH : 0 < H) :
    0 < initialErrorRowBound a b Z H := by
  have ht := initialTailHeight_pos Z H (initialErrorWindow a b) hZ hH
  unfold initialErrorRowBound initialErrorFrequencyBound
  positivity

theorem initialErrorRowBound_valid {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (F R : Finset ι) (a b Z H : ℝ) (hZ : 0 < Z) (hH : 0 < H)
    (x : SecondExpansionData ι)
    (hx : x ∈ secondSupportedSector p F (fun _ _ => initialErrorCutoff a b Z H) R Z
      (initialErrorWindow a b)) :
    elementNorm (sourceObservation p x).1 ≤ initialErrorRowBound a b Z H := by
  obtain ⟨hG,hE,hV,hk,hkf,hR,hs⟩ := secondSupportedSector_mem p F
    (fun _ _ => initialErrorCutoff a b Z H) R Z (initialErrorWindow a b) x hx
  have he := (secondSourceSupport_bounds p hp Z (initialErrorWindow a b) x hs hE).2.1
  have hf := initialErrorCutoff_norm_bound a b Z H hZ hH x.frequency hkf
  have hh := mul_le_mul he hf (sq_nonneg ‖eisEmbedding x.frequency‖) (by positivity)
  simpa only [initialErrorRowBound,sourceObservation,elementNorm,map_mul,norm_mul,mul_pow,
    primeSubsetGenerator_norm_eq_productNorm] using hh

def initialPolynomialCap (a b : ℝ) : ℝ :=
  1+Real.exp (initialErrorWindow a b)+
    48*Real.exp (initialErrorWindow a b)*(1+Real.exp (initialErrorWindow a b))^16

lemma initialPolynomialCap_ge_one (a b : ℝ) : 1 ≤ initialPolynomialCap a b := by
  unfold initialPolynomialCap
  have he := Real.exp_pos (initialErrorWindow a b)
  have hh : 0 ≤ 48*Real.exp (initialErrorWindow a b)*(1+Real.exp (initialErrorWindow a b))^16 := by positivity
  linarith

theorem initial_actual_bin_polynomial_caps (a b Z H : ℝ) (hZ : 1 ≤ Z) (hH : 1 ≤ H) :
    Z*Real.exp (initialErrorWindow a b) ≤ initialPolynomialCap a b*Z^17 ∧
    initialErrorRowBound a b Z H ≤ initialPolynomialCap a b*Z^17 := by
  have he := Real.exp_pos (initialErrorWindow a b)
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ
  have hz17 : Z ≤ Z^17 := by
    simpa only [pow_one] using pow_le_pow_right₀ hZ (by decide : 1 ≤ 17)
  have hC1 : Real.exp (initialErrorWindow a b) ≤ initialPolynomialCap a b := by
    unfold initialPolynomialCap
    have hh : 0 ≤ 48*Real.exp (initialErrorWindow a b)*(1+Real.exp (initialErrorWindow a b))^16 := by positivity
    linarith
  have hC2 : 48*Real.exp (initialErrorWindow a b)*(1+Real.exp (initialErrorWindow a b))^16 ≤
      initialPolynomialCap a b := by
    unfold initialPolynomialCap
    have hh : 0 ≤ 48*Real.exp (initialErrorWindow a b)*(1+Real.exp (initialErrorWindow a b))^16 := by positivity
    linarith
  constructor
  · calc
      _ ≤ Real.exp (initialErrorWindow a b)*Z^17 := by
        rw [mul_comm Z]; exact mul_le_mul_of_nonneg_left hz17 he.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hC1 (pow_nonneg hZ0 _)
  · have hb := mul_le_mul_of_nonneg_left (initialErrorFrequencyBound_le a b Z H hZ hH)
      (mul_nonneg hZ0 he.le)
    change initialErrorRowBound a b Z H ≤ _ at hb
    calc
      _ ≤ (Z*Real.exp (initialErrorWindow a b))*(48*(1+Real.exp (initialErrorWindow a b))^16*Z^16) := hb
      _ = (48*Real.exp (initialErrorWindow a b)*(1+Real.exp (initialErrorWindow a b))^16)*Z^17 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC2 (pow_nonneg hZ0 _)

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity normalizedColumn columnLog)

theorem initial_two_windows_bounded (V₁ V₂ : ℝ → ℂ)
    (hc₁ : HasCompactSupport V₁) (hc₂ : HasCompactSupport V₂)
    (hs₁ : Continuous V₁) (hs₂ : Continuous V₂) :
    ∃ A Vmax : ℝ,0 ≤ A ∧ 0 ≤ Vmax ∧
      (∀ t,‖V₁ t‖ ≤ Vmax) ∧ (∀ t,‖V₂ t‖ ≤ Vmax) ∧
      (∀ t,V₁ t ≠ 0 → |t| ≤ A) ∧ (∀ t,V₂ t ≠ 0 → |t| ≤ A) := by
  obtain ⟨A₁,hA₁,hbound₁⟩ := hc₁.exists_pos_le_norm
  obtain ⟨A₂,hA₂,hbound₂⟩ := hc₂.exists_pos_le_norm
  obtain ⟨B₁,hB₁⟩ := hc₁.exists_bound_of_continuous hs₁
  obtain ⟨B₂,hB₂⟩ := hc₂.exists_bound_of_continuous hs₂
  refine ⟨max A₁ A₂,max 0 (max B₁ B₂),?_,le_max_left _ _,?_,?_,?_,?_⟩
  · exact hA₁.le.trans (le_max_left _ _)
  · intro t
    exact (hB₁ t).trans ((le_max_left _ _).trans (le_max_right _ _))
  · intro t
    exact (hB₂ t).trans ((le_max_right _ _).trans (le_max_right _ _))
  · intro t ht
    have hh : ‖t‖ < A₁ := lt_of_not_ge (fun h => ht (hbound₁ t h))
    simpa only [Real.norm_eq_abs] using hh.le.trans (le_max_left A₁ A₂)
  · intro t ht
    have hh : ‖t‖ < A₂ := lt_of_not_ge (fun h => ht (hbound₂ t h))
    simpa only [Real.norm_eq_abs] using hh.le.trans (le_max_right A₁ A₂)

theorem initial_high_radial_source
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (a b θ τ ε : ℝ)
    (hU : ∀ t,g t ≠ 0 → U t=1)
    (hgs : ∀ t,g t ≠ 0 → |t| ≤ initialErrorWindow a b)
    (hθ : 0 < θ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ,0 < C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (F : Finset ι) (Ψ : O →* ℂ) (m : O) (Z H : ℝ),
      1 ≤ Z → 1 ≤ H → (∀ x,‖Ψ x‖ ≤ 1) →
      ∀ (s : SecondRayIndex → Finset ι → SecondLogIndex → Finset (SecondExpansionData ι)),
      (∀ ray R j,s ray R j ⊆ secondLogSector p ∅ F
        (fun _ _ => initialErrorCutoff a b Z H) R Z (initialErrorWindow a b) j) →
      let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
      (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p F (Z*Real.exp (initialErrorWindow a b)),
        ∑ j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H),
        if Z^θ < initialRadial Z H (primeProductNorm p R) j then
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray (s ray R j) G G W H‖ else 0) ≤
      C*Z^(-τ) := by
  obtain ⟨N,hN⟩ := initial_high_radial_order θ τ hθ
  have hM : 0 ≤ initialErrorWindow a b := by unfold initialErrorWindow; positivity
  obtain ⟨windows,Ct,Cs,hCt,hCs,hwc,hws,ht⟩ :=
    initial_subbin_transfer U hUc hUs g W (initialErrorWindow a b) hM hU hgs ε hε (N+2) 0
  obtain ⟨A,Vmax,hA,hVmax,hV₁,hV₂,hs₁,hs₂⟩ :=
    initial_two_windows_bounded (windows 5) (windows 6) (hwc 5) (hwc 6)
      (hws 5).continuous (hws 6).continuous
  obtain ⟨Ch,hCh,hh⟩ := initial_high_radial_negligible θ τ A Vmax Cs (initialPolynomialCap a b)
    N hN hA hVmax hCs (initialPolynomialCap_ge_one a b)
  refine ⟨Ct*Ch+1,by positivity,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr F Ψ m Z H hZ hH hΨ s hs
  dsimp only
  have hZ0 := zero_lt_one.trans_le hZ
  have hH0 := zero_lt_one.trans_le hH
  let K := fun (_ _ : Finset ι) => initialErrorCutoff a b Z H
  let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
  let B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ :=
    fun ray R j => Classical.choose
      (ht p hp hcop hg hinj hc hpr F R Ψ m ray K Z H (initialErrorWindow a b) j
        (s ray R j) hZ0 hH0 hΨ (hs ray R j))
  have hB (ray : SecondRayIndex) (R : Finset ι) (j : SecondLogIndex) :=
    Classical.choose_spec
      (ht p hp hcop hg hinj hc hpr F R Ψ m ray K Z H (initialErrorWindow a b) j
        (s ray R j) hZ0 hH0 hΨ (hs ray R j))
  have hcost := hh p hp hcop hg hc hinj F Ψ hΨ m K Z H
    (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H)
    (initialErrorWindow a b) ε hZ hH (by positivity) (initialErrorRowBound_pos a b Z H hZ0 hH0)
    hε1 (initial_actual_bin_polynomial_caps a b Z H hZ hH).1
    (initial_actual_bin_polynomial_caps a b Z H hZ hH).2
    s (fun ray R _ j _ => hs ray R j) (windows 5) (windows 6) hV₁ hV₂ hs₁ hs₂ B 0
    (fun ray R _ j _ => (hB ray R j).1) (fun ray R _ j _ => (hB ray R j).2.1)
  have hsum :
      (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p F (Z*Real.exp (initialErrorWindow a b)),
        ∑ j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H),
        if Z^θ < initialRadial Z H (primeProductNorm p R) j then
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray (s ray R j) G G W H‖ else 0) ≤
      Ct*initialHighRadialCost p hp hcop hg F Ψ m s B Z H
        (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H) ε θ (windows 5) (windows 6) := by
    unfold initialHighRadialCost
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ray hray
    apply Finset.sum_le_sum
    intro R hR
    apply Finset.sum_le_sum
    intro j hj
    split_ifs with hjrad
    · convert (hB ray R j).2.2 using 1 ;
        dsimp only [initialRestrictedBinCost,G,B] ; ring
    · simp
  calc
    _ ≤ Ct*initialHighRadialCost p hp hcop hg F Ψ m s B Z H
        (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H) ε θ (windows 5) (windows 6) := hsum
    _ ≤ Ct*(Ch*Z^(-τ)) := mul_le_mul_of_nonneg_left hcost hCt
    _ ≤ (Ct*Ch+1)*Z^(-τ) := by
      have hz := Real.rpow_nonneg hZ0.le (-τ)
      nlinarith

end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap
namespace FirstPassCubeLabels

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open MixedCrossSeparation (columnCoefficient columnPrimeCoprime)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

lemma threeBlockExponent_ne_zero_on (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool) :
    ∀i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,threeBlockExponent N P v ε₁ ε₂ i≠0 := by
  intro i hi
  by_cases hn:i∈N
  · simp [threeBlockExponent,hn]
  by_cases hp':i∈P
  · simp [threeBlockExponent,hn,hp']
  · have hiC:i∈cubeActiveSupport B v ε₁ ε₂ := by simpa [hn,hp'] using hi
    simp only [threeBlockExponent,ite_eq_right hn,ite_eq_right hp']
    exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp hiC).2

lemma threeBlockExponent_lt_six_on (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool) :
    ∀i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,threeBlockExponent N P v ε₁ ε₂ i<6 := by
  intro i hi
  unfold threeBlockExponent
  split_ifs <;> first | omega | exact ZMod.val_lt _

lemma threeGaussRowFactor_norm_le
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (d h : O) :
    ‖threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h‖≤‖C₁ N‖*‖C₂ P‖ := by
  let S := (N∪P)∪cubeActiveSupport B v ε₁ ε₂
  let e := threeBlockExponent N P v ε₁ ε₂
  have hG := FiniteGaussPhase.norm_canonicalProductGauss
    (fun i:S=>p i.val) (fun i=>hp i.val) (columnPrimeCoprime p hcop S)
    (fun i=>hg i.val) (fun i=>hc i.val) (fun i=>e i.val)
    (fun i=>threeBlockExponent_ne_zero_on N P B v ε₁ ε₂ i.val i.property)
    (fun i=>threeBlockExponent_lt_six_on N P B v ε₁ ε₂ i.val i.property)
  change ‖star (columnCoefficient p hp hcop hg N*C₁ N)*
    (columnCoefficient p hp hcop hg P*C₂ P)*
    FiniteGaussPhase.canonicalProductGauss (fun i:S=>p i.val) (fun i=>hp i.val)
      (columnPrimeCoprime p hcop S) (fun i=>hg i.val) (fun i=>e i.val)*
    (blockRow p hg S e d*star (blockRow p hg S e h))‖≤_
  simp only [norm_mul,norm_star,SecondPassArithmetic.columnCoefficient_norm_one p hp hcop hg hc,
    hG,one_mul,mul_one]
  apply mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (blockRow_norm_le_one p hg S e d)).trans (blockRow_norm_le_one p hg S e h)

lemma canonicalPairMode_norm_le
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) (d h : O) :
    ‖canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h‖≤
      (‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖eisEmbedding (∏i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,p i)‖)*
        (‖C₁ N‖*‖C₂ P‖))*
      ‖paperRadialFourier W ((K/(‖eisEmbedding d‖^2*
        primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)))*‖eisEmbedding h‖^2)‖ := by
  have hn : 0<‖eisEmbedding (∏i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,p i)‖ :=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i hi=>hp i)))
  have ha : K*‖eisEmbedding h‖^2/(‖eisEmbedding d‖^2*
      primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)) =
      (K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)))*
        ‖eisEmbedding h‖^2 := by ring
  simp only [canonicalPairMode,norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hK,abs_of_pos hn,ha]
  calc
    _ ≤ (‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖eisEmbedding (∏i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,p i)‖))*
      ‖paperRadialFourier W ((K/(‖eisEmbedding d‖^2*
        primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)))*‖eisEmbedding h‖^2)‖*
      (‖C₁ N‖*‖C₂ P‖) := mul_le_mul_of_nonneg_left
        (threeGaussRowFactor_norm_le p hp hcop hg hc N P B v ε₁ ε₂ C₁ C₂ d h) (by positivity)
    _ = _ := by ring

end

theorem full_uniform_canonicalPairMode_remainder (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
      (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
      (X₁ X₂ K H : ℝ),0<K → 0≤H → ∀(d : O),d≠0 → ∀T:Finset O,
      let S := (N∪P)∪cubeActiveSupport B v ε₁ ε₂
      let scale := K/(‖eisEmbedding d‖^2*primeProductNorm p S)
      (∀h:O,h∉T → H≤scale*‖eisEmbedding h‖^2) →
      ‖∑'h:{h:O // h∉T},canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖≤
      (‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖eisEmbedding (∏i∈S,p i)‖)*(‖C₁ N‖*‖C₂ P‖))*
      ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 scale)^2*(1+H)^A)) := by
  obtain ⟨s,C,hC,hb⟩ := EisensteinSchwartzPoisson.paperRadialFourier_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hcop hg hc N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K H hK hH d hd T
  dsimp only
  intro hT
  let S := (N∪P)∪cubeActiveSupport B v ε₁ ε₂
  let scale := K/(‖eisEmbedding d‖^2*primeProductNorm p S)
  let c := ‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖eisEmbedding (∏i∈S,p i)‖)*(‖C₁ N‖*‖C₂ P‖)
  have hscale : 0<scale := div_pos hK (mul_pos
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd))) (primeProductNorm_pos p hp S))
  have hc0 : 0≤c := by dsimp [c]; positivity
  let small : Set O := {h|h∉T}
  let large : Set O := {h|H≤scale*‖eisEmbedding h‖^2}
  let f : small→large := fun h=>⟨h.val,hT h.val h.property⟩
  have hfi : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun x:large=>x.val) hab)
  have hrad := EisensteinSchwartzPoisson.paperRadialFourier_lattice_summable_norm W scale hscale
  have hmajor := (hrad.subtype small).mul_left c
  have hpnt (h:small) :
      ‖canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖≤
      c*‖paperRadialFourier W (scale*‖eisEmbedding h.val‖^2)‖ :=
    canonicalPairMode_norm_le p hp hcop hg hc N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK d h.val
  have hsmall := Summable.of_nonneg_of_le (fun _=>norm_nonneg _) hpnt hmajor
  calc
    _ ≤ ∑'h:small,‖canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖ :=
      norm_tsum_le_tsum_norm hsmall
    _ ≤ ∑'h:small,c*‖paperRadialFourier W (scale*‖eisEmbedding h.val‖^2)‖ :=
      hsmall.tsum_le_tsum hpnt hmajor
    _ = c*∑'h:small,‖paperRadialFourier W (scale*‖eisEmbedding h.val‖^2)‖ := tsum_mul_left
    _ ≤ c*∑'h:large,‖paperRadialFourier W (scale*‖eisEmbedding h.val‖^2)‖ :=
      mul_le_mul_of_nonneg_left ((hrad.subtype small).tsum_le_tsum_of_inj f hfi
        (fun _ _=>norm_nonneg _) (fun _=>le_rfl) (hrad.subtype large)) hc0
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb W scale H hscale hH) hc0

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open SecondPassArithmetic (firstFrequencyDisk outside_firstFrequencyDisk columnLog_norm_upper)

def canonicalFirstFrequencyRadius {ι : Type*} [DecidableEq ι]
    (p : ι→O) (B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (d : O) (X₁ X₂ K P : ℝ) : ℝ :=
  P*(‖eisEmbedding d‖^2*primeProductNorm p (cubeActiveSupport B v ε₁ ε₂)*X₁*X₂)/K

theorem firstFrequencyDisk_uniform {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0)
    (N Q B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (hNQ : Disjoint N Q) (hNB : Disjoint N B) (hQB : Disjoint Q B)
    (d : O) (hd : d≠0) (X₁ X₂ K P M₁ M₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hK : 0<K)
    (hN : columnLog p X₁ N≤M₁) (hQ : columnLog p X₂ Q≤M₂)
    (h : O) (hh : h∉firstFrequencyDisk
      (canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P)) :
    P/Real.exp (M₁+M₂)≤
      (K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪Q)∪cubeActiveSupport B v ε₁ ε₂)))*
        ‖eisEmbedding h‖^2 := by
  let S := cubeActiveSupport B v ε₁ ε₂
  have hNS : Disjoint N S := hNB.mono_right (Finset.filter_subset _ _)
  have hQS : Disjoint Q S := hQB.mono_right (Finset.filter_subset _ _)
  have hNQS : Disjoint (N∪Q) S := Finset.disjoint_union_left.mpr ⟨hNS,hQS⟩
  have hnorm : primeProductNorm p ((N∪Q)∪S)=
      primeProductNorm p N*primeProductNorm p Q*primeProductNorm p S := by
    rw [primeProductNorm_union p _ _ hNQS,primeProductNorm_union p _ _ hNQ]
  have hNd : 0<‖eisEmbedding d‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd))
  have hU₁ : 0<X₁*Real.exp M₁ := mul_pos hX₁ (Real.exp_pos _)
  have hU₂ : 0<X₂*Real.exp M₂ := mul_pos hX₂ (Real.exp_pos _)
  let slow := K/(‖eisEmbedding d‖^2*(X₁*Real.exp M₁)*(X₂*Real.exp M₂)*primeProductNorm p S)
  have hs : 0<slow := div_pos hK (mul_pos (mul_pos (mul_pos hNd hU₁) hU₂) (primeProductNorm_pos p hp S))
  have hn := columnLog_norm_upper p hp X₁ M₁ hX₁ N hN
  have hq := columnLog_norm_upper p hp X₂ M₂ hX₂ Q hQ
  have hprod : primeProductNorm p N*primeProductNorm p Q≤(X₁*Real.exp M₁)*(X₂*Real.exp M₂) :=
    mul_le_mul hn hq (primeProductNorm_pos p hp Q).le hU₁.le
  have hscale : slow≤K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪Q)∪S)) := by
    apply div_le_div_of_nonneg_left hK.le
      (mul_pos hNd (primeProductNorm_pos p hp _))
    rw [hnorm]
    calc
      _ ≤ ‖eisEmbedding d‖^2*((X₁*Real.exp M₁)*(X₂*Real.exp M₂)*primeProductNorm p S) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hprod (primeProductNorm_pos p hp S).le) hNd.le
      _ = _ := by ring
  have hr : (P/Real.exp (M₁+M₂))/slow=
      canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P := by
    dsimp [slow,canonicalFirstFrequencyRadius,S]
    rw [Real.exp_add]
    field_simp

  have ho := outside_firstFrequencyDisk _ h hh
  rw [←hr] at ho
  have hbase : P/Real.exp (M₁+M₂)≤slow*‖eisEmbedding h‖^2 := by
    have hz := (div_lt_iff₀ hs).mp ho
    simpa only [mul_comm] using hz.le
  exact hbase.trans (mul_le_mul_of_nonneg_right hscale (sq_nonneg _))

theorem full_uniform_canonicalPairMode_disk_remainder (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (N Q B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool),
      Disjoint N Q → Disjoint N B → Disjoint Q B →
      ∀ (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
      (X₁ X₂ K P M₁ M₂ : ℝ),0<X₁ → 0<X₂ → 0<K → 0≤P →
      columnLog p X₁ N≤M₁ → columnLog p X₂ Q≤M₂ → ∀(d : O),d≠0 →
      let S := (N∪Q)∪cubeActiveSupport B v ε₁ ε₂
      let scale := K/(‖eisEmbedding d‖^2*primeProductNorm p S)
      let T := firstFrequencyDisk (canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P)
      ‖∑'h:{h:O // h∉T},canonicalPairMode p hp hcop hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖≤
      (‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ Q)‖*
        (K/‖eisEmbedding (∏i∈S,p i)‖)*(‖C₁ N‖*‖C₂ Q‖))*
      ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 scale)^2*(1+P/Real.exp (M₁+M₂))^A)) := by
  obtain ⟨s,C,hC,hb⟩:=full_uniform_canonicalPairMode_remainder A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hcop hg hc N Q B v ε₁ ε₂ hNQ hNB hQB C₁ C₂ W V₁ V₂ X₁ X₂ K P M₁ M₂ hX₁ hX₂ hK hP hN hQ d hd
  apply hb p hp hcop hg hc N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K _ hK
    (div_nonneg hP (Real.exp_pos _).le) d hd
  intro h hh
  exact firstFrequencyDisk_uniform p hp N Q B v ε₁ ε₂ hNQ hNB hQB d hd
    X₁ X₂ K P M₁ M₂ hX₁ hX₂ hK hN hQ h hh

end FirstPassCubeLabels

end

end OAI
