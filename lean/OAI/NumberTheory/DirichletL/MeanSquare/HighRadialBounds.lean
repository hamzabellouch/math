import OAI.NumberTheory.DirichletL.MeanSquare.DiagonalDensity

namespace OAI

noncomputable section

namespace InitialMeanSquare

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

section

open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open CanonicalQuadraticSieve (Admissible)

theorem initial_squarefree_target_geometry {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F R : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (Z M : ℝ) (j : SecondLogIndex) :
    let s := initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)
    ∀ z ∈ sourceIdealTarget (s.image (sourceObservation p)),
      Admissible z.1 ∧ (Ideal.absNorm z.1 : ℝ) ≤ initialLogLabel j ∧
      z.2 ≠ 0 ∧ ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ secondLogK j*Real.exp 1 := by
  dsimp only
  intro z hz
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨hxs,hsq⟩ := Finset.mem_filter.mp hx
  obtain ⟨hxp,hj⟩ := Finset.mem_filter.mp hxs
  have hk := (secondSupportedSector_mem p F K R Z M x hxp).2.2.2.1
  have hgeom := initial_log_target_bounds p hp x hk
  rw [initialLogIndex_eq_second,hj] at hgeom
  refine ⟨initial_squarefree_label_admissible p hp hg hc x hsq,?_,sourceRow_nonzero p x hk,hgeom.2⟩
  simpa only [sourceIdealPoint,elementNorm,eisEmbedding_norm_sq_eq_absNorm_span] using hgeom.1

end

section

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels

theorem initialSquarefreeBinCost_of_density_bound {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε Cₛ Cchild : ℝ)
    (hZ : 0 < Z) (hH : 0 < H) (hCₛ : 0 ≤ Cₛ)
    (j : SecondLogIndex) (windows : Fin 7 → ℝ → ℂ) (B : Frequency → ℝ)
    (J N : ℕ) (hB : ∀ q, 0 ≤ B q)
    (hdec : ∀ q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
      Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2)
    (hdensity :
      let s := initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)
      let X := initialLogColumn Z (primeProductNorm p R) j
      let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
      densityChildEnergy p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (sourceIdealTarget (s.image (sourceObservation p))) (windows 5) (windows 6) X X J ≤
        Cchild*(X*initialLogLabel j)^2) :
    initialSquarefreeBinCost p hp hcop hg F R Ψ m ray K Z H M ε j windows B ≤
      ((H/primeProductNorm p R)*Real.exp 4*Cchild*Cₛ)*
        ‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε /
        (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N := by
  let s := initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)
  let X := initialLogColumn Z (primeProductNorm p R) j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let E := densityChildEnergy p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
    (m*r) (sourceIdealTarget (s.image (sourceObservation p))) (windows 5) (windows 6) X X J
  let S := (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N
  have hR : 0 < primeProductNorm p R := primeProductNorm_pos p hp R
  have hk : 0 < secondLogK j := normLogScale_pos _
  have hS : 0 < S := by dsimp [S]; positivity
  have hd := initial_source_density_transfer p hp hcop hg F (secondRayMinus Ψ ray)
    (secondRayPlus Ψ ray) (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6)
    X X B J S Cₛ hS hCₛ hB (fun q => by
      simpa only [S,tripleLogDensity,mul_assoc] using hdec q)
  have hpref : 0 ≤ H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*
      (secondLogK j*Real.exp 2)^ε := by positivity
  calc
    _ ≤ (H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
        ((Cₛ/S)*E) := mul_le_mul_of_nonneg_left hd hpref
    _ ≤ (H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
        ((Cₛ/S)*(Cchild*(X*initialLogLabel j)^2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdensity (div_nonneg hCₛ hS.le)) hpref
    _ = _ := by
      dsimp only [X,S]
      rw [initial_log_mass Z (primeProductNorm p R) hR.ne',
        mul_pow (Z/primeProductNorm p R) (Real.exp 2) 2]
      have he : (Real.exp 2)^2=Real.exp 4 := by rw [pow_two,←Real.exp_add]; norm_num
      rw [he]
      have hz := hZ.ne'
      have hr := hR.ne'
      field_simp

end

section

open scoped BigOperators Classical

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels

lemma initial_bin_row_scale_le (U K : ℝ) (hK : 1 ≤ K) (j : SecondLogIndex)
    (hj : j ∈ secondLogBinBox U K) : secondLogK j ≤ K := by
  have hj' : j.1 < normLogBin U+1 ∧ j.2.1 < normLogBin U+1 ∧ j.2.2 < normLogBin K+1 := by
    simpa only [secondLogBinBox,Finset.mem_product,Finset.mem_range] using hj
  have hscale : secondLogK j ≤ normLogScale (normLogBin K) := by
    unfold secondLogK normLogScale
    apply Real.exp_le_exp.mpr
    exact_mod_cast Nat.le_of_lt_succ hj'.2.2
  exact hscale.trans (normLogBin_scale_bounds K hK).1

theorem initial_bin_cost_uniform {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M Kmax ε Cₛ Cchild : ℝ)
    (hZ : 0 < Z) (hH : 0 < H) (hKmax : 1 ≤ Kmax) (hε : 0 ≤ ε)
    (hCₛ : 0 ≤ Cₛ) (hCc : 0 ≤ Cchild)
    (j : SecondLogIndex) (hj : j ∈ secondLogBinBox (Z*Real.exp M) Kmax)
    (windows : Fin 7 → ℝ → ℂ) (B : Frequency → ℝ) (J N : ℕ)
    (hB : ∀ q, 0 ≤ B q)
    (hdec : ∀ q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
      Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2)
    (hdensity :
      let s := initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)
      let X := initialLogColumn Z (primeProductNorm p R) j
      let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
      densityChildEnergy p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (sourceIdealTarget (s.image (sourceObservation p))) (windows 5) (windows 6) X X J ≤
        Cchild*(X*initialLogLabel j)^2) :
    initialSquarefreeBinCost p hp hcop hg F R Ψ m ray K Z H M ε j windows B ≤
      (H*Real.exp 4*Cchild*Cₛ*(Kmax*Real.exp 2)^ε)/primeProductNorm p R*
        ‖secondRayCoefficient ray‖ := by
  have hb := initialSquarefreeBinCost_of_density_bound p hp hcop hg F R Ψ m ray K
    Z H M ε Cₛ Cchild hZ hH hCₛ j windows B J N hB hdec hdensity
  have hR := primeProductNorm_pos p hp R
  have hk : 0 < secondLogK j := normLogScale_pos _
  have hden : 1 ≤ (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N := by
    apply one_le_pow₀
    have hnon : 0 ≤ H*secondLogK j*(primeProductNorm p R)^2/Z^2 := by positivity
    linarith
  have hnum : 0 ≤ ((H/primeProductNorm p R)*Real.exp 4*Cchild*Cₛ)*
      ‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε := by positivity
  have hrow : (secondLogK j*Real.exp 2)^ε ≤ (Kmax*Real.exp 2)^ε :=
    Real.rpow_le_rpow (mul_pos hk (Real.exp_pos 2)).le
    (mul_le_mul_of_nonneg_right (initial_bin_row_scale_le (Z*Real.exp M) Kmax hKmax j hj)
      (Real.exp_pos 2).le) hε
  calc
    _ ≤ ((H/primeProductNorm p R)*Real.exp 4*Cchild*Cₛ)*
        ‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε :=
      hb.trans (div_le_self hnum hden)
    _ ≤ ((H/primeProductNorm p R)*Real.exp 4*Cchild*Cₛ)*
        ‖secondRayCoefficient ray‖*(Kmax*Real.exp 2)^ε :=
      mul_le_mul_of_nonneg_left hrow (by positivity)
    _ = _ := by ring

end

open ActualEisensteinCubic ConcretePrimeRowBridge

theorem outside_prime_divisor_mem_pool (S : Finset (Ideal O)) (D : ℕ)
    {I Q : Ideal O} (hI : I ∈ outsideIdealsUpTo S D) (hQ : Prime Q)
    (hd : Q ∣ I) : Q ∈ primePool (outsideSquarefreeIdeals S D) := by
  have hQpos : 1 ≤ Ideal.absNorm Q := Nat.one_le_iff_ne_zero.mpr
    (fun hz => hQ.ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
  have hQI : Ideal.absNorm Q ≤ Ideal.absNorm I :=
    Nat.le_of_dvd (mem_outsideIdealsUpTo.mp hI).1 (map_dvd Ideal.absNorm hd)
  have hQo : Q ∈ outsideIdealsUpTo S D := mem_outsideIdealsUpTo.mpr
    ⟨hQpos, hQI.trans (mem_outsideIdealsUpTo.mp hI).2.1,
      fun P hP hPQ => (mem_outsideIdealsUpTo.mp hI).2.2 P hP (hPQ.trans hd)⟩
  apply mem_primePool_iff.mpr
  refine ⟨Q, Finset.mem_filter.mpr ⟨hQo,hQ.squarefree⟩,?_⟩
  exact (UniqueFactorizationMonoid.mem_normalizedFactors_iff hQ.ne_zero).mpr
    ⟨hQ,dvd_rfl⟩

theorem outside_factors_mem_pool (S : Finset (Ideal O)) (D : ℕ)
    {I : Ideal O} (hI : I ∈ outsideIdealsUpTo S D) :
    ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors I,
      Q ∈ primePool (outsideSquarefreeIdeals S D) := by
  intro Q hQ
  obtain ⟨hprime,hdiv⟩ :=
    (UniqueFactorizationMonoid.mem_normalizedFactors_iff
      (outsideIdealsUpTo_ne_bot S D I hI)).mp hQ
  exact outside_prime_divisor_mem_pool S D hI hprime hdiv

theorem outside_prime_mem_pool (S : Finset (Ideal O)) (D : ℕ)
    {Q : Ideal O} (hQ : Prime Q) (hQD : Ideal.absNorm Q ≤ D)
    (hQS : ∀ P ∈ S, ¬ P ∣ Q) :
    Q ∈ primePool (outsideSquarefreeIdeals S D) := by
  apply outside_prime_divisor_mem_pool S D (I := Q) _ hQ dvd_rfl
  exact mem_outsideIdealsUpTo.mpr
    ⟨Nat.one_le_iff_ne_zero.mpr
      (fun hz => hQ.ne_zero (Ideal.absNorm_eq_zero_iff.mp hz)),hQD,hQS⟩

end

section

open MeasureTheory
open scoped BigOperators Classical

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)

def initialElementaryConstant (A V : ℝ) : ℝ := 6*128^4*(Real.exp A*V)^2

lemma initialElementaryConstant_nonneg (A V : ℝ) : 0 ≤ initialElementaryConstant A V := by
  unfold initialElementaryConstant
  positivity

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
  (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hc hinj in

theorem initial_child_energy_elementary (F : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (T : Finset (Ideal O × O)) (V : ℝ → ℂ)
    (X lengthScale K A Vmax a b : ℝ) (hX : 0 < X) (hL : 1 ≤ lengthScale) (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax)
    (hV : ∀ t,‖V t‖ ≤ Vmax) (hs : ∀ t,V t ≠ 0 → |t| ≤ A)
    (hT : ∀ z ∈ T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) (tn rn : Bool) :
    childEnergy p hp hcop hg F Ψ m T V X tn rn a b ≤
      initialElementaryConstant A Vmax*K*X^2*lengthScale := by
  by_cases hscale : 1 ≤ X*Real.exp A
  · have hb := childEnergy_elementary_normalized p hp hcop hg hc hinj F Ψ hΨ m T V
      X lengthScale K A Vmax a b hX hL hK hA hVmax hV hs hT tn rn
    have hXL : 0 < X*lengthScale := mul_pos hX (zero_lt_one.trans_le hL)
    have hb' := (div_le_iff₀ hXL).mp hb
    rw [max_eq_right hscale] at hb'
    convert hb' using 1
    unfold initialElementaryConstant
    field_simp

  · rw [childEnergy_subunit p hp hcop hg F Ψ m T V X A hX hs
      (lt_of_not_ge hscale) a b tn rn]
    exact mul_nonneg (mul_nonneg (mul_nonneg (initialElementaryConstant_nonneg A Vmax)
      (zero_le_one.trans hK)) (sq_nonneg X)) (zero_le_one.trans hL)

include hc hinj in

theorem initial_child_geometric_elementary (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (hΨ₁ : ∀ a,‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a,‖Ψ₂ a‖ ≤ 1)
    (m : O) (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ)
    (X lengthScale K A Vmax : ℝ) (hX : 0 < X) (hL : 1 ≤ lengthScale) (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (hT : ∀ z ∈ T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) (q : Frequency) :
    childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X X q ≤
      initialElementaryConstant A Vmax*K*(X*lengthScale)^2 := by
  let E := initialElementaryConstant A Vmax*K*X^2*lengthScale
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg (mul_nonneg (mul_nonneg (initialElementaryConstant_nonneg A Vmax)
      (zero_le_one.trans hK)) (sq_nonneg X)) (zero_le_one.trans hL)
  have he₁ := initial_child_energy_elementary p hp hcop hg hc hinj F Ψ₁ hΨ₁ m T V₁
    X lengthScale K A Vmax q.1 q.2.2 hX hL hK hA hVmax hV₁ hs₁ hT true false
  have he₂ := initial_child_energy_elementary p hp hcop hg hc hinj F Ψ₂ hΨ₂ m T V₂
    X lengthScale K A Vmax q.2.1 q.2.2 hX hL hK hA hVmax hV₂ hs₂ hT false true
  have hb : childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X X q ≤ E := by
    calc
      _ ≤ Real.sqrt E*Real.sqrt E := mul_le_mul (Real.sqrt_le_sqrt he₁)
        (Real.sqrt_le_sqrt he₂) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = E := Real.mul_self_sqrt hE
  apply hb.trans
  calc
    E ≤ E*lengthScale := le_mul_of_one_le_right hE hL
    _ = _ := by dsimp only [E]; ring

include hp in

theorem initial_subbin_target_bounds (F R : Finset ι)
    (K : Finset ι → Finset ι → Finset O) (Z M : ℝ) (j : SecondLogIndex)
    (s : Finset (SecondExpansionData ι)) (hs : s ⊆ secondLogSector p ∅ F K R Z M j) :
    ∀ z ∈ sourceIdealTarget (s.image (sourceObservation p)),z.1 ≠ ⊥ ∧
      (Ideal.absNorm z.1 : ℝ) ≤ initialLogLabel j ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ secondLogK j*Real.exp 2 := by
  apply sourceIdealTarget_bounds
  intro z hz
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  have hx' := hs hx
  obtain ⟨hxsec,hj⟩ := Finset.mem_filter.mp hx'
  have hk := (secondSupportedSector_mem p F K R Z M x hxsec).2.2.2.1
  have hji : initialLogIndex p x=j := (initialLogIndex_eq_second p x).trans hj
  have ht := initial_log_target_bounds p hp x hk
  rw [hji] at ht
  refine ⟨?_,ht.1,?_⟩
  · exact mul_ne_zero (primeSubsetGenerator_ne_zero _ _)
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  · exact ht.2.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num))
      (normLogScale_pos _).le)

include hc hinj in

theorem initial_subbin_geometric_elementary (F R : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z M A Vmax : ℝ)
    (hZ : 0 < Z) (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax)
    (j : SecondLogIndex) (s : Finset (SecondExpansionData ι))
    (hs : s ⊆ secondLogSector p ∅ F K R Z M j) (V₁ V₂ : ℝ → ℂ)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (q : Frequency) :
    let X := initialLogColumn Z (primeProductNorm p R) j
    let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
    childGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
      (m*r) (sourceIdealTarget (s.image (sourceObservation p))) V₁ V₂ X X q ≤
      (initialElementaryConstant A Vmax*(secondLogK j*Real.exp 2))*(X*initialLogLabel j)^2 := by
  dsimp only
  have hR := FirstPassCubeLabels.primeProductNorm_pos p hp R
  have hX : 0 < initialLogColumn Z (primeProductNorm p R) j :=
    div_pos hZ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) hR)
  have hL : 1 ≤ initialLogLabel j := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (normLogScale_ge_one _) (normLogScale_ge_one _))
    (Real.one_le_exp (by norm_num))
  have hrow : 1 ≤ secondLogK j*Real.exp 2 :=
    one_le_mul_of_one_le_of_one_le (normLogScale_ge_one _) (Real.one_le_exp (by norm_num))
  exact initial_child_geometric_elementary p hp hcop hg hc hinj F
    (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
    (fun a => (secondRayMinus_norm_le Ψ ray a).trans (hΨ a))
    (fun a => (secondRayPlus_norm_le Ψ ray a).trans (hΨ a)) _ _ V₁ V₂
    _ _ _ A Vmax hX hL hrow hA hVmax hV₁ hV₂ hs₁ hs₂
    (initial_subbin_target_bounds p hp F R K Z M j s hs) q

end

open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)

def initialRestrictedBinCost {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (s : Finset (SecondExpansionData ι)) (Z H ε : ℝ) (j : SecondLogIndex)
    (V₁ V₂ : ℝ → ℂ) (B : Frequency → ℝ) : ℝ :=
  let X := initialLogColumn Z (primeProductNorm p R) j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  (H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
    (∫ t₁ : ℝ,∫ t₂ : ℝ,∫ t₃ : ℝ,B (t₁,t₂,t₃)*
      sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (s.image (sourceObservation p)) V₁ V₂ X X (t₁,t₂,t₃))

lemma initialRestrictedBinCost_full {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε : ℝ) (j : SecondLogIndex)
    (windows : Fin 7 → ℝ → ℂ) (B : Frequency → ℝ) :
    initialRestrictedBinCost p hp hcop hg F R Ψ m ray
      (secondLogSector p ∅ F K R Z M j) Z H ε j (windows 5) (windows 6) B =
    initialBinCost p hp hcop hg F R Ψ m ray K Z H M ε j windows B := rfl

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
  (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hc hinj in

theorem initial_subbin_density_elementary (F R : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M A Vmax Cs : ℝ)
    (hZ : 0 < Z) (hH : 0 < H) (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax) (hCs : 0 ≤ Cs)
    (j : SecondLogIndex) (s : Finset (SecondExpansionData ι))
    (hs : s ⊆ secondLogSector p ∅ F K R Z M j) (V₁ V₂ : ℝ → ℂ)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (B : Frequency → ℝ) (J N : ℕ) (hB : ∀ q,0 ≤ B q)
    (hdec : ∀ q,(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
      Cs*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) :
    let X := initialLogColumn Z (primeProductNorm p R) j
    let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
    (∫ t₁ : ℝ,∫ t₂ : ℝ,∫ t₃ : ℝ,B (t₁,t₂,t₃)*
      sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (s.image (sourceObservation p)) V₁ V₂ X X (t₁,t₂,t₃)) ≤
    (Cs*(initialElementaryConstant A Vmax*(secondLogK j*Real.exp 2)*(X*initialLogLabel j)^2)/
      (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N)*(∫ t : ℝ,firstLogDensity 0 t)^3 := by
  dsimp only
  let X := initialLogColumn Z (primeProductNorm p R) j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let G := sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
    (m*r) (s.image (sourceObservation p)) V₁ V₂ X X
  let E := initialElementaryConstant A Vmax*(secondLogK j*Real.exp 2)*(X*initialLogLabel j)^2
  have hk : 0 < secondLogK j := normLogScale_pos _
  have hE : 0 ≤ E := mul_nonneg
    (mul_nonneg (initialElementaryConstant_nonneg A Vmax) (mul_nonneg hk.le (Real.exp_pos _).le))
    (sq_nonneg _)
  have hG : ∀ q,0 ≤ G q := fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hbound (q : Frequency) : G q ≤ E :=
    (sourceGeometricMean_le_ideal p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
      (m*r) (s.image (sourceObservation p)) V₁ V₂ X X q).trans
    (initial_subbin_geometric_elementary p hp hcop hg hc hinj F R Ψ hΨ m ray K Z M A Vmax
      hZ hA hVmax j s hs V₁ V₂ hV₁ hV₂ hs₁ hs₂ q)
  have hweighted (q : Frequency) :
      G q ≤ E*(1+‖q.1‖)^J*(1+‖q.2.1‖)^J*(1+‖q.2.2‖)^J := by
    have h₁ := one_le_pow₀ (show 1 ≤ 1+‖q.1‖ by linarith [norm_nonneg q.1]) (n := J)
    have h₂ := one_le_pow₀ (show 1 ≤ 1+‖q.2.1‖ by linarith [norm_nonneg q.2.1]) (n := J)
    have h₃ := one_le_pow₀ (show 1 ≤ 1+‖q.2.2‖ by linarith [norm_nonneg q.2.2]) (n := J)
    exact (hbound q).trans ((le_mul_of_one_le_right hE h₁).trans
      ((le_mul_of_one_le_right (mul_nonneg hE (zero_le_one.trans h₁)) h₂).trans
        (le_mul_of_one_le_right (mul_nonneg (mul_nonneg hE (zero_le_one.trans h₁))
          (zero_le_one.trans h₂)) h₃)))
  exact polynomial_density_cost B G J _ Cs E (by positivity) hCs hE hB hG hdec hweighted

include hc hinj in

theorem initial_subbin_cost_elementary (F R : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε A Vmax Cs : ℝ)
    (hZ : 0 < Z) (hH : 0 < H) (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax) (hCs : 0 ≤ Cs)
    (j : SecondLogIndex) (s : Finset (SecondExpansionData ι))
    (hs : s ⊆ secondLogSector p ∅ F K R Z M j) (V₁ V₂ : ℝ → ℂ)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (B : Frequency → ℝ) (J N : ℕ) (hB : ∀ q,0 ≤ B q)
    (hdec : ∀ q,(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
      Cs*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) :
    initialRestrictedBinCost p hp hcop hg F R Ψ m ray s Z H ε j V₁ V₂ B ≤
    ((H/primeProductNorm p R)*Real.exp 4*
      (initialElementaryConstant A Vmax*(secondLogK j*Real.exp 2))*Cs*
      (∫ t : ℝ,firstLogDensity 0 t)^3)*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε /
      (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N := by
  have hb := initial_subbin_density_elementary p hp hcop hg hc hinj F R Ψ hΨ m ray K Z H M
    A Vmax Cs hZ hH hA hVmax hCs j s hs V₁ V₂ hV₁ hV₂ hs₁ hs₂ B J N hB hdec
  have hk : 0 < secondLogK j := normLogScale_pos _
  have hR := FirstPassCubeLabels.primeProductNorm_pos p hp R
  have hpref : 0 ≤ H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*
      (secondLogK j*Real.exp 2)^ε := by positivity
  have h := mul_le_mul_of_nonneg_left hb hpref
  apply h.trans_eq
  rw [initial_log_mass Z (primeProductNorm p R) hR.ne',mul_pow]
  have he : (Real.exp 2)^2=Real.exp 4 := by rw [pow_two,←Real.exp_add]; norm_num
  rw [he]
  have hz := hZ.ne'
  have hr := hR.ne'
  field_simp

end

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)

def initialRadial (Z H R : ℝ) (j : SecondLogIndex) : ℝ :=
  H*secondLogK j*R^2/Z^2

theorem initial_radial_absorbs_rows (Z H R k : ℝ) (N : ℕ)
    (hZ : 0 < Z) (hH : 1 ≤ H) (hR : 1 ≤ R) (hk : 0 ≤ k) :
    H*k^2/(1+H*k*R^2/Z^2)^(N+2) ≤ Z^4/(1+H*k*R^2/Z^2)^N := by
  let r := H*k*R^2/Z^2
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have h1 : 0 < 1+r := by linarith
  have hHR : 1 ≤ H*R^4 := one_le_mul_of_one_le_of_one_le hH (one_le_pow₀ hR)
  have he : Z^4*r^2=(H*k^2)*(H*R^4) := by
    dsimp [r]
    field_simp

  have hnum : H*k^2 ≤ Z^4*r^2 := by
    rw [he]
    exact le_mul_of_one_le_right (mul_nonneg hH0 (sq_nonneg k)) hHR
  change H*k^2/(1+r)^(N+2) ≤ Z^4/(1+r)^N
  calc
    _ ≤ Z^4*r^2/(1+r)^(N+2) := div_le_div_of_nonneg_right hnum (pow_nonneg h1.le _)
    _ ≤ Z^4*(1+r)^2/(1+r)^(N+2) := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg h1.le _)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr (by linarith) 2) (by positivity)
    _ = _ := by rw [pow_add]; field_simp

def initialHighRadialConstant (A Vmax Cs : ℝ) : ℝ :=
  Real.exp 8*initialElementaryConstant A Vmax*Cs*(∫ t : ℝ,firstLogDensity 0 t)^3

lemma initialHighRadialConstant_nonneg (A Vmax Cs : ℝ) (hCs : 0 ≤ Cs) :
    0 ≤ initialHighRadialConstant A Vmax Cs := by
  have hi : 0 ≤ ∫ t : ℝ,firstLogDensity 0 t := integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have hc := initialElementaryConstant_nonneg A Vmax
  unfold initialHighRadialConstant
  positivity

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
  (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hc hinj in

theorem initial_subbin_cost_radial_decay (F R : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε A Vmax Cs : ℝ)
    (hZ : 0 < Z) (hH : 1 ≤ H) (hε : ε ≤ 1)
    (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax) (hCs : 0 ≤ Cs)
    (j : SecondLogIndex) (s : Finset (SecondExpansionData ι))
    (hs : s ⊆ secondLogSector p ∅ F K R Z M j) (V₁ V₂ : ℝ → ℂ)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (B : Frequency → ℝ) (J N : ℕ) (hB : ∀ q,0 ≤ B q)
    (hdec : ∀ q,(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2)*B q ≤
      Cs*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) :
    initialRestrictedBinCost p hp hcop hg F R Ψ m ray s Z H ε j V₁ V₂ B ≤
      initialHighRadialConstant A Vmax Cs*Z^4/primeProductNorm p R*
        ‖secondRayCoefficient ray‖/(1+initialRadial Z H (primeProductNorm p R) j)^N := by
  have hH0 := zero_lt_one.trans_le hH
  have hb := initial_subbin_cost_elementary p hp hcop hg hc hinj F R Ψ hΨ m ray K Z H M
    ε A Vmax Cs hZ hH0 hA hVmax hCs j s hs V₁ V₂ hV₁ hV₂ hs₁ hs₂ B J (N+2) hB hdec
  have hR1 := primeProductNorm_ge_one p hp R
  have hR0 := zero_lt_one.trans_le hR1
  have hk : 0 < secondLogK j := normLogScale_pos _
  have hrow : 1 ≤ secondLogK j*Real.exp 2 :=
    one_le_mul_of_one_le_of_one_le (normLogScale_ge_one _) (Real.one_le_exp (by norm_num))
  have hrowpow : (secondLogK j*Real.exp 2)^ε ≤ secondLogK j*Real.exp 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hrow hε
  have hcc := initialElementaryConstant_nonneg A Vmax
  have hi : 0 ≤ ∫ t : ℝ,firstLogDensity 0 t := integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have hfixed := initialHighRadialConstant_nonneg A Vmax Cs hCs
  have hpref : 0 ≤ ((H/primeProductNorm p R)*Real.exp 4*
      (initialElementaryConstant A Vmax*(secondLogK j*Real.exp 2))*Cs*
      (∫ t : ℝ,firstLogDensity 0 t)^3)*‖secondRayCoefficient ray‖ := by positivity
  have hden : 0 ≤ (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2) := by positivity
  apply hb.trans
  calc
    _ ≤ ((H/primeProductNorm p R)*Real.exp 4*
        (initialElementaryConstant A Vmax*(secondLogK j*Real.exp 2))*Cs*
        (∫ t : ℝ,firstLogDensity 0 t)^3)*‖secondRayCoefficient ray‖*
        (secondLogK j*Real.exp 2)/(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrowpow hpref) hden
    _ = (initialHighRadialConstant A Vmax Cs/primeProductNorm p R*‖secondRayCoefficient ray‖)*
        (H*(secondLogK j)^2/(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2)) := by
      unfold initialHighRadialConstant
      have he : Real.exp 4*(Real.exp 2)^2=Real.exp 8 := by
        rw [pow_two,←Real.exp_add,←Real.exp_add]; norm_num
      rw [←he]
      ring
    _ ≤ (initialHighRadialConstant A Vmax Cs/primeProductNorm p R*‖secondRayCoefficient ray‖)*
        (Z^4/(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N) :=
      mul_le_mul_of_nonneg_left (initial_radial_absorbs_rows Z H (primeProductNorm p R)
        (secondLogK j) N hZ hH hR1 hk.le) (by positivity)
    _ = _ := by unfold initialRadial; ring

end InitialMeanSquare

end

end OAI
