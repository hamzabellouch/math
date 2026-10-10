import OAI.NumberTheory.DirichletL.CubicSieve.DyadicKernel

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

namespace InitialMeanSquare

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)

lemma star_normalizedColumn {ι : Type*} (p : ι → O) (g : 𝓢(ℝ,ℂ))
    (Z : ℝ) (S : Finset ι) :
    star (normalizedColumn p (fun T => g (columnLog p Z T)) S) =
      normalizedColumn p (fun T => conjugateProfile g (columnLog p Z T)) S := by
  simp only [normalizedColumn, conjugateProfile_apply]
  simp

lemma conjugateProfile_support_bound (g : 𝓢(ℝ,ℂ)) (A : ℝ)
    (hg : ∀ t, g t ≠ 0 → |t| ≤ A) :
    ∀ t, conjugateProfile g t ≠ 0 → |t| ≤ A := by
  intro t ht
  apply hg t
  intro hz
  apply ht
  simp only [conjugateProfile_apply, hz, star_zero]

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem initial_nonzero_source_eq_bins
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda^2 ∣ p i-1) (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (g W : 𝓢(ℝ,ℂ)) (Z H M Kmax : ℝ) (hZ : 0 < Z)
    (hgM : ∀ t, g t ≠ 0 → |t| ≤ M)
    (K : Finset ι → Finset ι → Finset O)
    (hK : ∀ R ∈ F.powerset, ∀ x ∈ secondSupportedSector p F K R Z M,
      elementNorm (sourceObservation p x).1 ≤ Kmax) :
    let G := fun S => normalizedColumn p (fun T => g (columnLog p Z T)) S
    truncatedSecondSource p hp hg hinj F Ψ m 1 1 G W H (fun C E => (K C E).erase 0) =
      ∑ ray : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F (Z*Real.exp M),
        ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,
          secondExpansionSource p hp hcop hg F Ψ m 1 1 ray
            (secondLogSector p ∅ F K R Z M j) G G W H := by
  dsimp only
  have hrow : ∀ R ∈ F.powerset, ∀ x ∈ secondSupportedSector p F K R Z M,
      ‖eisEmbedding (actualSecondRow p ∅ x.divisor x.frequency)‖^2 ≤ Kmax := by
    intro R hR x hx
    simpa only [initial_actual_row_norm] using hK R hR x hx
  have hfull := truncatedSecondSource_eq_binned p hp hcop hg hinj hc hpr ∅ F Ψ m 1 1
    g W Z H M Kmax hZ hgM K hrow
  have hsplit := truncatedSecondSource_eq_nonzero_add_zero p hp hg hinj F Ψ m 1 1
    (fun S => normalizedColumn p (fun T => g (columnLog p Z T)) S) W H K
  dsimp only at hfull
  rw [hsplit] at hfull
  exact add_left_cancel (by simpa only [add_comm] using hfull)

theorem initial_nonzero_source_norm_le_bins
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda^2 ∣ p i-1) (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (g W : 𝓢(ℝ,ℂ)) (Z H M Kmax : ℝ) (hZ : 0 < Z)
    (hgM : ∀ t, g t ≠ 0 → |t| ≤ M)
    (K : Finset ι → Finset ι → Finset O)
    (hK : ∀ R ∈ F.powerset, ∀ x ∈ secondSupportedSector p F K R Z M,
      elementNorm (sourceObservation p x).1 ≤ Kmax) :
    let G := fun S => normalizedColumn p (fun T => g (columnLog p Z T)) S
    ‖truncatedSecondSource p hp hg hinj F Ψ m 1 1 G W H (fun C E => (K C E).erase 0)‖ ≤
      ∑ ray : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F (Z*Real.exp M),
        ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray
            (secondLogSector p ∅ F K R Z M j) G G W H‖ := by
  dsimp only
  rw [initial_nonzero_source_eq_bins p hp hcop hg hinj hc hpr F Ψ m g W Z H M Kmax hZ hgM K hK]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro ray hray
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro R hR
  exact norm_sum_le _ _

end

open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog firstLogDensity)

def initialBinCost {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε : ℝ) (j : SecondLogIndex)
    (windows : Fin 7 → ℝ → ℂ) (B : Frequency → ℝ) : ℝ :=
  let s := secondLogSector p ∅ F K R Z M j
  let X := initialLogColumn Z (primeProductNorm p R) j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  (H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
    (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, B (t₁,t₂,t₃)*
      sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X (t₁,t₂,t₃))

theorem initial_nonzero_source_transfer
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0 ≤ A)
    (hU : ∀ t, g t ≠ 0 → U t=1) (hgA : ∀ t, g t ≠ 0 → |t| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (N J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C Cₛ : ℝ), 0 ≤ C ∧ 0 ≤ Cₛ ∧
      (∀ i, HasCompactSupport (windows i)) ∧ (∀ i, ContDiff ℝ ∞ (windows i)) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
        [∀ i, (Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀ i, lambda ∉ Ideal.span {p i})
        (hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
        (_hpr : ∀ i, lambda^2 ∣ p i-1)
        (F : Finset ι) (Ψ : O →* ℂ) (m : O)
        (K : Finset ι → Finset ι → Finset O) (Z H Kmax : ℝ),
        0 < Z → 0 < H → (∀ a, ‖Ψ a‖ ≤ 1) →
        (∀ R ∈ F.powerset, ∀ x ∈ secondSupportedSector p F K R Z A,
          elementNorm (sourceObservation p x).1 ≤ Kmax) →
        ∃ B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ,
          (∀ ray R j q, 0 ≤ B ray R j q) ∧
          (∀ ray R j q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B ray R j q ≤
            Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) ∧
          ‖truncatedSecondSource p hp hg hinj F Ψ m 1 1
            (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V)
            W H (fun C E => (K C E).erase 0)‖ ≤
            C*(∑ ray : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F (Z*Real.exp A),
              ∑ j ∈ secondLogBinBox (Z*Real.exp A) Kmax,
                initialBinCost p hp hcop hg F R Ψ m ray K Z H A ε j windows (B ray R j)) := by
  obtain ⟨windows,C,Cₛ,hC,hCₛ,hwc,hws,ht⟩ :=
    initial_bin_transfer U hUc hUs g W A hA hU hgA ε hε N J
  refine ⟨windows,C,Cₛ,hC,hCₛ,hwc,hws,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr F Ψ m K Z H Kmax hZ hH hΨ hK
  let B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ :=
    fun ray R j => Classical.choose
      (ht p hp hcop hg hinj hc hpr F R Ψ m ray K Z H A j hZ hH hΨ)
  have hB (ray : SecondRayIndex) (R : Finset ι) (j : SecondLogIndex) :=
    Classical.choose_spec (ht p hp hcop hg hinj hc hpr F R Ψ m ray K Z H A j hZ hH hΨ)
  refine ⟨B,fun ray R j => (hB ray R j).1,fun ray R j => (hB ray R j).2.1,?_⟩
  apply (initial_nonzero_source_norm_le_bins p hp hcop hg hinj hc hpr F Ψ m
    g W Z H A Kmax hZ hgA K hK).trans
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ray hray
  apply Finset.sum_le_sum
  intro R hR
  apply Finset.sum_le_sum
  intro j hj
  convert (hB ray R j).2.2 using 1 ; dsimp only [initialBinCost, B] ; ring

end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap ContDiff
namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic

theorem completed_smooth_series_rowPhase
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (hV₀n : ∀y,‖V₀ y‖≤1) (hV₁n : ∀y,‖V₁ y‖≤1) (hV₂n : ∀y,‖V₂ y‖≤1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ρ q : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) :
    ∃C : ℝ,0<C ∧ ∀K Y H : ℝ,1≤K → 0<Y → 0<H →
    ∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal O),
      (∀i,∀I∈S i,I≠0 ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀I∈T i,I≠0 ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.1) →
    ∀β : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖β i n v‖≤
        1/(Real.sqrt ((2:ℝ)^i.2.2)*(2:ℝ)^i.2.1*ramifiedScale ρ q i.1*Real.sqrt H)) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange K→ℂ,(∀i k,‖σ i k‖≤1) →
      (∀k,Summable (fun i => ‖σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ W K Y ρ q S T β i k‖)) ∧
      (∑k : idealRange K,‖∑'i : ℕ×ℕ×ℕ,
        σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ W K Y ρ q S T β i k‖^2)
        ≤C*(K*Y)^(2*deltaLoss)*(K+Y)/H := by
  obtain ⟨A,hA⟩ := exists_nat_gt (deltaLoss+1/2)
  obtain ⟨Cq,hCq,hquad⟩ := completed_smooth_quadratic V₀ V₁ V₂ M₀ M₁ M₂
    hM₀ hM₁ hM₂ hV₀ hV₁ hV₂ hV₀n hV₁n hV₂n W a b ha hsupp hW A (2*deltaLoss) (by positivity)
  obtain ⟨Cs,hCs,hsum⟩ := normMajorant_sum_bound deltaLoss A ρ q hδ hA hρ hq
  refine ⟨2*Cq*Cs^2,by positivity,?_⟩
  intro K Y H hK hY hH S T hS hT β hβ σ hσ
  have hKp : 0<K := by linarith
  have hqp : 0<q := by linarith
  let g : (ℕ×ℕ×ℕ)→ℝ := fun i => Real.sqrt Cq *
    normMajorant deltaLoss A K Y⁻¹ (ramifiedScale ρ q i.1) H ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)
  have hg0 (i : ℕ×ℕ×ℕ) : 0≤g i := by
    dsimp [g]
    exact mul_nonneg (Real.sqrt_nonneg _) (normMajorant_nonneg _ _ _ _ _ _ _ _
      hKp (by positivity) (ramifiedScale_pos ρ q hρ hqp _) hH (by positivity) (by positivity))
  have henergy (i : ℕ×ℕ×ℕ) :
      (∑k : idealRange K,‖σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ W K Y ρ q S T β i k‖^2)
        ≤(g i)^2 := by
    let U : ℝ := (2:ℝ)^i.2.2
    let B : ℝ := (2:ℝ)^i.2.1
    let r : ℝ := ramifiedScale ρ q i.1
    let R : ℝ := Y⁻¹*r^3*B^3*U
    have hU : 1≤U := one_le_pow₀ (by norm_num)
    have hB : 1≤B := one_le_pow₀ (by norm_num)
    have hUp : 0<U := by positivity
    have hBp : 0<B := by positivity
    have hr : 0<r := ramifiedScale_pos ρ q hρ hqp _
    have hR : 0<R := by dsimp [R]; positivity
    have h := hquad K U B (1/(Real.sqrt U*B*r*Real.sqrt H)) R
      hK hU hB (by positivity) hR (S i) (T i) (hS i) (hT i) (β i) (hβ i)
      (fun k => Real.log ((Ideal.absNorm k.val:ℝ)/K))
      (fun n => Real.log ((Ideal.absNorm n:ℝ)/U))
      (fun v => Real.log ((Ideal.absNorm v:ℝ)/B))
    change (∑k,‖completedSmoothDyadicBlock V₀ V₁ V₂ W K Y ρ q S T β i k‖^2)≤_ at h
    have hphase : (∑k : idealRange K,‖σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ W K Y ρ q S T β i k‖^2)≤
        ∑k : idealRange K,‖completedSmoothDyadicBlock V₀ V₁ V₂ W K Y ρ q S T β i k‖^2 := by
      apply Finset.sum_le_sum
      intro k _
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hσ i k)
    apply (hphase.trans h).trans
    have he : Cq*(K*(U*B))^(2*deltaLoss)*(K+U*B)*(U*B)*
        (1/(Real.sqrt U*B*r*Real.sqrt H))^2/(1+R)^(2*A)=
        Cq*((K*(U*B))^(2*deltaLoss)*(K+U*B)/(B*r^2*H)/(1+R)^(2*(A:ℝ))) := by
      rw [show 2*(A:ℝ)=((2*A:ℕ):ℝ) by norm_num,Real.rpow_natCast]
      simp only [one_div,inv_pow,mul_pow,Real.sq_sqrt hUp.le,Real.sq_sqrt hH.le]
      field_simp

    rw [he]
    have hm := smooth_energy_le_normMajorant_sq deltaLoss A K Y⁻¹ r H U B
      hKp (by positivity) hr hH hUp hBp
    calc
      _ ≤ Cq*(normMajorant deltaLoss A K Y⁻¹ r H U B)^2 := mul_le_mul_of_nonneg_left hm hCq.le
      _ = (g i)^2 := by dsimp [g,U,B,r]; rw [mul_pow,Real.sq_sqrt hCq.le]
  obtain ⟨hs,hb⟩ := hsum K Y H hKp hY hH
  have hm := finite_tsum_energy_bound
    (fun i k => σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ W K Y ρ q S T β i k) g hg0
    (hs.mul_left (Real.sqrt Cq)) henergy
  refine ⟨hm.1,hm.2.trans ?_⟩
  have hb' : (∑'i,g i)≤Real.sqrt Cq*(Cs*(K*Y)^deltaLoss*(Real.sqrt K+Real.sqrt Y)/Real.sqrt H) := by
    rw [show g=(fun i => Real.sqrt Cq*normMajorant deltaLoss A K Y⁻¹
      (ramifiedScale ρ q i.1) H ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)) from rfl,tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
  have hsq := pow_le_pow_left₀ (tsum_nonneg hg0) hb' 2
  apply hsq.trans
  have hroot : (Real.sqrt K+Real.sqrt Y)^2≤2*(K+Y) := by
    nlinarith [Real.sq_sqrt hKp.le,Real.sq_sqrt hY.le,
      sq_nonneg (Real.sqrt K-Real.sqrt Y)]
  simp only [mul_pow,div_pow,Real.sq_sqrt hCq.le,Real.sq_sqrt hH.le]
  have hp : ((K*Y)^deltaLoss)^2=(K*Y)^(2*deltaLoss) := by
    rw [←Real.rpow_mul_natCast (mul_pos hKp hY).le]
    congr 1
    ring
  rw [hp]
  calc
    _ ≤ Cq*(Cs^2*(K*Y)^(2*deltaLoss)*(2*(K+Y))/H) := by
      apply mul_le_mul_of_nonneg_left _ hCq.le
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hroot (by positivity)) hH.le
    _ = _ := by ring

end

open ActualEisensteinCubic

theorem completed_fiber_scalar_cost (deltaLoss K X a t Q c D S E : ℝ)
    (hδ : 0≤deltaLoss) (hK : 1≤K) (hX : 1≤X) (ha : 1≤a) (ht : 1≤t) (hQ : 1≤Q)
    (hc0 : 0<c) (hc : c≤K*Q) (hD : 1≤D) (hS : 1≤S) (hE : 1≤E)
    (hcost : c^2/(D*S*E^4)≤a*t^2*Q) :
    let k := K/(a*t)
    let y := k^2*c^2/(X*D*E^3)
    (k*y)^(2*deltaLoss)*(k+y)/(S*E)≤(K*Q)^(10*deltaLoss)*(K+K^2*Q/X)/a := by
  dsimp only
  let k : ℝ := K/(a*t)
  let y : ℝ := k^2*c^2/(X*D*E^3)
  change (k*y)^(2*deltaLoss)*(k+y)/(S*E)≤_
  have ha0 : 0<a := by linarith
  have ht0 : 0<t := by linarith
  have hX0 : 0<X := by linarith
  have hD0 : 0<D := by linarith
  have hS0 : 0<S := by linarith
  have hE0 : 0<E := by linarith
  have hK0 : 0<K := by linarith
  have hQ0 : 0<Q := by linarith
  have hk0 : 0<k := by dsimp [k]; positivity
  have hy0 : 0<y := by dsimp [y]; positivity
  have hat : 1≤a*t := one_le_mul_of_one_le_of_one_le ha ht
  have hk : k≤K := (div_le_self hK0.le hat)
  have hden : 1≤X*D*E^3 := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hX hD) (one_le_pow₀ hE)
  have hy : y≤K^2*(K*Q)^2 := by
    calc
      y ≤ k^2*c^2 := div_le_self (by positivity) hden
      _ ≤ K^2*(K*Q)^2 := mul_le_mul
        (pow_le_pow_left₀ hk0.le hk 2) (pow_le_pow_left₀ hc0.le hc 2) (by positivity) (by positivity)
  have hky : k*y≤(K*Q)^5 := by
    have hQ3 : 1≤Q^3 := one_le_pow₀ hQ
    calc
      k*y ≤ K*(K^2*(K*Q)^2) := mul_le_mul hk hy hy0.le hK0.le
      _ ≤ (K*(K^2*(K*Q)^2))*Q^3 := le_mul_of_one_le_right (by positivity) hQ3
      _ = (K*Q)^5 := by ring
  have hp : (k*y)^(2*deltaLoss)≤(K*Q)^(10*deltaLoss) := by
    have hh := Real.rpow_le_rpow (mul_pos hk0 hy0).le hky (by positivity : 0≤2*deltaLoss)
    convert hh using 1
    rw [←Real.rpow_natCast_mul (mul_pos hK0 hQ0).le]
    congr 1
    ring
  have hfirst : k/(S*E)≤K/a := by
    have hse : 1≤t*(S*E) := one_le_mul_of_one_le_of_one_le ht (one_le_mul_of_one_le_of_one_le hS hE)
    calc
      k/(S*E) = (K/a)/(t*(S*E)) := by dsimp [k]; field_simp
      _ ≤ K/a := div_le_self (by positivity) hse
  have hsecond : y/(S*E)≤K^2*Q/(a*X) := by
    calc
      y/(S*E) = (k^2/X)*(c^2/(D*S*E^4)) := by dsimp [y]; field_simp
      _ ≤ (k^2/X)*(a*t^2*Q) := mul_le_mul_of_nonneg_left hcost (by positivity)
      _ = K^2*Q/(a*X) := by dsimp [k]; field_simp
  have hshape : (k+y)/(S*E)≤(K+K^2*Q/X)/a := by
    rw [add_div]
    have hh := add_le_add hfirst hsecond
    convert hh using 1
    field_simp
  calc
    _ = (k*y)^(2*deltaLoss)*((k+y)/(S*E)) := by ring
    _ ≤ (K*Q)^(10*deltaLoss)*((K+K^2*Q/X)/a) :=
      mul_le_mul hp hshape (by positivity) (by positivity)
    _ = _ := by ring

theorem completed_conductor_norm_bound {ι : Type*} [Fintype ι]
    (I Q : Ideal O) (hI : I≠0) (hQ : Q≠0)
    (P : ι→Ideal O) (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀i,P i∣I*Q) :
    (Ideal.absNorm (∏i,P i):ℝ)≤(Ideal.absNorm I:ℝ)*(Ideal.absNorm Q:ℝ) := by
  have hd : (∏i,P i)∣I*Q := Fintype.prod_dvd_of_coprime hcop hpool
  have hn : 0<Ideal.absNorm (I*Q) := Nat.pos_of_ne_zero (fun hz =>
    mul_ne_zero hI hQ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hh := Nat.le_of_dvd hn (map_dvd Ideal.absNorm hd)
  exact_mod_cast (by simpa only [map_mul] using hh)

theorem completed_actual_fiber_cost {ι : Type*} [Fintype ι]
    (deltaLoss K X : ℝ) (hδ : 0≤deltaLoss) (hK : 1≤K) (hX : 1≤X)
    (I F Q : Ideal O) (hI : I≠0) (hQ : Q≠0) (hIK : (Ideal.absNorm I:ℝ)≤K)
    (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀i,P i∣I*Q) (hres : ∀i,¬P i∣rowResidualPart I Q) (e : ι→Fin 3) :
    let j := fun i => completedLocalExponent I F (P i)
    let k := K/((Ideal.absNorm (rowPowerfulPart I):ℝ)*(Ideal.absNorm (rowMaskPart I Q):ℝ))
    let D := (Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)
    let S := (Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)
    let E := (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)
    let y := k^2*(Ideal.absNorm (∏i,P i):ℝ)^2/(X*D*E^3)
    (k*y)^(2*deltaLoss)*(k+y)/(S*E)≤
      (K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
        (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  have hn (J : Ideal O) (hJ : J≠0) : 1≤(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hJ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hprod : (∏i,P i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i))
  have hc := (completed_conductor_norm_bound I Q hI hQ P hcop hpool).trans
    (mul_le_mul_of_nonneg_right hIK (Nat.cast_nonneg _))
  have hh := completed_fiber_scalar_cost deltaLoss K X
    (Ideal.absNorm (rowPowerfulPart I):ℝ) (Ideal.absNorm (rowMaskPart I Q):ℝ)
    (Ideal.absNorm Q:ℝ) (Ideal.absNorm (∏i,P i):ℝ)
    (Ideal.absNorm (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 1):ℝ)
    (Ideal.absNorm (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 0):ℝ)
    (Ideal.absNorm (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 2):ℝ)
    hδ hK hX (hn _ (rowPowerfulPart_ne_zero I))
    (hn _ (squarefreeMaskPart_ne_zero (rowSimplePart I) Q)) (hn _ hQ)
    (lt_of_lt_of_le (by norm_num) (hn _ hprod)) hc
    (hn _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) _ e 1))
    (hn _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) _ e 0))
    (hn _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) _ e 2))
    (reflectionConductorCost_bound I F Q hI hQ P hcop hpool hres e)
  exact hh

def completedShellWindow (x : ℝ) : ℂ :=
  if -Real.log 2≤x ∧ x≤0 then 1 else 0

theorem completedShellWindow_support (x : ℝ) (h : completedShellWindow x≠0) :
    |x|≤Real.log 2 := by
  have hx : -Real.log 2≤x ∧ x≤0 := by
    by_contra hn
    exact h (by simp [completedShellWindow,hn])
  apply abs_le.mpr
  exact ⟨hx.1,hx.2.trans (Real.log_nonneg (by norm_num))⟩

theorem completedShellWindow_norm (x : ℝ) : ‖completedShellWindow x‖≤1 := by
  unfold completedShellWindow
  split_ifs <;> simp

theorem completedShellWindow_log (x U : ℝ) (hx : 0<x) (hU : 0<U)
    (hlo : U/2≤x) (hhi : x≤U) : completedShellWindow (Real.log (x/U))=1 := by
  apply ite_eq_left
  constructor
  · have hhalf : (1/2:ℝ)≤x/U := (le_div_iff₀ hU).mpr (by linarith)
    have hh := Real.strictMonoOn_log.monotoneOn (by norm_num : (1/2:ℝ)∈Set.Ioi 0)
      (show x/U∈Set.Ioi 0 from div_pos hx hU) hhalf
    simpa only [one_div,Real.log_inv] using hh
  · exact Real.log_nonpos (div_nonneg hx.le hU.le) ((div_le_one hU).mpr hhi)

theorem dyadic_root_product_bound (u v U B : ℝ) (hu : 0<u) (_hv : 0<v)
    (hU : 0<U) (hB : 0<B) (huU : U/2≤u) (hvB : B/2≤v) :
    Real.sqrt U*B≤4*(Real.sqrt u*v) := by
  have hs : Real.sqrt U≤2*Real.sqrt u := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt hU.le,Real.sq_sqrt hu.le]
    nlinarith
  calc
    _ ≤ (2*Real.sqrt u)*(2*v) := mul_le_mul hs (by linarith) hB.le (by positivity)
    _ = _ := by ring

def reflectedDyadicCoefficient {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (η : Ideal O→Ideal O→ℂ) (r : ℝ)
    (n v : Ideal O) : ℂ :=
  η n v*reflectedBranch P hg j e
    (primaryGenerator (reflectionExtractedDivisor P j e 1*n))
    (primaryGenerator (reflectionExtractedDivisor P j e 2*v))/
    ((4*r*Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 1*n):ℝ)*
      (Ideal.absNorm (reflectionExtractedDivisor P j e 2*v):ℝ):ℝ):ℂ)

theorem reflectedDyadicCoefficient_norm {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (η : Ideal O→Ideal O→ℂ) (r U B : ℝ)
    (hr : 0<r) (hU : 0<U) (hB : 0<B) (n v : Ideal O) (hn : n≠0) (hv : v≠0)
    (hη : ‖η n v‖≤1) (hlo : U/2≤(Ideal.absNorm n:ℝ)) (hlov : B/2≤(Ideal.absNorm v:ℝ)) :
    ‖reflectedDyadicCoefficient P hg j e η r n v‖≤
      1/(Real.sqrt U*B*r*Real.sqrt
        ((Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)*
          (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ))) := by
  let D := reflectionExtractedDivisor P j e 1
  let E := reflectionExtractedDivisor P j e 2
  let S := reflectionExtractedDivisor P j e 0
  have hnorm (J : Ideal O) (hJ : J≠0) : 0<(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hJ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hDn := hnorm D (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) j e 1)
  have hEn := hnorm E (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) j e 2)
  have hSn := hnorm S (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) j e 0)
  have hnn := hnorm n hn
  have hvn := hnorm v hv
  have hlocal := reflectedBranch_normalized_bound P hg j e
    (primaryGenerator (D*n)) (primaryGenerator (E*v))
    (Ideal.absNorm n:ℝ) (Ideal.absNorm v:ℝ) hnn hvn
  change ‖reflectedBranch P hg j e (primaryGenerator (D*n)) (primaryGenerator (E*v))‖ /
      (Real.sqrt ((Ideal.absNorm D:ℝ)*(Ideal.absNorm n:ℝ))*
        ((Ideal.absNorm E:ℝ)*(Ideal.absNorm v:ℝ)))≤
      1/(Real.sqrt (Ideal.absNorm n:ℝ)*(Ideal.absNorm v:ℝ)*
        Real.sqrt ((Ideal.absNorm S:ℝ)*(Ideal.absNorm E:ℝ))) at hlocal
  have hbase : 0<Real.sqrt ((Ideal.absNorm S:ℝ)*(Ideal.absNorm E:ℝ)) := by positivity
  have hroot := dyadic_root_product_bound _ _ U B hnn hvn hU hB hlo hlov
  unfold reflectedDyadicCoefficient
  change ‖η n v*reflectedBranch P hg j e (primaryGenerator (D*n)) (primaryGenerator (E*v))/
    ((4*r*Real.sqrt (Ideal.absNorm (D*n):ℝ)*(Ideal.absNorm (E*v):ℝ):ℝ):ℂ)‖≤_
  rw [norm_div,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  simp only [map_mul,Nat.cast_mul]
  calc
    _ ≤ ‖reflectedBranch P hg j e (primaryGenerator (D*n)) (primaryGenerator (E*v))‖/
      (4*r*Real.sqrt ((Ideal.absNorm D:ℝ)*(Ideal.absNorm n:ℝ))*
        ((Ideal.absNorm E:ℝ)*(Ideal.absNorm v:ℝ))) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_of_le_one_left (norm_nonneg _) hη
    _ = (1/(4*r))*(‖reflectedBranch P hg j e (primaryGenerator (D*n)) (primaryGenerator (E*v))‖/
      (Real.sqrt ((Ideal.absNorm D:ℝ)*(Ideal.absNorm n:ℝ))*
        ((Ideal.absNorm E:ℝ)*(Ideal.absNorm v:ℝ)))) := by ring
    _ ≤ (1/(4*r))*(1/(Real.sqrt (Ideal.absNorm n:ℝ)*(Ideal.absNorm v:ℝ)*
      Real.sqrt ((Ideal.absNorm S:ℝ)*(Ideal.absNorm E:ℝ)))) :=
        mul_le_mul_of_nonneg_left hlocal (by positivity)
    _ = 1/(4*(Real.sqrt (Ideal.absNorm n:ℝ)*(Ideal.absNorm v:ℝ))*r*
      Real.sqrt ((Ideal.absNorm S:ℝ)*(Ideal.absNorm E:ℝ))) := by ring
    _ ≤ _ := by
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hroot hr.le) hbase.le

open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic

def reflectedBranchBlock {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (W : ℝ→ℂ) (K Y ρ q : ℝ)
    (S T : (ℕ×ℕ×ℕ)→Finset (Ideal O))
    (η : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ)
    (σ : (ℕ×ℕ×ℕ)→idealRange K→ℂ) (i : ℕ×ℕ×ℕ) (k : idealRange K) : ℂ :=
  σ i k*completedSmoothDyadicBlock completedShellWindow completedShellWindow completedShellWindow
    W K Y ρ q S T (fun v => reflectedDyadicCoefficient P hg j e (η v) (ramifiedScale ρ q v.1)) i k

theorem completed_reflected_branch_series
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ρ q : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) :
    ∃C : ℝ,0<C ∧ ∀K Y : ℝ,1≤K → 0<Y →
    ∀{ι : Type*} [Fintype ι] (P : ι→Ideal O) [∀i,(P i).IsMaximal]
      (hg : ∀i,lambda∉P i) (j : ι→ℕ) (e : ι→Fin 3),
    ∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal O),
      (∀i,∀I∈S i,I≠0 ∧ (2:ℝ)^i.2.2/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀I∈T i,I≠0 ∧ (2:ℝ)^i.2.1/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.1) →
    ∀η : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖η i n v‖≤1) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange K→ℂ,(∀i k,‖σ i k‖≤1) →
      (∀k,Summable (fun i => ‖reflectedBranchBlock P hg j e W K Y ρ q S T η σ i k‖)) ∧
      (∑k : idealRange K,‖∑'i : ℕ×ℕ×ℕ,reflectedBranchBlock P hg j e W K Y ρ q S T η σ i k‖^2)
        ≤C*(K*Y)^(2*deltaLoss)*(K+Y)/
          ((Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)*
            (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)) := by
  have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  obtain ⟨C,hC,h⟩ := completed_smooth_series_rowPhase
    completedShellWindow completedShellWindow completedShellWindow (Real.log 2) (Real.log 2) (Real.log 2)
    hl hl hl completedShellWindow_support completedShellWindow_support completedShellWindow_support
    completedShellWindow_norm completedShellWindow_norm completedShellWindow_norm
    W a b ha hsupp hW deltaLoss ρ q hδ hρ hq
  refine ⟨C,hC,?_⟩
  intro K Y hK hY ι _ P _ hg j e S T hS hT η hη σ hσ
  have hn (v : Fin 3) : 0<(Ideal.absNorm (reflectionExtractedDivisor P j e v):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz =>
      reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) j e v
        (Ideal.absNorm_eq_zero_iff.mp hz))
  exact h K Y _ hK hY (mul_pos (hn 0) (hn 2)) S T
    (fun i I hI => ⟨(hS i I hI).1,(hS i I hI).2.2⟩)
    (fun i I hI => ⟨(hT i I hI).1,(hT i I hI).2.2⟩)
    (fun v => reflectedDyadicCoefficient P hg j e (η v) (ramifiedScale ρ q v.1))
    (fun i n hn v hv => reflectedDyadicCoefficient_norm P hg j e (η i)
      (ramifiedScale ρ q i.1) _ _ (ramifiedScale_pos ρ q hρ (by linarith) _) (by positivity) (by positivity)
      n v (hS i n hn).1 (hT i v hv).1 (hη i n hn v hv) (hS i n hn).2.1 (hT i v hv).2.1)
    σ hσ

end CompletedGauss

end

end OAI
