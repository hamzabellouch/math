import OAI.NumberTheory.DirichletL.QuadraticSieve.ProductColumns

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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum

theorem product_quadratic_norm_all :
    ∀ε : ℝ, 0<ε → ∃C : ℝ, 0<C ∧ ∀K U B : ℝ,
      1≤K → 1≤U → 1≤B → ∀S T : Finset (Ideal O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,I≠0 ∧ (Ideal.absNorm I:ℝ)≤B) →
      ∀β : Ideal O → Ideal O → ℂ, (∀n∈S,∀b∈T,‖β n b‖≤1) →
      (∑k : idealRange K,‖∑n∈S,∑b∈T,quadraticRow k.val (primaryGenerator (n*b))*β n b‖^2)≤
        C*(K*(U*B))^ε*(K+U*B)*(U*B) := by
  intro ε hε
  have hh : 0<ε/2 := by positivity
  have hq : 0<ε/4 := by positivity
  obtain ⟨C,hC,hbound⟩ := bounded_nonzero_quadratic_norm (ε/2) hh
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε/4) hq
  refine ⟨C*D^2,by positivity,?_⟩
  intro K U B hK hU hB S T hS hT β hβ
  let X := U*B
  let P := (S×ˢT).image (fun p => p.1*p.2)
  have hX : 1≤X := by dsimp [X]; nlinarith
  have hX0 : 0<X := by linarith
  have hK0 : 0<K := by linarith
  have hp (I : Ideal O) (hI : I∈P) : I≠0 ∧ (Ideal.absNorm I:ℝ)≤X := by
    obtain ⟨⟨n,b⟩,hnb,rfl⟩ := Finset.mem_image.mp hI
    have hm := Finset.mem_product.mp hnb
    refine ⟨mul_ne_zero (hS n hm.1).1 (hT b hm.2).1,?_⟩
    rw [map_mul,Nat.cast_mul]
    exact mul_le_mul (hS n hm.1).2 (hT b hm.2).2 (Nat.cast_nonneg _) (by linarith)
  have hcoeff (I : Ideal O) (hI : I∈P) : ‖productColumnCoefficient S T β I‖≤D*X^(ε/4) := by
    apply (productColumnCoefficient_norm S T β hβ I (hp I hI).1).trans
    apply (hdiv I (hp I hI).1).trans
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (hp I hI).2 hq.le) hD.le
  have hb := hbound K X (D*X^(ε/4)) hK hX (by positivity) P hp (productColumnCoefficient S T β) hcoeff
  simp_rw [productColumnCoefficient_row_sum]
  apply hb.trans
  have hpow : (K*X)^(ε/2)*(X^(ε/4))^2≤(K*X)^ε := by
    have hXP : X≤K*X := by nlinarith
    calc
      _ ≤ (K*X)^(ε/2)*((K*X)^(ε/4))^2 := by gcongr
      _ = _ := by
        rw [pow_two,←mul_assoc,←Real.rpow_add (by positivity : 0<K*X),←Real.rpow_add (by positivity : 0<K*X)]
        congr 1
        ring
  calc
    _ = (C*D^2)*((K*X)^(ε/2)*(X^(ε/4))^2)*(K+X)*X := by ring
    _ ≤ _ := by change _≤(C*D^2)*(K*X)^ε*(K+X)*X; gcongr

end CanonicalQuadraticSieve

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open JointLogSeparation (frequencyTwist frequencyTwist_apply)

theorem full_uniform_secondPairRadialMode_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2),
    ∀ (S T : Finset ι) (e : O), e ≠ 0 → ∀ (W : 𝓢(ℝ, ℂ)) (Y H : ℝ),
      0 < Y → 0 ≤ H →
      let n := ∏ i : activeSupport T S, p i.val
      let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
      (∑' k : {k : O // H ≤ scale * ‖eisEmbedding k‖^2},
        ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖) ≤
      (Y / ‖eisEmbedding n‖) *
        ((C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 scale)^2 * (1+H)^A)) := by
  obtain ⟨s,C,hC,hbound⟩ := EisensteinSchwartzPoisson.paperRadialFourier_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hg hinj hc
    S T e he W Y H hY hH
  dsimp only
  let n := ∏ i : activeSupport T S, p i.val
  let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
  have hn : n ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i hi => hp i.val)
  have hnorm : 0 < ‖eisEmbedding n‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero hn)
  have hscale : 0 < scale := div_pos hY
    (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero he))) (sq_pos_of_pos hnorm))
  let tailSet : Set O := {k | H ≤ scale * ‖eisEmbedding k‖^2}
  let c := Y / ‖eisEmbedding n‖
  have hc0 : 0 ≤ c := (div_pos hY hnorm).le
  have hpnt (k : tailSet) : ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖ ≤
      c * ‖EisensteinSchwartzPoisson.paperRadialFourier W (scale * ‖eisEmbedding k.val‖^2)‖ := by
    have ha : Y * ‖eisEmbedding k.val‖^2 / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2) =
        scale * ‖eisEmbedding k.val‖^2 := by dsimp [scale]; ring
    simp only [secondPairRadialMode, norm_mul]
    change ‖(Y : ℂ) / (‖eisEmbedding n‖ : ℂ)‖ * _ * _ ≤ _
    rw [ha, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hY, abs_of_pos hnorm]
    exact mul_le_of_le_one_right (by positivity)
      (activeGaussRowFactor_norm_le_one p hp hg hinj hc T S e k.val)
  have hmajor : Summable (fun k : tailSet =>
      c * ‖EisensteinSchwartzPoisson.paperRadialFourier W (scale * ‖eisEmbedding k.val‖^2)‖) :=
    ((EisensteinSchwartzPoisson.paperRadialFourier_lattice_summable_norm W scale hscale).subtype tailSet).mul_left c
  have hsmall : Summable (fun k : tailSet => ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpnt hmajor
  calc
    _ ≤ ∑' k : tailSet, c * ‖EisensteinSchwartzPoisson.paperRadialFourier W
          (scale * ‖eisEmbedding k.val‖^2)‖ := hsmall.tsum_le_tsum hpnt hmajor
    _ = c * ∑' k : tailSet, ‖EisensteinSchwartzPoisson.paperRadialFourier W
          (scale * ‖eisEmbedding k.val‖^2)‖ := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (hbound W scale H hscale hH) hc0

theorem full_uniform_secondPairRadialMode_remainder (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2),
    ∀ (S T : Finset ι) (e : O), e ≠ 0 → ∀ (W : 𝓢(ℝ, ℂ)) (Y H : ℝ),
      0 < Y → 0 ≤ H → ∀ K : Finset O,
      let n := ∏ i : activeSupport T S, p i.val
      let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
      (∀ k : O, k ∉ K → H ≤ scale * ‖eisEmbedding k‖^2) →
      ‖∑' k : {k : O // k ∉ K}, secondPairRadialMode p hp hg hinj S T e k.val W Y‖ ≤
        (Y/‖eisEmbedding n‖) *
          ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 scale)^2*(1+H)^A)) := by
  obtain ⟨s,C,hC,hb⟩ := full_uniform_secondPairRadialMode_tail A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hg hinj hc
  have hb := hb p hp hg hinj hc
  intro S T e he W Y H hY hH K
  dsimp only
  intro hK
  let n := ∏ i : activeSupport T S, p i.val
  let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
  let small : Set O := {k | k ∉ K}
  let large : Set O := {k | H ≤ scale * ‖eisEmbedding k‖^2}
  let f : small → large := fun k => ⟨k.val,hK k.val k.property⟩
  have hi : Function.Injective f := by
    intro a b heq
    exact Subtype.ext (congrArg (fun z : large => z.val) heq)
  have hs := secondPairRadialMode_summable_norm p hp hg hinj hc S T e he W Y hY
  calc
    _ ≤ ∑' k : small, ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖ :=
      norm_tsum_le_tsum_norm (hs.subtype small)
    _ ≤ ∑' k : large, ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖ :=
      (hs.subtype small).tsum_le_tsum_of_inj f hi (fun _ _ => norm_nonneg _) (fun _ => le_rfl)
        (hs.subtype large)
    _ ≤ _ := hb S T e he W Y H hY hH

theorem full_uniform_residualSecondMode_tail_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2),
    ∀ (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O) (H₁ H₂ : Finset ι → ℂ)
      (e : O), e ≠ 0 → ∀ (W : 𝓢(ℝ, ℂ)) (Y H : ℝ), 0 < Y → 0 ≤ H → ∀ K : Finset O,
      (∀ S ∈ (F\G).powerset, ∀ T ∈ (F\G).powerset, Disjoint S T →
        residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T ≠ 0 →
        ∀ k : O, k ∉ K →
          H ≤ (Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) *
            ‖eisEmbedding k‖^2) →
      ‖∑' k : {k : O // k ∉ K}, residualSecondMode p hp hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂ e k.val W Y‖ ≤
      residualTailCost p hg F G Ψ₁ Ψ₂ m c d H₁ H₂ e Y H A (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by
  obtain ⟨s,C,hC,hb⟩ := full_uniform_secondPairRadialMode_remainder A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hg hinj hc
  have hb := hb p hp hg hinj hc
  intro F G Ψ₁ Ψ₂ m c d H₁ H₂ e he W Y H hY hH K hK
  rw [residualSecondMode_tail_eq p hp hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂ e he W Y hY K]
  unfold residualTailCost
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro S hS
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro T hT
  by_cases hd : Disjoint S T
  · simp only [ite_eq_left hd, norm_mul]
    by_cases hw : residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T = 0
    · simp only [hw, norm_zero, zero_mul, le_refl]
    · exact mul_le_mul_of_nonneg_left (hb S T e he W Y H hY hH K (hK S hS T hT hd hw)) (norm_nonneg _)
  · simp [hd]

theorem full_uniform_secondSourceTail_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2),
    ∀ (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (Hcol : Finset ι → ℂ)
      (W : 𝓢(ℝ, ℂ)) (Y H : ℝ), 0 < Y → 0 ≤ H →
      ∀ K : Finset ι → Finset ι → Finset O,
      (∀ G ∈ F.powerset, ∀ E : G.powerset,
        ∀ S ∈ (F\G).powerset, ∀ T ∈ (F\G).powerset, Disjoint S T →
        residualPairWeight p hg Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U)) S T ≠ 0 →
        ∀ k : O, k ∉ K G E.val →
          H ≤ (Y / (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖^2 *
            ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) * ‖eisEmbedding k‖^2) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y K‖ ≤
      ∑ G ∈ F.powerset, ∑ E : G.powerset, ‖secondSourceCommonCoefficient p hg Ψ m c d G E.val‖ *
        residualTailCost p hg F G Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U))
          (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) Y H A
          (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by
  obtain ⟨s,C,hC,hb⟩ := full_uniform_residualSecondMode_tail_bound A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hg hinj hc
  have hb := hb p hp hg hinj hc
  intro F Ψ m c d Hcol W Y H hY hH K hK
  unfold secondSourceTail
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro G hG
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro E hE
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simp_rw [← residualSecondMode_eq_frequencyKernel p hp hg hinj F G E.val
    (Finset.mem_powerset.mp E.property) Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U))]
  exact hb F G Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U))
    (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) (primeSubsetGenerator_ne_zero _ _)
    W Y H hY hH (K G E.val) (hK G hG E)

theorem full_uniform_firstCoreSecondCutoff_tail_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2),
    ∀ (F D : Finset ι) (Ψ : O →* ℂ) (m c d : O) (g V W : 𝓢(ℝ, ℂ))
      (negative : Bool) (t X Y M H : ℝ),
      0 < X → 0 < Y → 0 ≤ H → (∀ u, g u ≠ 0 → |u| ≤ M) →
      let X' := X / primeProductNorm p D
      let Hbase := normalizedColumn p (fun S => firstCoreBaseProfile g V negative (columnLog p X' S))
      let Hmode := normalizedColumn p (fun S => firstCoreModeProfile g V negative t (columnLog p X' S))
      ‖secondSourceTail p hp hg hinj (F\D) Ψ m c d Hmode W Y (firstCoreSecondCutoff p D X Y M H)‖ ≤
      ∑ G ∈ (F\D).powerset, ∑ E : G.powerset,
        ‖secondSourceCommonCoefficient p hg Ψ m c d G E.val‖ *
        residualTailCost p hg (F\D) G Ψ Ψ m c d (fun S => Hbase (G∪S)) (fun S => Hbase (G∪S))
          (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) Y H A
          (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by
  obtain ⟨s,C,hC,hb⟩ := full_uniform_secondSourceTail_bound A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hg hinj hc
  have hb := hb p hp hg hinj hc
  intro F D Ψ m c d g V W negative t X Y M H hX hY hH hgM
  dsimp only
  have hcut : ∀ G ∈ (F\D).powerset, ∀ E : G.powerset,
      ∀ S ∈ ((F\D)\G).powerset, ∀ T ∈ ((F\D)\G).powerset, Disjoint S T →
      residualPairWeight p hg Ψ Ψ m c d
        (fun U => normalizedColumn p (fun R => firstCoreModeProfile g V negative t
          (columnLog p (X / primeProductNorm p D) R)) (G∪U))
        (fun U => normalizedColumn p (fun R => firstCoreModeProfile g V negative t
          (columnLog p (X / primeProductNorm p D) R)) (G∪U)) S T ≠ 0 →
      ∀ k : O, k ∉ firstCoreSecondCutoff p D X Y M H G E.val →
        H ≤ (Y / (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖^2 *
          ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) * ‖eisEmbedding k‖^2 := by
    intro G hG E S hS T hT hST hw k hk
    have hGS : Disjoint G S := Finset.disjoint_of_subset_right
      (Finset.mem_powerset.mp hS) disjoint_sdiff_self_right
    have hGT : Disjoint G T := Finset.disjoint_of_subset_right
      (Finset.mem_powerset.mp hT) disjoint_sdiff_self_right
    obtain ⟨hs,ht⟩ := residualPairWeight_test_ne_zero p hg Ψ Ψ m c d _ _ S T hw
    exact firstCoreSecondCutoff_uniform p hp g V negative t M hgM D G E.val S T hGS hGT hST
      X Y H hX hY hs ht k hk
  have h := hb (F\D) Ψ m c d
    (normalizedColumn p (fun S => firstCoreModeProfile g V negative t
      (columnLog p (X / primeProductNorm p D) S))) W Y H hY hH
    (firstCoreSecondCutoff p D X Y M H) hcut
  simpa only [firstCoreModeProfile, residualTailCost_frequencyTwist] using h

theorem full_uniform_firstCoreSecondCutoff_tail_polynomial (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2),
    ∀ (F D : Finset ι) (Ψ : O →* ℂ) (m c d : O) (g V W : 𝓢(ℝ, ℂ))
      (negative : Bool) (t X Y M H : ℝ),
      (∀ a, ‖Ψ a‖ ≤ 1) → 0 < X → 0 < Y → 0 ≤ H → (∀ u, g u ≠ 0 → |u| ≤ M) →
      let X' := X / primeProductNorm p D
      let lengthScale := 1 + X' * Real.exp M
      let Hmode := normalizedColumn p (fun S => firstCoreModeProfile g V negative t (columnLog p X' S))
      ‖secondSourceTail p hp hg hinj (F\D) Ψ m c d Hmode W Y (firstCoreSecondCutoff p D X Y M H)‖ ≤
        (128*lengthScale)^4 * ((SchwartzMap.seminorm ℝ 0 0 (firstCoreBaseProfile g V negative))^2 *
          (Y*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*(1+lengthScale^3/Y)^2/(1+H)^A)) := by
  obtain ⟨s,C,hC,hb⟩ := full_uniform_firstCoreSecondCutoff_tail_bound A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hg hinj hc
  have hb := hb p hp hg hinj hc
  intro F D Ψ m c d g V W negative t X Y M H hΨ hX hY hH hgM
  dsimp only
  have hX' : 0 < X / primeProductNorm p D :=
    div_pos hX (FirstPassCubeLabels.primeProductNorm_pos p hp D)
  have hgbase : ∀ u, firstCoreBaseProfile g V negative u ≠ 0 → |u| ≤ M := by
    intro u hu
    apply hgM u
    intro hz
    apply hu
    simp only [firstCoreBaseProfile_apply, hz, zero_mul]
  have hP : 0 ≤ C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := mul_nonneg hC.le (apply_nonneg _ _)
  exact (hb F D Ψ m c d g V W negative t X Y M H hX hY hH hgM).trans
    (secondSourceTailCost_polynomial p hp hg hinj (F\D) Ψ hΨ m c d
      (firstCoreBaseProfile g V negative) M (X / primeProductNorm p D) Y H
      (1 + X / primeProductNorm p D * Real.exp M) (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) A
      hX' hY hH hP (by linarith [mul_pos hX' (Real.exp_pos M)]) (by linarith) hgbase)

theorem full_uniform_firstCoreSecondCutoff_tail_fixed_source (A : ℕ) (g V W : 𝓢(ℝ, ℂ)) (negative : Bool) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2),
    ∀ (F D : Finset ι) (Ψ : O →* ℂ) (m c d : O) (t X Y M H : ℝ),
      (∀ a, ‖Ψ a‖ ≤ 1) → 0 < X → 0 < Y → 0 ≤ H → (∀ u, g u ≠ 0 → |u| ≤ M) →
      let X' := X / primeProductNorm p D
      let lengthScale := 1 + X' * Real.exp M
      let Hmode := normalizedColumn p (fun S => firstCoreModeProfile g V negative t (columnLog p X' S))
      ‖secondSourceTail p hp hg hinj (F\D) Ψ m c d Hmode W Y (firstCoreSecondCutoff p D X Y M H)‖ ≤
        C*lengthScale^4*Y*(1+lengthScale^3/Y)^2/(1+H)^A := by
  obtain ⟨s,C,hC,hb⟩ := full_uniform_firstCoreSecondCutoff_tail_polynomial A
  let C₀ := 128^4 * (SchwartzMap.seminorm ℝ 0 0 (firstCoreBaseProfile g V negative))^2 *
    (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  refine ⟨1+C₀, by linarith, ?_⟩
  intro ι _ p hp _ hg hinj hc
  have hb := hb p hp hg hinj hc
  intro F D Ψ m c d t X Y M H hΨ hX hY hH hgM
  dsimp only
  have h := hb F D Ψ m c d g V W negative t X Y M H hΨ hX hY hH hgM
  apply h.trans
  calc
    _ = C₀*(1+X/primeProductNorm p D*Real.exp M)^4*Y*
        (1+(1+X/primeProductNorm p D*Real.exp M)^3/Y)^2/(1+H)^A := by dsimp [C₀]; ring
    _ ≤ _ := by gcongr; linarith

end SecondPassArithmetic

open scoped BigOperators Classical
namespace InitialMeanSquare
open IdealMobiusDivisorSum

structure ElementDatum where
  divisor : Ideal O
  shared : O
  frequency : O
  deriving DecidableEq

def elementRow (gen : Ideal O→O) (x : ElementDatum) : O := gen x.divisor*x.frequency
def elementLabel (gen : Ideal O→O) (x : ElementDatum) : O := gen x.divisor*x.shared
def elementObservation (gen : Ideal O→O) (x : ElementDatum) : O×O := (elementRow gen x,elementLabel gen x)

theorem element_divisor_injective_on_fiber (gen : Ideal O→O) (y f : O) (hy : y≠0) :
    Set.InjOn ElementDatum.divisor {x : ElementDatum | elementObservation gen x=(y,f)} := by
  intro x hx z hz hd
  have hxrow : elementRow gen x=y := congrArg Prod.fst hx
  have hzrow : elementRow gen z=y := congrArg Prod.fst hz
  have hxlabel : elementLabel gen x=f := congrArg Prod.snd hx
  have hzlabel : elementLabel gen z=f := congrArg Prod.snd hz
  have hgen : gen x.divisor≠0 := by
    intro he
    apply hy
    rw [←hxrow,elementRow,he,zero_mul]
  have hs : x.shared=z.shared := by
    apply mul_left_cancel₀ hgen
    calc
      gen x.divisor*x.shared = f := hxlabel
      _ = gen z.divisor*z.shared := hzlabel.symm
      _ = gen x.divisor*z.shared := by rw [hd]
  have hh : x.frequency=z.frequency := by
    apply mul_left_cancel₀ hgen
    calc
      gen x.divisor*x.frequency = y := hxrow
      _ = gen z.divisor*z.frequency := hzrow.symm
      _ = gen x.divisor*z.frequency := by rw [hd]
  cases x
  cases z
  simp_all

theorem element_fiber_card_le (gen : Ideal O→O) (hgen : ∀D,Ideal.span {gen D}=D)
    (s : Finset ElementDatum) (y f : O) (hy : y≠0) :
    (s.filter (fun x => elementObservation gen x=(y,f))).card≤(idealDivisors (Ideal.span {y})).card := by
  have hyI : (Ideal.span {y}:Ideal O)≠0 := by intro hz; exact hy (Ideal.span_singleton_eq_bot.mp hz)
  apply Finset.card_le_card_of_injOn ElementDatum.divisor
  · intro x hx
    change x.divisor∈idealDivisors (Ideal.span {y})
    rw [mem_idealDivisors hyI]
    have he : elementRow gen x=y := congrArg Prod.fst (Finset.mem_filter.mp hx).2
    rw [←he,elementRow,←Ideal.span_singleton_mul_span_singleton,hgen]
    exact dvd_mul_right _ _
  · intro x hx z hz he
    exact element_divisor_injective_on_fiber gen y f hy (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hz).2 he

theorem element_weighted_energy_pushforward (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (gen : Ideal O→O), (∀D,Ideal.span {gen D}=D) →
      ∀ (s : Finset ElementDatum) (t : Finset (O×O)) (w : ElementDatum→ℂ)
        (P : O×O→ℂ) (A K : ℝ),
      0≤A → 0≤K → (∀x∈s,elementObservation gen x∈t) →
      (∀y∈t,y.1≠0) → (∀y∈t,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K) →
      (∀x∈s,‖w x‖≤A) →
      (∑x∈s,‖w x‖*‖P (elementObservation gen x)‖^2)≤A*C*K^ε*∑y∈t,‖P y‖^2 := by
  obtain ⟨C,hC,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro gen hgen s t w P A K hA hK hmap ht hnorm hw
  apply (DescentWeightedCauchy.bounded_energy_pushforward s t (elementObservation gen) w P A hmap hw).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  have hyI : (Ideal.span {y.1}:Ideal O)≠0 := by intro hz; exact ht y hy (Ideal.span_singleton_eq_bot.mp hz)
  have hcard : ((s.filter (fun x => elementObservation gen x=y)).card:ℝ)≤C*K^ε := by
    calc
      _ ≤ ((idealDivisors (Ideal.span {y.1})).card:ℝ) := by
        exact_mod_cast element_fiber_card_le gen hgen s y.1 y.2 (ht y hy)
      _ ≤ C*(Ideal.absNorm (Ideal.span {y.1}):ℝ)^ε := hdiv _ hyI
      _ ≤ C*K^ε := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm y hy) hε.le) hC.le
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hA) (sq_nonneg ‖P y‖)
  simpa only [mul_assoc] using hh

end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn)
open EisensteinSchwartzPoisson (paperRadialFourier)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalFirstDiagonalCost (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℂ) (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ))
    (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) : ℝ :=
  ∑ b∈s,‖w b‖*(primeProductNorm p b.firstCommon)⁻¹*
    (|Y b| *‖paperRadialFourier W 0‖*
      ∑ G∈(globalFirstRawPool pool b).powerset,
        ‖secondInputCoefficient p hg Ψ (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
          (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
          (globalFirstBlockTest p g ell side b) G‖^2)

include hp in
theorem globalFirstDiagonalCost_nonneg (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℂ) (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ))
    (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) :
    0≤globalFirstDiagonalCost p hg pool s w Ψ m g W ell side Y := by
  unfold globalFirstDiagonalCost
  apply Finset.sum_nonneg
  intro b hb
  have hn := (FirstPassCubeLabels.primeProductNorm_pos p hp b.firstCommon).le
  positivity

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalFirstBlockTest_mode_norm (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool)
    (t : ℝ) (b : GlobalFirstData ι) (G : Finset ι) :
    ‖globalFirstBlockTest p (firstCoreModeProfile g V side t) ell side b G‖ =
      ‖globalFirstBlockTest p (firstCoreBaseProfile g V side) ell side b G‖ := by
  simp only [globalFirstBlockTest,normalizedColumn,norm_div,firstCoreModeProfile,
    JointLogSeparation.frequencyTwist_norm]

include hp in

theorem globalFirstSourceZero_bound
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (Ψ : O →* ℂ) (m : O) (g V W : 𝓢(ℝ,ℂ)) (K ell B F M H : ℝ) (side : Bool) (t : ℝ) :
    ‖globalFirstSourceZero p hg pool s w (globalFirstConcreteCutoff p K ell B F M H side)
      Ψ m (firstCoreModeProfile g V side t) W ell side (globalFirstPooledRow p K ell B F side)‖ ≤
    globalFirstDiagonalCost p hg pool s w Ψ m (firstCoreBaseProfile g V side) W ell side
      (globalFirstPooledRow p K ell B F side) := by
  unfold globalFirstSourceZero globalFirstDiagonalCost
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b hb
  rw [norm_mul,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg (FirstPassCubeLabels.primeProductNorm_pos p hp _).le]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _)
    (inv_nonneg.mpr (FirstPassCubeLabels.primeProductNorm_pos p hp _).le))
  have hh := truncatedSecondZero_norm_le p hg hinj (globalFirstRawPool pool b) Ψ
    (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
    (globalFirstBlockTest p (firstCoreModeProfile g V side t) ell side b)
    W (globalFirstPooledRow p K ell B F side b) (globalFirstConcreteCutoff p K ell B F M H side b)
    (fun G hG E hE => firstCoreSecondCutoff_zero _ _ _ _ _ _ _ _)
  apply hh.trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro G hG
  simp only [secondInputCoefficient,norm_mul,globalFirstBlockTest_mode_norm]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

def globalFirstTailCost (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (K ell B F M H : ℝ) (N : ℕ) (side : Bool) : ℝ :=
  ∑ b∈s,
    let lengthScale := 1+globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon*Real.exp M
    let Y := globalFirstPooledRow p K ell B F side b
    ‖w b‖*(primeProductNorm p b.firstCommon)⁻¹*lengthScale^4*Y*(1+lengthScale^3/Y)^2/(1+H)^N

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalFirstTailCost_nonneg (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (K ell B F M H : ℝ) (N : ℕ) (side : Bool)
    (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F) (hH : 0≤H) :
    0≤globalFirstTailCost p s w K ell B F M H N side := by
  unfold globalFirstTailCost
  apply Finset.sum_nonneg
  intro b hb
  dsimp only
  have hn := (FirstPassCubeLabels.primeProductNorm_pos p hp b.firstCommon).le
  have hY : 0<globalFirstPooledRow p K ell B F side b := globalPooledRowScale_pos K ell B F hK hell hB hF _
  positivity
end

theorem globalFirstSourceTail_bound (N : ℕ) (g V W : 𝓢(ℝ,ℂ)) (side : Bool) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
      (Ψ : O →* ℂ) (m : O) (K ell B F M H t : ℝ),
      (∀ a,‖Ψ a‖≤1) → 0<K → 0<ell → 0<B → 0<F → 0≤H → (∀ u,g u≠0 → |u|≤M) →
      ‖globalFirstSourceTail p hp hg hinj pool s w (globalFirstConcreteCutoff p K ell B F M H side)
        Ψ m (firstCoreModeProfile g V side t) W ell side (globalFirstPooledRow p K ell B F side)‖ ≤
      C*globalFirstTailCost p s w K ell B F M H N side := by
  obtain ⟨C,hC,hbound⟩ := full_uniform_firstCoreSecondCutoff_tail_fixed_source N g V W side
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hg hinj hc pool s w Ψ m K ell B F M H t hΨ hK hell hB hF hH hgM
  unfold globalFirstSourceTail globalFirstTailCost
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b hb
  dsimp only
  rw [norm_mul,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg (FirstPassCubeLabels.primeProductNorm_pos p hp _).le]
  have hX : 0<globalFirstBlockColumnScale p ell side b :=
    div_pos hell (mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp _) (FirstPassCubeLabels.primeProductNorm_pos p hp _))
  have hY : 0<globalFirstPooledRow p K ell B F side b := globalPooledRowScale_pos K ell B F hK hell hB hF _
  have hh := hbound p hp hg hinj hc (pool\(b.cube.support∪b.common)) b.firstCommon Ψ
    (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
    t (globalFirstBlockColumnScale p ell side b) (globalFirstPooledRow p K ell B F side b) M H
    hΨ hX hY hH hgM
  have hh' := mul_le_mul_of_nonneg_left hh (mul_nonneg (norm_nonneg (w b))
    (inv_nonneg.mpr (FirstPassCubeLabels.primeProductNorm_pos p hp b.firstCommon).le))
  apply hh'.trans_eq
  ring

end SecondPassArithmetic

end

end OAI
