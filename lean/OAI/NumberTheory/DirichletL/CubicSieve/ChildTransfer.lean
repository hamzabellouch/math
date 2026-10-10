import OAI.NumberTheory.DirichletL.Fourier.FrequencyTwists

namespace OAI

noncomputable section

namespace SecondPassArithmetic

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

open scoped BigOperators Classical

section
open ActualEisensteinCubic
open SecondPassFiber (OldTuple newLabel newRow Valid)
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def fixedSecondMode (s : Finset OldTuple) (w : OldTuple → ℂ) (label : OldTuple → O)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (H₁ H₂ : Finset ι → ℂ) : ℂ :=
  ∑ x ∈ s, w x *
    star (fixedChildRow p hp hcop hg F Ψ₁ m H₁ (label x) (newRow x)) *
      fixedChildRow p hp hcop hg F Ψ₂ m H₂ (label x) (-newRow x)

theorem fixed_second_mode_transfer (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset OldTuple) (t : Finset (Ideal O × O))
      (b0 : Ideal O) (w : OldTuple → ℂ) (B lengthScale : ℝ) (label : OldTuple → O)
      (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (H₁ H₂ : Finset ι → ℂ),
      b0 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
      (∀ x ∈ s, (newLabel x, newRow x) ∈ t) →
      (∀ z ∈ t, z.1 ≠ ⊥) →
      (∀ z ∈ t, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∀ x ∈ s, Ideal.span {label x} = newLabel x) →
      ‖fixedSecondMode p hp hcop hg s w label F Ψ₁ Ψ₂ m H₁ H₂‖ ≤
        (B * C * (lengthScale * Ideal.absNorm b0)^ε) *
        Real.sqrt (∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hp hcop hg F Ψ₁ m H₁ false u z‖ ^ 2) *
        Real.sqrt (∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hp hcop hg F Ψ₂ m H₂ true u z‖ ^ 2) := by
  obtain ⟨C, hC, hpush⟩ := labeled_child_second_energy_pushforward p hp hcop hg ε hε
  refine ⟨C, hC, ?_⟩
  intro s t b0 w B lengthScale label F Ψ₁ Ψ₂ m H₁ H₂ hb0 hB hL hv hm ht hn hw hl
  let P₁ := fun x => fixedChildRow p hp hcop hg F Ψ₁ m H₁ (label x) (newRow x)
  let P₂ := fun x => fixedChildRow p hp hcop hg F Ψ₂ m H₂ (label x) (-newRow x)
  have h₁ := hpush s t b0 w B lengthScale label F Ψ₁ m H₁ false hb0 hB hL hv hm ht hn hw hl
  have h₂ := hpush s t b0 w B lengthScale label F Ψ₂ m H₂ true hb0 hB hL hv hm ht hn hw hl
  simp only [Bool.false_eq_true, ite_false, ite_true] at h₁ h₂
  let D : ℝ := B * C * (lengthScale * Ideal.absNorm b0)^ε
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hCau := DescentWeightedCauchy.weighted_cauchy s w P₂ P₁
  have hmode : fixedSecondMode p hp hcop hg s w label F Ψ₁ Ψ₂ m H₁ H₂ =
      ∑ x ∈ s, w x * P₂ x * star (P₁ x) := by
    unfold fixedSecondMode
    apply Finset.sum_congr rfl
    intro x hx
    dsimp [P₁, P₂]
    ring
  rw [hmode]
  apply hCau.trans
  calc
    _ ≤ Real.sqrt (D * (∑ u : Oˣ, ∑ z ∈ t,
        ‖idealChildRow p hp hcop hg F Ψ₂ m H₂ true u z‖ ^ 2)) *
      Real.sqrt (D * (∑ u : Oˣ, ∑ z ∈ t,
        ‖idealChildRow p hp hcop hg F Ψ₁ m H₁ false u z‖ ^ 2)) := by
      gcongr
    _ = _ := by
      rw [Real.sqrt_mul hD, Real.sqrt_mul hD]
      calc
        _ = (Real.sqrt D)^2 *
          Real.sqrt (∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hp hcop hg F Ψ₁ m H₁ false u z‖ ^ 2) *
          Real.sqrt (∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hp hcop hg F Ψ₂ m H₂ true u z‖ ^ 2) := by ring
        _ = _ := by rw [Real.sq_sqrt hD]

end

section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius supportConjugateSum)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondInputCoefficient_union (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (G U : Finset ι) (hd : Disjoint G U) :
    secondInputCoefficient p hg Ψ m c d H (G ∪ U) =
      secondInputCoefficient p hg Ψ m c d (fun _ => 1) G *
        secondInputCoefficient p hg Ψ m c d (fun V => H (G ∪ V)) U := by
  simp only [secondInputCoefficient, Finset.prod_union hd, map_mul,
    FirstPassCubeLabels.mask_union _ hg G U hd,
    FirstPassCubeLabels.row_union _ hg G U hd, mul_pow, mul_one]
  ring

def inputConjugateRow (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (z : O) : ℂ :=
  supportConjugateSum (fun i => Ideal.span {p i}) hg F
    (secondInputCoefficient p hg Ψ m c d H) z

theorem supportMobius_disjoint_mul
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (G U : Finset ι) (hd : Disjoint G U) :
    supportMobius (fun i => Ideal.span {p i}) (G ∪ U) =
      supportMobius (fun i => Ideal.span {p i}) G * supportMobius (fun i => Ideal.span {p i}) U := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  simp only [supportMobius, prime_product_moebius _ hprime hinj,
    Finset.card_union_of_disjoint hd, pow_add]

theorem inputConjugateRow_sq_overlap
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ) (z : O) :
    (↑(‖inputConjugateRow p hg F Ψ m c d H z‖ ^ 2) : ℂ) =
      ∑ G ∈ F.powerset, ∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset,
        if Disjoint U V then
          (↑(‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2) : ℂ) *
          rowCoprimeMask (fun i => Ideal.span {p i}) G z *
          (star (supportMobius (fun i => Ideal.span {p i}) U *
            secondInputCoefficient p hg Ψ m c d (fun S => H (G ∪ S)) U) *
            (supportMobius (fun i => Ideal.span {p i}) V *
              secondInputCoefficient p hg Ψ m c d (fun S => H (G ∪ S)) V) *
            (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U z *
              star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V z))) else 0 := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have hnorm (a : ℂ) : (↑(‖a‖ ^ 2) : ℂ) = star a * a := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    rfl
  rw [hnorm]
  unfold inputConjugateRow supportConjugateSum
  rw [star_sum, Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [FiniteOverlapDecomposition.sum_pair_eq_overlap]
  apply Finset.sum_congr rfl
  intro G hG
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  by_cases hd : Disjoint U V
  · rw [ite_eq_left hd, ite_eq_left hd]
    have hGU : Disjoint G U := Finset.disjoint_left.mpr (fun i hi hu =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hU) hu)).2 hi)
    have hGV : Disjoint G V := Finset.disjoint_left.mpr (fun i hi hv =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hV) hv)).2 hi)
    rw [supportMobius_disjoint_mul p hinj G U hGU, supportMobius_disjoint_mul p hinj G V hGV,
      secondInputCoefficient_union p hg Ψ m c d H G U hGU,
      secondInputCoefficient_union p hg Ψ m c d H G V hGV,
      FirstPassCubeLabels.row_union _ hg G U hGU,
      FirstPassCubeLabels.row_union _ hg G V hGV]
    simp only [star_mul, star_star, FirstCauchyArithmetic.star_supportMobius]
    have hmu := FirstCauchyArithmetic.supportMobius_sq _ hprime hinj G
    have hrow := finiteSquarefreeRow_self_pair (fun i => Ideal.span {p i}) hg G z
    rw [hnorm]
    calc
      _ = (supportMobius (fun i => Ideal.span {p i}) G * supportMobius (fun i => Ideal.span {p i}) G) *
        (star (secondInputCoefficient p hg Ψ m c d (fun _ => 1) G) *
          secondInputCoefficient p hg Ψ m c d (fun _ => 1) G) *
        (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg G z) *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg G z) *
        (star (supportMobius (fun i => Ideal.span {p i}) U *
            secondInputCoefficient p hg Ψ m c d (fun S => H (G ∪ S)) U) *
          (supportMobius (fun i => Ideal.span {p i}) V *
            secondInputCoefficient p hg Ψ m c d (fun S => H (G ∪ S)) V) *
          (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U z *
            star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V z))) := by
          simp only [star_mul, FirstCauchyArithmetic.star_supportMobius]
          ring
      _ = _ := by
        rw [hmu, hrow]
        simp only [star_mul, FirstCauchyArithmetic.star_supportMobius]
        ring
  · simp [hd]

end

section
open ActualEisensteinCubic

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
include hg

theorem commonProduct_mask
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (U G : Finset ι) :
    rowCoprimeMask (fun i => Ideal.span {p i}) U (∏ i ∈ G, p i) =
      if Disjoint U G then 1 else 0 := by
  by_cases hd : Disjoint U G
  · rw [ite_eq_left hd, FirstPassCubeLabels.mask_prod _ hg U G p]
    apply Finset.prod_eq_one
    intro j hj
    have hh : ¬ ∃ i ∈ U, p j ∈ Ideal.span {p i} := by
      rintro ⟨i, hi, hpi⟩
      have hij : i ≠ j := fun he => Finset.disjoint_left.mp hd hi (he ▸ hj)
      exact (prime_generator_not_mem_of_ne (Ideal.span {p i}) (Ideal.span {p j})
        (fun he => hij (hinj he)) (p j) rfl) hpi
    simp [rowCoprimeMask, hh]
  · rw [ite_eq_right hd]
    obtain ⟨i, hiU, hiG⟩ := Finset.not_disjoint_iff.mp hd
    have hh : ∃ j ∈ U, (∏ i ∈ G, p i) ∈ Ideal.span {p j} :=
      ⟨i, hiU, Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem p hiG)⟩
    simp [rowCoprimeMask, hh]

theorem sum_remove_common_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F G : Finset ι) (A : Finset ι → ℂ) :
    (∑ U ∈ (F \ G).powerset, A U) =
      ∑ U ∈ F.powerset, rowCoprimeMask (fun i => Ideal.span {p i}) U (∏ i ∈ G, p i) * A U := by
  have hsub : (F \ G).powerset ⊆ F.powerset := Finset.powerset_mono.mpr Finset.sdiff_subset
  calc
    _ = ∑ U ∈ (F \ G).powerset,
        rowCoprimeMask (fun i => Ideal.span {p i}) U (∏ i ∈ G, p i) * A U := by
      apply Finset.sum_congr rfl
      intro U hU
      have hd : Disjoint U G := Finset.disjoint_left.mpr (fun i hi hG =>
        (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hU) hi)).2 hG)
      rw [commonProduct_mask p hg hinj U G, ite_eq_left hd, one_mul]
    _ = _ := by
      apply Finset.sum_subset hsub
      intro U hUF hUG
      have hd : ¬ Disjoint U G := by
        intro hd
        apply hUG
        apply Finset.mem_powerset.mpr
        intro i hi
        exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp hUF) hi,
          fun hG => Finset.disjoint_left.mp hd hi hG⟩
      rw [commonProduct_mask p hg hinj U G, ite_eq_right hd, zero_mul]

omit [DecidableEq ι] in
theorem secondInputCoefficient_fixed_mask (Ψ : O →* ℂ) (m g c d : O)
    (H : Finset ι → ℂ) (U : Finset ι) :
    secondInputCoefficient p hg Ψ (m*g) c d H U =
      rowCoprimeMask (fun i => Ideal.span {p i}) U g * secondInputCoefficient p hg Ψ m c d H U := by
  rw [secondInputCoefficient, FirstPassCubeLabels.mask_mul _ hg U m g]
  unfold secondInputCoefficient
  ring

theorem inputConjugateRow_fixed_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F G : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ) (z : O) :
    inputConjugateRow p hg (F \ G) Ψ m c d H z =
      inputConjugateRow p hg F Ψ (m * ∏ i ∈ G, p i) c d H z := by
  unfold inputConjugateRow FirstCauchyArithmetic.supportConjugateSum
  rw [sum_remove_common_pool p hg hinj F G]
  apply Finset.sum_congr rfl
  intro U hU
  rw [secondInputCoefficient_fixed_mask]
  ring

end

section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
include hg

theorem sum_pair_remove_common_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F G : Finset ι) (A : Finset ι → Finset ι → ℂ) :
    (∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset, A U V) =
      ∑ U ∈ F.powerset, ∑ V ∈ F.powerset,
        rowCoprimeMask (fun i => Ideal.span {p i}) U (∏ i ∈ G, p i) *
        rowCoprimeMask (fun i => Ideal.span {p i}) V (∏ i ∈ G, p i) * A U V := by
  rw [sum_remove_common_pool p hg hinj F G]
  apply Finset.sum_congr rfl
  intro U hU
  rw [sum_remove_common_pool p hg hinj F G, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro V hV
  ring

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] hg in
lemma star_mask (P : ι → Ideal O) (S : Finset ι) (a : O) :
    star (rowCoprimeMask P S a) = rowCoprimeMask P S a := by
  unfold rowCoprimeMask
  split_ifs <;> simp

theorem input_pair_fixed_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O)
    (H₁ H₂ : Finset ι → ℂ) (K : Finset ι → Finset ι → ℂ) :
    (∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset,
      if Disjoint U V then
        star (supportMobius (fun i => Ideal.span {p i}) U * secondInputCoefficient p hg Ψ₁ m c d H₁ U) *
        (supportMobius (fun i => Ideal.span {p i}) V * secondInputCoefficient p hg Ψ₂ m c d H₂ V) * K U V
      else 0) =
    ∑ U ∈ F.powerset, ∑ V ∈ F.powerset,
      if Disjoint U V then
        star (supportMobius (fun i => Ideal.span {p i}) U *
          secondInputCoefficient p hg Ψ₁ (m * ∏ i ∈ G, p i) c d H₁ U) *
        (supportMobius (fun i => Ideal.span {p i}) V *
          secondInputCoefficient p hg Ψ₂ (m * ∏ i ∈ G, p i) c d H₂ V) * K U V
      else 0 := by
  rw [sum_pair_remove_common_pool p hg hinj F G]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  by_cases hd : Disjoint U V
  · rw [ite_eq_left hd, ite_eq_left hd, secondInputCoefficient_fixed_mask,
      secondInputCoefficient_fixed_mask]
    simp only [star_mul, star_mask]
    ring
  · simp [hd]

omit hg in

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem poisson_mask_generator_dvd (E G : Finset ι) (hEG : E ⊆ G) :
    primeSubsetGenerator (fun i => Ideal.span {p i}) E ∣ ∏ i ∈ G, p i := by
  have hs : Ideal.span {primeSubsetGenerator (fun i => Ideal.span {p i}) E} =
      Ideal.span {∏ i ∈ E, p i} := by
    rw [primeSubsetGenerator, ConcretePrimeRowBridge.span_idealGenerator,
      FiniteGaussPhase.span_finset_prod]
  have ha := Ideal.span_singleton_eq_span_singleton.mp hs
  exact (dvd_dvd_iff_associated.mpr ha).1.trans (Finset.prod_dvd_prod_of_subset E G p hEG)

omit hg in
def secondMaskQuotient (E G : Finset ι) (hEG : E ⊆ G) : O :=
  Classical.choose (poisson_mask_generator_dvd p E G hEG)

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] hg in
theorem secondMaskQuotient_spec (E G : Finset ι) (hEG : E ⊆ G) :
    (∏ i ∈ G, p i) = primeSubsetGenerator (fun i => Ideal.span {p i}) E *
      secondMaskQuotient p E G hEG :=
  Classical.choose_spec (poisson_mask_generator_dvd p E G hEG)

end

open ActualEisensteinCubic

theorem secondMaskQuotient_span {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (E G : Finset ι) (hEG : E ⊆ G) :
    Ideal.span {secondMaskQuotient p E G hEG} =
      ∏ i ∈ G \ E, Ideal.span {p i} := by
  have hE : (∏ i ∈ E, Ideal.span {p i}) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (Ideal.span {p i}))
  have he : Ideal.span {primeSubsetGenerator (fun i => Ideal.span {p i}) E} =
      ∏ i ∈ E, Ideal.span {p i} := by
    rw [primeSubsetGenerator, ConcretePrimeRowBridge.span_idealGenerator]
  apply mul_left_cancel₀ hE
  calc
    _ = Ideal.span {primeSubsetGenerator (fun i => Ideal.span {p i}) E *
        secondMaskQuotient p E G hEG} := by rw [← he, Ideal.span_singleton_mul_span_singleton]
    _ = Ideal.span {∏ i ∈ G, p i} := by rw [← secondMaskQuotient_spec]
    _ = ∏ i ∈ G, Ideal.span {p i} := FiniteGaussPhase.span_finset_prod G p
    _ = _ := by simpa only [mul_comm] using
      (Finset.prod_sdiff (f := fun i => Ideal.span {p i}) hEG).symm

theorem secondMaskQuotient_norm {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (E G : Finset ι) (hEG : E ⊆ G) :
    ‖ConcreteTraceCRT.eisEmbedding (secondMaskQuotient p E G hEG)‖ ^ 2 =
      (Ideal.absNorm (∏ i ∈ G \ E, Ideal.span {p i}) : ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span, secondMaskQuotient_span]

end

section

open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstCauchyArithmetic (supportMobius)
open EisensteinSchwartzPoisson (paperRadialFourier)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def maskedSecondSource (G U V : Finset ι) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ∑' z : O, rowCoprimeMask (fun i => Ideal.span {p i}) G z *
    (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V z) *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U z) * W (‖eisEmbedding z‖ ^ 2 / Y)

def overlapPairWeight (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ) (G U V : Finset ι) : ℂ :=
  (↑(‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2) : ℂ) *
    star (supportMobius (fun i => Ideal.span {p i}) U *
      secondInputCoefficient p hg Ψ m c d (fun S => H (G ∪ S)) U) *
    (supportMobius (fun i => Ideal.span {p i}) V *
      secondInputCoefficient p hg Ψ m c d (fun S => H (G ∪ S)) V)

omit [DecidableEq ι] in
theorem maskedSecondSource_summable (G U V : Finset ι) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun z : O => rowCoprimeMask (fun i => Ideal.span {p i}) G z *
      (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V z) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U z) * W (‖eisEmbedding z‖ ^ 2 / Y)) := by
  have h := finiteSquarefreeRow_pair_radial_summable (fun i => Ideal.span {p i}) hg V U W Y hY
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _ h.norm
  intro z
  have hm : ‖rowCoprimeMask (fun i => Ideal.span {p i}) G z‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> norm_num
  simpa only [norm_mul, one_mul, mul_assoc] using
    mul_le_mul_of_nonneg_right hm
      (norm_nonneg ((star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V z) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U z) * W (‖eisEmbedding z‖ ^ 2 / Y)))

theorem inputConjugateRow_smoothed_overlap
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖inputConjugateRow p hg F Ψ m c d H z‖ ^ 2) : ℂ)) =
      ∑ G ∈ F.powerset, ∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset,
        if Disjoint U V then overlapPairWeight p hg Ψ m c d H G U V *
          maskedSecondSource p hg G U V W Y else 0 := by
  let f := fun (G U V : Finset ι) (z : O) => if Disjoint U V then
    overlapPairWeight p hg Ψ m c d H G U V *
      (rowCoprimeMask (fun i => Ideal.span {p i}) G z *
        (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V z) *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U z) * W (‖eisEmbedding z‖ ^ 2 / Y))
    else 0
  have hf (G U V : Finset ι) : Summable (f G U V) := by
    by_cases hd : Disjoint U V
    · simpa only [f, ite_eq_left hd] using
        (maskedSecondSource_summable p hg G U V W Y hY).mul_left (overlapPairWeight p hg Ψ m c d H G U V)
    · simp only [f, ite_eq_right hd]
      exact summable_zero
  have he (z : O) : W (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖inputConjugateRow p hg F Ψ m c d H z‖ ^ 2) : ℂ) =
      ∑ G ∈ F.powerset, ∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset, f G U V z := by
    rw [inputConjugateRow_sq_overlap p hg hinj]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro G hG
    apply Finset.sum_congr rfl
    intro U hU
    apply Finset.sum_congr rfl
    intro V hV
    by_cases hd : Disjoint U V
    · simp only [f, ite_eq_left hd, overlapPairWeight]
      ring
    · simp [f, hd]
  rw [tsum_congr he]
  rw [Summable.tsum_finsetSum (fun G _ => summable_sum (fun U _ => summable_sum (fun V _ => hf G U V)))]
  apply Finset.sum_congr rfl
  intro G hG
  rw [Summable.tsum_finsetSum (fun U _ => summable_sum (fun V _ => hf G U V))]
  apply Finset.sum_congr rfl
  intro U hU
  rw [Summable.tsum_finsetSum (fun V _ => hf G U V)]
  apply Finset.sum_congr rfl
  intro V hV
  by_cases hd : Disjoint U V
  · simp only [f, ite_eq_left hd, maskedSecondSource]
    exact tsum_mul_left
  · simp [f, hd]

def maskedSecondDual (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (G U V : Finset ι) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  let n := ∏ i : activeSupport V U, p i.val
  ((Y : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
    ∑ E ∈ G.powerset,
      let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
        (‖eisEmbedding e‖ ^ 2 : ℝ)) *
        ∑' k : O, paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 /
          (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) *
          FirstCauchyArithmetic.activeGaussRowFactor p hp hinj hg V U e k

theorem inputConjugateRow_smoothed_second_poisson (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖inputConjugateRow p hg F Ψ m c d H z‖ ^ 2) : ℂ)) =
      ∑ G ∈ F.powerset, ∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset,
        if Disjoint U V then overlapPairWeight p hg Ψ m c d H G U V *
          maskedSecondDual p hg hp hinj G U V W Y else 0 := by
  rw [inputConjugateRow_smoothed_overlap p hg hinj F Ψ m c d H W Y hY]
  apply Finset.sum_congr rfl
  intro G hG
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  by_cases hd : Disjoint U V
  · rw [ite_eq_left hd, ite_eq_left hd]
    congr 1
    exact masked_pair_second_poisson p hp hinj hg hc G U V hd W Y hY
  · simp [hd]

end

open scoped BigOperators Classical
open ActualEisensteinCubic
open FirstPassCubeLabels (cubeCoreCoefficient cubeOddSupport coreRayCoefficient coreRayTwist
  coreRayCharacter dilatedCoreRow dilatedRayColumn afterDilationLabel b0Label jLabel)
open FirstCauchyArithmetic (supportMobius supportRay supportConjugateSum)
open RayFourExpansion (RayCharacter)
open FourierBridge (logPhase)

abbrev FirstCoreIndex := RayCharacter × (RayCharacter × RayCharacter)

def sideRayMonoid (negative : Bool) (χ : RayCharacter) : O →* ℂ :=
  if negative then conjugateRayMonoid χ else rayMonoid χ

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def multiplicativeCoreColumn (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) (S : Finset ι) : ℂ :=
  Ψ (∏ i ∈ S, p i) * rowCoprimeMask (fun i => Ideal.span {p i}) S m * H S

def firstCoreTest (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ)
    (negative : Bool) (t : ℝ) (D U : Finset ι) : ℂ :=
  H (D ∪ U) *
    (if negative then star (V (y (D ∪ U)) * logPhase t (-(y (D ∪ U))))
      else V (y (D ∪ U)) * logPhase t (-(y (D ∪ U))))

def firstCoreOuter (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (Ψ : O →* ℂ) (m : O) (D : Finset ι) (r : FirstCoreIndex) : ℂ :=
  coreRayCoefficient p (cubeOddSupport B v ε₁ ε₂) negative r.1 r.2.1 r.2.2 *
    (Ψ * coreRayTwist negative r.1 r.2.2) (∏ i ∈ D, p i) *
    rowCoprimeMask (fun i => Ideal.span {p i}) D m *
    (if negative then star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg D (-1)) else 1)

def firstCoreTwist (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ)
    (r : FirstCoreIndex) : O →* ℂ :=
  sideRayMonoid negative χ * (Ψ * coreRayTwist negative r.1 r.2.2)

theorem cubeCoreCoefficient_ray_family
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (t : ℝ) (S : Finset ι) :
    cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t S =
      ∑ r : FirstCoreIndex,
        coreRayCoefficient p (cubeOddSupport B v ε₁ ε₂) negative r.1 r.2.1 r.2.2 *
          supportRay p (coreRayCharacter negative r.1 r.2.2) S * C S *
          (if negative then star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-1)) else 1) *
          (if negative then star (V (y S) * logPhase t (-(y S))) else V (y S) * logPhase t (-(y S))) := by
  have hphase := FirstPassCubeLabels.core_phase_ray_expansion p hp hcop hg hc hpr
    (cubeOddSupport B v ε₁ ε₂) S negative
  have he : cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t S =
      ((if negative then star (FirstPassCubeLabels.fixedRayExpansion p (cubeOddSupport B v ε₁ ε₂) S)
          else FirstPassCubeLabels.fixedRayExpansion p (cubeOddSupport B v ε₁ ε₂) S) *
        MixedCrossSeparation.columnG p hp hcop hg S) * C S *
          (if negative then star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-1)) else 1) *
          (if negative then star (V (y S) * logPhase t (-(y S))) else V (y S) * logPhase t (-(y S))) := by
    cases negative <;> simp only [cubeCoreCoefficient, Bool.false_eq_true, ite_false, ite_true] <;> ring
  rw [he, hphase]
  simp only [Fintype.sum_prod_type, Finset.sum_mul]

theorem dilatedCoreRow_eq_input_family
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O) (t : ℝ) (z : O) :
    dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ
      (multiplicativeCoreColumn p Ψ m H) V y c d t z =
    ∑ r : FirstCoreIndex, firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r *
      inputConjugateRow p hg (F \ D) (firstCoreTwist negative χ Ψ r)
        (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
        (firstCoreTest H V y negative t D) (if negative then -z else z) := by
  unfold dilatedCoreRow dilatedRayColumn supportConjugateSum
  simp_rw [cubeCoreCoefficient_ray_family p hp hcop hg hc hpr]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [inputConjugateRow, supportConjugateSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  have hDU : Disjoint D U := Finset.disjoint_left.mpr (fun i hi hu =>
    (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hU) hu)).2 hi)
  have hz : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U (-z) =
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U (-1) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U z := by
    simpa only [neg_one_mul] using finiteSquarefreeRow_mul (fun i => Ideal.span {p i}) hg U (-1) z
  cases negative <;>
    simp only [multiplicativeCoreColumn, firstCoreOuter, firstCoreTwist, sideRayMonoid,
      firstCoreTest, secondInputCoefficient, afterDilationLabel, Bool.false_eq_true, ite_false, ite_true,
      Finset.prod_union hDU, map_mul, FirstPassCubeLabels.mask_union _ hg D U hDU,
      FirstPassCubeLabels.row_union _ hg D U hDU, FirstPassCubeLabels.mask_mul _ hg U,
      FirstPassCubeLabels.coreRayTwist_prod, MonoidHom.mul_apply, conjugateRayMonoid_apply, rayMonoid_apply,
      supportRay, coreRayCharacter, RayFourExpansion.rayCharacter_mul, hz, star_mul, mul_one] <;> ring

end SecondPassArithmetic

end

end OAI
