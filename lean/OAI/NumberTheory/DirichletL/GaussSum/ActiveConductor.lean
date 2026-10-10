import OAI.NumberTheory.DirichletL.PrimeRows.ActiveGaussFactorization
import OAI.NumberTheory.DirichletL.Poisson.RadialFourier

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

namespace ActualEisensteinCubic

section

 theorem activeSupport_nonempty_of_ne {α : Type*} [DecidableEq α]
    {S T : Finset α} (h : S ≠ T) : (activeSupport S T).Nonempty := by
  by_contra hn
  apply h
  have he : activeSupport S T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  ext i
  simp only [activeSupport, Finset.union_eq_empty, Finset.sdiff_eq_empty_iff_subset] at he
  exact ⟨fun hi => he.1 hi, fun hi => he.2 hi⟩

 theorem activeRow_zero_of_ne {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) {S T : Finset α} (h : S ≠ T) :
    finiteSexticRow (activePrimes P S T) (fun i => hgood i.val)
      (activeExponent S T) 0 = 0 := by
  let : Nonempty (activeSupport S T) := (activeSupport_nonempty_of_ne h).to_subtype
  exact finiteSexticRow_zero _ _ _

open ConcreteTraceCRT EisensteinSchwartzPoisson

 theorem finiteSexticRow_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) (a : O) :
    finiteSexticRow P hgood j a = 1 := by
  simp [finiteSexticRow]

 theorem finitePrimeModulus_norm_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (P : ι → Ideal O) : ‖eisEmbedding (finitePrimeModulus P)‖ = 1 := by
  have h := finitePrimeModulus_norm_sq P
  simp only [Finset.univ_eq_empty, Finset.prod_empty, map_one, Nat.cast_one] at h
  nlinarith [norm_nonneg (eisEmbedding (finitePrimeModulus P))]

 theorem canonicalGaussSum_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) :
    canonicalGaussSum P hcop hgood j = 1 := by
  let c := finitePrimeModulus P
  have hc : Ideal.span {c} = ⊤ := by
    simpa only [c, Finset.univ_eq_empty, Finset.prod_empty, Ideal.one_eq_top] using
      span_finitePrimeModulus P
  have hzero (r : O ⧸ Ideal.span {c}) : r = 0 := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (by rw [hc]; trivial)
  let : Subsingleton (O ⧸ Ideal.span {c}) := ⟨fun a b => (hzero a).trans (hzero b).symm⟩
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span (finitePrimeModulus_ne_zero P)
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  unfold canonicalGaussSum
  change (∑ r : O ⧸ Ideal.span {c}, _ ) = 1
  rw [Fintype.sum_subsingleton _ 0]
  simp [principalSexticRow, finiteSexticQuotientRow]

 theorem canonicalNormalizedGauss_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) :
    canonicalNormalizedGauss P hcop hgood j = 1 := by
  rw [canonicalNormalizedGauss, canonicalGaussSum_of_isEmpty,
    finitePrimeModulus_norm_of_isEmpty, Complex.ofReal_one, div_one]

noncomputable def squarefreePairPoissonZeroMode
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ :=
  let Q := activePrimes P S T
  let hQ := activePrimes_pairwise_isCoprime P hinj S T
  let row := finiteSexticRow Q (fun i => hgood i.val) (activeExponent S T)
  let c := finitePrimeModulus Q
  ((scale : ℂ) * canonicalNormalizedGauss Q hQ (fun i => hgood i.val)
      (activeExponent S T) / (‖eisEmbedding c‖ : ℂ)) *
    ∑ E ∈ (S ∩ T).powerset,
      let d := primeSubsetGenerator P E
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) * row d /
        (‖eisEmbedding d‖ ^ 2 : ℝ)) *
        (star (row 0) * paperRadialFourier W 0)

 theorem squarefreePairPoissonZeroMode_eq_zero_of_ne
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i)
    {S T : Finset ι} (hST : S ≠ T) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    squarefreePairPoissonZeroMode P hinj hgood S T W scale = 0 := by
  simp only [squarefreePairPoissonZeroMode, activeRow_zero_of_ne P hgood hST,
    star_zero, zero_mul, mul_zero, Finset.sum_const_zero]

 theorem squarefreePairPoissonZeroMode_diag
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    squarefreePairPoissonZeroMode P hinj hgood S S W scale =
      (scale : ℂ) * paperRadialFourier W 0 *
        ∑ E ∈ S.powerset, (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
          (Ideal.absNorm (∏ i ∈ E, P i) : ℂ) := by
  have hempty : activeSupport S S = ∅ := by simp [activeSupport]
  let : IsEmpty (activeSupport S S) := ⟨fun x => by simpa [hempty] using x.property⟩
  simp only [squarefreePairPoissonZeroMode, canonicalNormalizedGauss_of_isEmpty,
    finitePrimeModulus_norm_of_isEmpty, Complex.ofReal_one, mul_one, div_one,
    Finset.inter_self, finiteSexticRow_of_isEmpty, star_one, one_mul]
  rw [← Finset.sum_mul]
  have hn (E : Finset ι) : ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 =
      (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ))
      (ConcretePrimeRowBridge.span_idealGenerator _)
  simp_rw [hn, Complex.ofReal_natCast]
  ring

end

open EisensteinSchwartzPoisson

theorem primeSubset_moebius_norm_sum
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P) (S : Finset ι) :
    (∑ E ∈ S.powerset, (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
      (Ideal.absNorm (∏ i ∈ E, P i) : ℂ)) =
      ∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i)) := by
  rw [Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro E hE
  rw [prime_product_moebius P hprime hinj E]
  simp only [Finset.prod_const_one, mul_one,  map_prod, Nat.cast_prod,
    Finset.prod_inv_distrib, div_eq_mul_inv, one_mul]

theorem primeDensity_nonneg_le_one
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (S : Finset ι) :
    0 ≤ (∏ i ∈ S, (1 - (1 : ℝ) / Ideal.absNorm (P i))) ∧
      (∏ i ∈ S, (1 - (1 : ℝ) / Ideal.absNorm (P i))) ≤ 1 := by
  have hfactor (i : ι) : 0 ≤ 1 - (1 : ℝ) / Ideal.absNorm (P i) ∧
      1 - (1 : ℝ) / Ideal.absNorm (P i) ≤ 1 := by
    have hnorm : (1 : ℝ) ≤ Ideal.absNorm (P i) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (NeZero.ne (P i)))
    constructor
    · exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr hnorm)
    · have : 0 ≤ (1 : ℝ) / Ideal.absNorm (P i) := by positivity
      linarith
  exact ⟨Finset.prod_nonneg (fun i _ => (hfactor i).1),
    Finset.prod_le_one₀ (fun i _ => (hfactor i).1) (fun i _ => (hfactor i).2)⟩

theorem squarefreePairPoissonZeroMode_diag_product
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    squarefreePairPoissonZeroMode P hinj hgood S S W scale =
      (scale : ℂ) * paperRadialFourier W 0 *
        ∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i)) := by
  rw [squarefreePairPoissonZeroMode_diag, primeSubset_moebius_norm_sum P hprime hinj]

theorem norm_squarefreePairPoissonZeroMode_diag_le
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    ‖squarefreePairPoissonZeroMode P hinj hgood S S W scale‖ ≤
      |scale| * ‖paperRadialFourier W 0‖ := by
  rw [squarefreePairPoissonZeroMode_diag_product P hprime]
  have hp : (∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i))) =
      ((∏ i ∈ S, (1 - (1 : ℝ) / Ideal.absNorm (P i))) : ℝ) := by
    simp only [Complex.ofReal_prod, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_div, Complex.ofReal_natCast]
  rw [hp, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (primeDensity_nonneg_le_one P S).1]
  exact mul_le_of_le_one_right (by positivity) (primeDensity_nonneg_le_one P S).2

end ActualEisensteinCubic

namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge EisensteinSchwartzPoisson

noncomputable def idealPairPoissonZeroMode
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ := by
  letI : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  exact squarefreePairPoissonZeroMode (fun i : primePool F => i.1)
    Subtype.val_injective (primePool_good F hFgood)
    (idealSupport F I) (idealSupport F J) W scale

theorem weighted_idealPairPoissonZeroMode_eq_zero_of_ne
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    {I J : Ideal O} (hI : I ∈ F) (hJ : J ∈ F) (hIJ : I ≠ J)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    (star (baseChangeWeight χ I * A (Ideal.absNorm I)) *
        (baseChangeWeight χ J * A (Ideal.absNorm J))) *
      idealPairPoissonZeroMode F hFpos hFgood I J W scale = 0 := by
  by_cases hsI : Squarefree I
  · by_cases hsJ : Squarefree J
    · have hsupport : idealSupport F I ≠ idealSupport F J := fun h =>
        hIJ (idealSupport_injective_on_squarefree F hI hJ hsI hsJ h)
      let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
      have hz : idealPairPoissonZeroMode F hFpos hFgood I J W scale = 0 :=
        squarefreePairPoissonZeroMode_eq_zero_of_ne (fun i : primePool F => i.1)
          Subtype.val_injective (primePool_good F hFgood) hsupport W scale
      rw [hz, mul_zero]
    · simp [baseChangeWeight_eq_zero_of_not_squarefree χ hsJ]
  · simp [baseChangeWeight_eq_zero_of_not_squarefree χ hsI]

theorem idealRowSum_zeroMode_diagonal
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    (∑ I ∈ F, ∑ J ∈ F,
      (star (baseChangeWeight χ I * A (Ideal.absNorm I)) *
        (baseChangeWeight χ J * A (Ideal.absNorm J))) *
      idealPairPoissonZeroMode F hFpos hFgood I J W scale) =
    ∑ I ∈ F, (↑(‖baseChangeWeight χ I * A (Ideal.absNorm I)‖ ^ 2) : ℂ) *
      idealPairPoissonZeroMode F hFpos hFgood I I W scale := by
  apply Finset.sum_congr rfl
  intro I hI
  rw [Finset.sum_eq_single I]
  · rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    rfl
  · intro J hJ hJI
    exact weighted_idealPairPoissonZeroMode_eq_zero_of_ne F hFpos hFgood
      χ A hI hJ hJI.symm W scale
  · exact fun h => (h hI).elim

theorem norm_idealRowSum_zeroMode_le
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    ‖∑ I ∈ F, ∑ J ∈ F,
      (star (baseChangeWeight χ I * A (Ideal.absNorm I)) *
        (baseChangeWeight χ J * A (Ideal.absNorm J))) *
      idealPairPoissonZeroMode F hFpos hFgood I J W scale‖ ≤
    (|scale| * ‖paperRadialFourier W 0‖) *
      ∑ I ∈ F, ‖baseChangeWeight χ I * A (Ideal.absNorm I)‖ ^ 2 := by
  rw [idealRowSum_zeroMode_diagonal F hFpos hFgood χ A W scale, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun I hI => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  have hprime (i : primePool F) : Prime i.val := by
    obtain ⟨I, hI, hi⟩ := mem_primePool_iff.mp i.property
    exact UniqueFactorizationMonoid.prime_of_normalized_factor i.val hi
  have hb : ‖idealPairPoissonZeroMode F hFpos hFgood I I W scale‖ ≤
      |scale| * ‖paperRadialFourier W 0‖ :=
    norm_squarefreePairPoissonZeroMode_diag_le (fun i : primePool F => i.val)
      hprime Subtype.val_injective (primePool_good F hFgood) (idealSupport F I) W scale
  nlinarith [mul_le_mul_of_nonneg_left hb
    (sq_nonneg ‖baseChangeWeight χ I * A (Ideal.absNorm I)‖)]

end ConcretePrimeRowBridge

open scoped BigOperators Classical SchwartzMap ContDiff
namespace ActualEisensteinCubic
open ConcreteTraceCRT EisensteinSchwartzPoisson

theorem activeRow_norm_le_one
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S T : Finset ι) (h : O) :
    ‖finiteSexticRow (activePrimes P S T) (fun i => hgood i.val)
      (activeExponent S T) h‖ ≤ 1 := by
  rw [finiteSexticRow_activeSupport, norm_mul, norm_star]
  calc
    _ ≤ 1 * 1 := mul_le_mul
      (finiteSquarefreeRow_norm_le_one P hgood (S \ T) h)
      (finiteSquarefreeRow_norm_le_one P hgood (T \ S) h) (norm_nonneg _) (by norm_num)
    _ = 1 := one_mul _

theorem activeRow_paperFourier_summable
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S T : Finset ι)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    Summable (fun h : O => star (finiteSexticRow (activePrimes P S T)
      (fun i => hgood i.val) (activeExponent S T) h) *
        paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (paperRadialFourier_lattice_summable_norm W scale hscale)
  intro h
  rw [norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _) (activeRow_norm_le_one P hgood S T h)

theorem activeRow_paperFourier_zero_split
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S T : Finset ι)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) (den : ℝ) (hden : 0 < den) :
    let row := finiteSexticRow (activePrimes P S T) (fun i => hgood i.val)
      (activeExponent S T)
    (∑' h : O, star (row h) * paperRadialFourier W
      (scale * ‖eisEmbedding h‖ ^ 2 / den)) =
      star (row 0) * paperRadialFourier W 0 +
        ∑' h : O, if h = 0 then 0 else star (row h) * paperRadialFourier W
          (scale * ‖eisEmbedding h‖ ^ 2 / den) := by
  dsimp only
  have hs := activeRow_paperFourier_summable P hgood S T W
    (scale / den) (div_pos hscale hden)
  have heq (h : O) : scale / den * ‖eisEmbedding h‖ ^ 2 =
      scale * ‖eisEmbedding h‖ ^ 2 / den := by ring
  simp_rw [heq] at hs
  simpa only [map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
    zero_div] using hs.tsum_eq_add_tsum_ite 0

noncomputable def squarefreePairPoissonNonzeroMode
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ :=
  let Q := activePrimes P S T
  let hQ := activePrimes_pairwise_isCoprime P hinj S T
  let row := finiteSexticRow Q (fun i => hgood i.val) (activeExponent S T)
  let c := finitePrimeModulus Q
  ((scale : ℂ) * canonicalNormalizedGauss Q hQ (fun i => hgood i.val)
      (activeExponent S T) / (‖eisEmbedding c‖ : ℂ)) *
    ∑ E ∈ (S ∩ T).powerset,
      let d := primeSubsetGenerator P E
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) * row d /
        (‖eisEmbedding d‖ ^ 2 : ℝ)) *
        ∑' h : O, if h = 0 then 0 else star (row h) * paperRadialFourier W
          (scale * ‖eisEmbedding h‖ ^ 2 /
            (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding c‖ ^ 2))

theorem squarefreePairPoissonKernel_zero_split
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    squarefreePairPoissonKernel P hinj hgood S T W scale =
      squarefreePairPoissonZeroMode P hinj hgood S T W scale +
        squarefreePairPoissonNonzeroMode P hinj hgood S T W scale := by
  unfold squarefreePairPoissonKernel squarefreePairPoissonZeroMode
    squarefreePairPoissonNonzeroMode
  dsimp only
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro E hE
  have hden : 0 < ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 *
      ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖ ^ 2 :=
    mul_pos (sq_pos_of_pos (norm_pos_iff.mpr
      (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P E))))
      (sq_pos_of_pos (norm_pos_iff.mpr
        (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero (activePrimes P S T)))))
  rw [activeRow_paperFourier_zero_split P hgood S T W scale hscale _ hden, mul_add]

end ActualEisensteinCubic

namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge ConcreteTraceCRT EisensteinSchwartzPoisson

noncomputable def idealPrimeDensity (F : Finset (Ideal O)) (I : Ideal O) : ℝ :=
  ∏ i ∈ idealSupport F I, (1 - (1 : ℝ) / Ideal.absNorm i.val)

theorem idealPrimeDensity_mem_Icc
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥) (I : Ideal O) :
    idealPrimeDensity F I ∈ Set.Icc (0 : ℝ) 1 := by
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  exact primeDensity_nonneg_le_one (fun i : primePool F => i.val) (idealSupport F I)

theorem idealPairPoissonZeroMode_diag
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (I : Ideal O) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    idealPairPoissonZeroMode F hFpos hFgood I I W scale =
      (scale : ℂ) * paperRadialFourier W 0 * idealPrimeDensity F I := by
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  have hprime (i : primePool F) : Prime i.val := by
    obtain ⟨J, hJ, hi⟩ := mem_primePool_iff.mp i.property
    exact UniqueFactorizationMonoid.prime_of_normalized_factor i.val hi
  have heq := squarefreePairPoissonZeroMode_diag_product
    (fun i : primePool F => i.val) hprime Subtype.val_injective
    (primePool_good F hFgood) (idealSupport F I) W scale
  simpa only [idealPairPoissonZeroMode, idealPrimeDensity, Complex.ofReal_prod,
    Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div,
    Complex.ofReal_natCast] using heq

theorem idealRowSum_zeroMode_formula
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    (∑ I ∈ F, ∑ J ∈ F,
      (star (baseChangeWeight χ I * A (Ideal.absNorm I)) *
        (baseChangeWeight χ J * A (Ideal.absNorm J))) *
      idealPairPoissonZeroMode F hFpos hFgood I J W scale) =
    (scale : ℂ) * paperRadialFourier W 0 *
      ∑ I ∈ F, (↑(‖baseChangeWeight χ I * A (Ideal.absNorm I)‖ ^ 2) : ℂ) *
        idealPrimeDensity F I := by
  rw [idealRowSum_zeroMode_diagonal F hFpos hFgood χ A W scale, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [idealPairPoissonZeroMode_diag]
  ring

noncomputable def idealPairPoissonNonzeroMode
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ := by
  letI : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  exact squarefreePairPoissonNonzeroMode (fun i : primePool F => i.val)
    Subtype.val_injective (primePool_good F hFgood)
    (idealSupport F I) (idealSupport F J) W scale

theorem idealPairPoissonKernel_zero_split
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    idealPairPoissonKernel F hFpos hFgood I J W scale =
      idealPairPoissonZeroMode F hFpos hFgood I J W scale +
        idealPairPoissonNonzeroMode F hFpos hFgood I J W scale := by
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  exact squarefreePairPoissonKernel_zero_split (fun i : primePool F => i.val)
    Subtype.val_injective (primePool_good F hFgood)
    (idealSupport F I) (idealSupport F J) W scale hscale

theorem idealRowSum_smoothed_poisson_zero_split
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (hchar : ∀ i : primePool F, ringChar (O ⧸ i.val) ≠ 2)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' u : O, W (‖eisEmbedding u‖ ^ 2 / scale) *
      (↑(‖idealRowSum F hFpos hFgood χ A u‖ ^ 2) : ℂ)) =
    (scale : ℂ) * paperRadialFourier W 0 *
      (∑ I ∈ F, (↑(‖baseChangeWeight χ I * A (Ideal.absNorm I)‖ ^ 2) : ℂ) *
        idealPrimeDensity F I) +
      ∑ I ∈ F, ∑ J ∈ F,
        (star (baseChangeWeight χ I * A (Ideal.absNorm I)) *
          (baseChangeWeight χ J * A (Ideal.absNorm J))) *
        idealPairPoissonNonzeroMode F hFpos hFgood I J W scale := by
  rw [idealRowSum_smoothed_poisson F hFpos hFgood hchar χ A W scale hscale]
  simp_rw [idealPairPoissonKernel_zero_split F hFpos hFgood _ _ W scale hscale,
    mul_add, Finset.sum_add_distrib]
  rw [idealRowSum_zeroMode_formula F hFpos hFgood χ A W scale]

end ConcretePrimeRowBridge

namespace ShortDraftHeckeBridge

theorem norm_baseChangeWeight_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (I : Ideal O) :
    ‖baseChangeWeight χ I‖ ≤ 1 := by
  by_cases hI : Squarefree I
  · simp only [baseChangeWeight, hI.moebius_eq, Int.cast_pow, Int.cast_neg,
      Int.cast_one, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact χ.norm_le_one _
  · rw [ConcretePrimeRowBridge.baseChangeWeight_eq_zero_of_not_squarefree χ hI, norm_zero]
    exact zero_le_one

end ShortDraftHeckeBridge

namespace ConcretePrimeRowBridge

section
open ActualEisensteinCubic ShortDraftHeckeBridge EisensteinSchwartzPoisson

theorem norm_idealRowSum_zeroMode_le_test_mass
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    ‖∑ I ∈ F, ∑ J ∈ F,
      (star (baseChangeWeight χ I * A (Ideal.absNorm I)) *
        (baseChangeWeight χ J * A (Ideal.absNorm J))) *
      idealPairPoissonZeroMode F hFpos hFgood I J W scale‖ ≤
    (|scale| * ‖paperRadialFourier W 0‖) *
      ∑ I ∈ F, ‖A (Ideal.absNorm I)‖ ^ 2 := by
  refine (norm_idealRowSum_zeroMode_le F hFpos hFgood χ A W scale).trans ?_
  gcongr with I hI
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_baseChangeWeight_le_one χ I)

end

open ActualEisensteinCubic ShortDraftHeckeBridge

theorem idealSupport_image_eq_factors
    (F : Finset (Ideal O)) {I : Ideal O} (hI : I ∈ F) :
    (idealSupport F I).image Subtype.val =
      (UniqueFactorizationMonoid.normalizedFactors I).toFinset := by
  ext P
  simp only [Finset.mem_image, Multiset.mem_toFinset]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (mem_idealSupport_iff F I p).mp hp
  · intro hP
    let p : primePool F := ⟨P, mem_primePool_iff.mpr ⟨I, hI, hP⟩⟩
    exact ⟨p, (mem_idealSupport_iff F I p).mpr hP, rfl⟩

theorem idealSupport_product_eq
    (F : Finset (Ideal O)) {I : Ideal O} (hI : I ∈ F) (hsI : Squarefree I) :
    (∏ i ∈ idealSupport F I, i.val) = I := by
  have hnodup := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
    hsI.ne_zero).mp hsI
  calc
    _ = ∏ P ∈ (idealSupport F I).image Subtype.val, P := by
      rw [Finset.prod_image]
      exact fun a ha b hb h => Subtype.val_injective h
    _ = ∏ P ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset, P := by
      rw [idealSupport_image_eq_factors F hI]
    _ = (UniqueFactorizationMonoid.normalizedFactors I).prod := by
      change ((UniqueFactorizationMonoid.normalizedFactors I).toFinset.val.map id).prod = _
      rw [Multiset.map_id, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
    _ = I := Ideal.prod_normalizedFactors_eq_self hsI.ne_zero

end ConcretePrimeRowBridge

namespace ActualEisensteinCubic

theorem activeSupport_product_mul_common_sq
    {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    (P : ι → M) (S T : Finset ι) :
    (∏ i ∈ activeSupport S T, P i) * (∏ i ∈ S ∩ T, P i) ^ 2 =
      (∏ i ∈ S, P i) * (∏ i ∈ T, P i) := by
  have hset : activeSupport S T = (S ∪ T) \ (S ∩ T) := by
    ext i
    simp only [activeSupport, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hsub : S ∩ T ⊆ S ∪ T := Finset.inter_subset_left.trans Finset.subset_union_left
  calc
    _ = ((∏ i ∈ activeSupport S T, P i) * (∏ i ∈ S ∩ T, P i)) *
      (∏ i ∈ S ∩ T, P i) := by rw [pow_two, mul_assoc]
    _ = (∏ i ∈ S ∪ T, P i) * (∏ i ∈ S ∩ T, P i) := by
      rw [hset, Finset.prod_sdiff hsub]
    _ = _ := Finset.prod_union_inter

theorem activePrimeModulus_norm_sq
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S T : Finset ι) :
    ‖ConcreteTraceCRT.eisEmbedding (finitePrimeModulus (activePrimes P S T))‖ ^ 2 =
      (Ideal.absNorm (∏ i ∈ activeSupport S T, P i) : ℝ) := by
  rw [finitePrimeModulus_norm_sq]
  congr 2
  exact Finset.prod_coe_sort (activeSupport S T) P

end ActualEisensteinCubic

namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge

theorem idealSupport_active_conductor_mul_common_sq
    (F : Finset (Ideal O)) {I J : Ideal O} (hI : I ∈ F) (hJ : J ∈ F)
    (hsI : Squarefree I) (hsJ : Squarefree J) :
    (∏ i ∈ activeSupport (idealSupport F I) (idealSupport F J), i.val) *
      (primeSubsetProduct F (idealSupport F I ∩ idealSupport F J)) ^ 2 = I * J := by
  rw [primeSubsetProduct, activeSupport_product_mul_common_sq,
    idealSupport_product_eq F hI hsI, idealSupport_product_eq F hJ hsJ]

theorem idealPairPoisson_conductor_norm_sq
    (F : Finset (Ideal O)) {I J : Ideal O} (hI : I ∈ F) (hJ : J ∈ F)
    (hsI : Squarefree I) (hsJ : Squarefree J) :
    ‖ConcreteTraceCRT.eisEmbedding (finitePrimeModulus
      (activePrimes (fun i : primePool F => i.val) (idealSupport F I) (idealSupport F J)))‖ ^ 2 *
      (Ideal.absNorm (primeSubsetProduct F (idealSupport F I ∩ idealSupport F J)) : ℝ) ^ 2 =
      (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) := by
  rw [activePrimeModulus_norm_sq]
  have hn := congrArg (fun K : Ideal O => (Ideal.absNorm K : ℝ))
    (idealSupport_active_conductor_mul_common_sq F hI hJ hsI hsJ)
  simpa only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow] using hn

theorem idealPairPoisson_conductor_norm_sq_of_weight_ne_zero
    (F : Finset (Ideal O)) {I J : Ideal O} (hI : I ∈ F) (hJ : J ∈ F)
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hwI : baseChangeWeight χ I ≠ 0) (hwJ : baseChangeWeight χ J ≠ 0) :
    ‖ConcreteTraceCRT.eisEmbedding (finitePrimeModulus
      (activePrimes (fun i : primePool F => i.val) (idealSupport F I) (idealSupport F J)))‖ ^ 2 *
      (Ideal.absNorm (primeSubsetProduct F (idealSupport F I ∩ idealSupport F J)) : ℝ) ^ 2 =
      (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) := by
  have hsI : Squarefree I := by
    by_contra h
    exact hwI (baseChangeWeight_eq_zero_of_not_squarefree χ h)
  have hsJ : Squarefree J := by
    by_contra h
    exact hwJ (baseChangeWeight_eq_zero_of_not_squarefree χ h)
  exact idealPairPoisson_conductor_norm_sq F hI hJ hsI hsJ

end ConcretePrimeRowBridge

end

end OAI
