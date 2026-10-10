import OAI.Probability.TraceReconstruction.Model
import OAI.Probability.TraceReconstruction.Parity
import OAI.Probability.TraceReconstruction.Ranks

namespace OAI

/-!
# Differences

Tensor gap differences, positional shifts, two-gap elimination, central clipping, disjoint rank regions, and weighted period sums.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology

namespace TraceReconstruction

/-- Forward length differences of the actual binomial probability
polynomial, before imposing the conditional rank total. -/
def binomialLengthDifference (g s : ℕ) (p : ℝ) : IntSeries :=
  (biasedSeries 1 p - 1)^s * biasedSeries g p

/-- Increasing the number of trials corresponds exactly to multiplying
by the Bernoulli step polynomial. -/
theorem binomialLengthDifference_succ (g s : ℕ) (p : ℝ) :
    binomialLengthDifference g (s+1) p =
      binomialLengthDifference (g+1) s p - binomialLengthDifference g s p := by
  unfold binomialLengthDifference
  rw [biasedSeries_add]
  ring

theorem biasedSeries_step_sub_one (p : ℝ) :
    biasedSeries 1 p - 1 = (-p) • firstDifference := by
  unfold biasedSeries firstDifference
  rw [pow_one,smul_sub,AddMonoidAlgebra.smul_single,AddMonoidAlgebra.smul_single]
  simp only [smul_eq_mul,mul_one]
  have h1 : (1 : IntSeries) = AddMonoidAlgebra.single 0 1 := rfl
  rw [h1]
  simp only [AddMonoidAlgebra.single_sub]
  ext z
  simp only [AddMonoidAlgebra.coeff_sub,AddMonoidAlgebra.coeff_add,
    Finsupp.sub_apply,Finsupp.add_apply,AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
  split_ifs <;> ring

theorem binomialLengthDifference_eq (g s : ℕ) (p : ℝ) :
    binomialLengthDifference g s p =
      (-p)^s • (firstDifference^s * biasedSeries g p) := by
  unfold binomialLengthDifference
  rw [biasedSeries_step_sub_one,smul_pow,smul_mul_assoc]

theorem seriesL2Sq_smul (c : ℝ) (f : IntSeries) :
    seriesL2Sq (c • f) = c^2 * seriesL2Sq f := by
  unfold seriesL2Sq
  simp only [AddMonoidAlgebra.coeff_smul,Finsupp.smul_apply,smul_eq_mul,mul_pow]
  exact tsum_mul_left

/-- Pointwise and square-sum bounds for every forward length difference.
The quotient form keeps every order and every channel factor explicit. -/
theorem binomialLengthDifference_bounds (g s : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    (∀ z : ℤ, |(binomialLengthDifference g s p).coeff z| ≤
      (2*biasedBinomialBound (g/(s+1)) p)^s * biasedBinomialBound (g/(s+1)) p) ∧
    (seriesL2Sq (binomialLengthDifference g s p) ≤
      ((2*biasedBinomialBound (g/(s+1)) p)^s)^2 * biasedBinomialBound (g/(s+1)) p) := by
  have hpow : |(-p)^s| ≤ 1 := by
    rw [abs_pow,abs_neg,abs_of_pos hp.1]
    exact pow_le_one₀ hp.1.le hp.2.le
  have hs := biased_difference_smoothing g s hp
  rw [binomialLengthDifference_eq]
  constructor
  · intro z
    simp only [AddMonoidAlgebra.coeff_smul,Finsupp.smul_apply,smul_eq_mul,abs_mul]
    exact (mul_le_mul_of_nonneg_right hpow (abs_nonneg _)).trans (by simpa using hs.1 z)
  · rw [seriesL2Sq_smul]
    have h : ((-p)^s) ^ 2 ≤ 1 := by nlinarith [sq_abs ((-p)^s),abs_nonneg ((-p)^s)]
    exact (mul_le_mul_of_nonneg_right h (seriesL2Sq_nonneg _)).trans (by simpa using hs.2)

/-- Explicit fixed-order smoothing constant; no asymptotic hypothesis is hidden. -/
def lengthDifferenceConstant (s : ℕ) (p : ℝ) : ℝ :=
  2 * Real.sqrt (((s:ℝ)+1)/(p*(1-p)))

theorem lengthDifferenceConstant_pos (s : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    0 < lengthDifferenceConstant s p := by
  unfold lengthDifferenceConstant
  positivity [hp.1,sub_pos.mpr hp.2]

theorem biasedBinomialBound_length_le (g s : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    2*biasedBinomialBound (g/(s+1)) p ≤
      lengthDifferenceConstant s p / Real.sqrt ((g:ℝ)+1) := by
  calc
    _ ≤ 2*Real.sqrt (((s:ℝ)+1)/(((g:ℝ)+1)*p*(1-p))) :=
      mul_le_mul_of_nonneg_left (biasedBinomialBound_quotient_le g s hp) (by norm_num)
    _ = _ := by
      unfold lengthDifferenceConstant
      rw [show ((s:ℝ)+1)/(((g:ℝ)+1)*p*(1-p)) =
        (((s:ℝ)+1)/(p*(1-p)))/((g:ℝ)+1) by field_simp]
      rw [Real.sqrt_div (by positivity [hp.1,sub_pos.mpr hp.2])]
      ring

/-- Squared supremum and squared L2 smoothing estimates in a form suitable
for exact constrained rank profiles. -/
theorem binomialLengthDifference_numeric (g s : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    (∀ z : ℤ, (binomialLengthDifference g s p).coeff z ^ 2 ≤
      (lengthDifferenceConstant s p)^(2*s+2) / ((g:ℝ)+1)^(s+1)) ∧
    (seriesL2Sq (binomialLengthDifference g s p) ≤
      (lengthDifferenceConstant s p)^(2*s+1) /
        (((g:ℝ)+1)^s * Real.sqrt ((g:ℝ)+1))) := by
  have hb := binomialLengthDifference_bounds g s hp
  have hc := biasedBinomialBound_length_le g s hp
  have hB : 0 ≤ biasedBinomialBound (g/(s+1)) p := Real.sqrt_nonneg _
  have hC : 0 < lengthDifferenceConstant s p := lengthDifferenceConstant_pos s hp
  have hg : 0 < Real.sqrt ((g:ℝ)+1) := Real.sqrt_pos.mpr (by positivity)
  have hB' : biasedBinomialBound (g/(s+1)) p ≤
      lengthDifferenceConstant s p / Real.sqrt ((g:ℝ)+1) := by linarith
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 2*biasedBinomialBound (g/(s+1)) p) hc s
  constructor
  · intro z
    have h := (hb.1 z).trans (mul_le_mul hs hB' hB (by positivity))
    rw [← pow_succ] at h
    have hsq := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs] at hsq
    refine hsq.trans_eq ?_
    rw [← pow_mul,div_pow]
    have he : (s+1)*2=2*s+2 := by omega
    rw [he]
    congr 1
    rw [show 2*s+2=2*(s+1) by omega,pow_mul,Real.sq_sqrt (by positivity)]
  · have hsq := pow_le_pow_left₀ (by positivity :
        0 ≤ (2*biasedBinomialBound (g/(s+1)) p)^s) hs 2
    refine hb.2.trans ((mul_le_mul hsq hB' hB (by positivity)).trans_eq ?_)
    rw [← pow_mul,← pow_succ,div_pow]
    congr 1
    · congr 1; omega
    · rw [pow_succ,show s*2=2*s by omega,pow_mul,Real.sq_sqrt (by positivity)]

end TraceReconstruction

namespace TraceReconstruction

theorem series_finite_sum_sq_le {α : Type*} [Fintype α]
    (f : IntSeries) (z : α → ℤ) (hz : Function.Injective z) :
    (∑ a, f.coeff (z a)^2) ≤ seriesL2Sq f := by
  simpa only [tsum_fintype,seriesL2Sq] using
    Summable.tsum_le_tsum_of_inj z hz (fun _ _ => sq_nonneg _)
      (fun _ => le_rfl) (hasSum_fintype _).summable (series_summable f (fun x => x^2) (by simp))

/-- Product coefficients of signed gap series, including an arbitrary
translation of each observed rank gap. -/
def signedRankProduct {l r : ℕ} (f : Fin (r+1) → IntSeries)
    (shift : Fin (r+1) → ℤ) (v : IncreasingTuple l r) : ℝ :=
  ∏ i, (f i).coeff ((tupleGap v.val i : ℤ)-shift i)

/-- Largest-gap elimination also holds for signed finite-difference series.
The fixed sum of the observed gaps supplies the missing square-root factor;
translations are unrestricted and the estimate contains no omitted ranks. -/
theorem signedRankProduct_square_sum_le {l r : ℕ}
    (f : Fin (r+1) → IntSeries) (shift : Fin (r+1) → ℤ)
    (e : Fin (r+1)) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z : ℤ, (f e).coeff z ^ 2 ≤ M) :
    (∑ v : IncreasingTuple l r, signedRankProduct f shift v ^ 2) ≤
      M * ∏ i : Fin r, seriesL2Sq (f (Equiv.swap 0 e i.succ)) := by
  classical
  let σ : Equiv.Perm (Fin (r+1)) := Equiv.swap 0 e
  let F : Fin (r+1) → Fin (l-r+1) → ℝ :=
    fun i k => (f (σ i)).coeff ((k.val:ℤ)-shift (σ i)) ^ 2
  have hF : ∀ i k, 0 ≤ F i k := fun _ _ => sq_nonneg _
  have hpoint (v : IncreasingTuple l r) :
      signedRankProduct f shift v ^ 2 = ∏ i, F i (rankGapProfile σ v i) := by
    unfold signedRankProduct
    rw [← Finset.prod_pow]
    dsimp [F,rankGapProfile]
    exact (Equiv.prod_comp σ _).symm
  simp_rw [hpoint]
  calc
    _ ≤ ∑ z : Fin (r+1) → Fin (l-r+1),
        if ∑ i, (z i).val = l-r then ∏ i, F i (z i) else 0 := by
      exact sum_injective_profile_le (rankGapProfile σ) (rankGapProfile_injective σ)
        (fun z => ∑ i, (z i).val = l-r) (rankGapProfile_sum σ)
        (fun z => ∏ i, F i (z i)) (fun _ => Finset.prod_nonneg (fun _ _ => hF _ _))
    _ ≤ M * ∏ i : Fin r, ∑ k : Fin (l-r+1), F i.succ k :=
      constrained_sum_product_le r (l-r) F hF M hM (by
        intro k
        simpa only [F,σ,Equiv.swap_apply_left] using hbound ((k.val:ℤ)-shift e))
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hM
      apply Finset.prod_le_prod₀ (fun _ _ => Finset.sum_nonneg (fun _ _ => hF _ _))
      intro i _
      dsimp only [F]
      apply series_finite_sum_sq_le
      intro a b h
      exact Fin.ext (Int.ofNat_inj.mp (sub_left_injective h))

/-- Finite mixtures of signed rank products can be estimated termwise.
This is the exact Cauchy--Schwarz form used when expanding positional
finite-difference operators into gap derivatives. -/
theorem rank_mixture_square_sum_le {α V : Type*} [Fintype α] [Fintype V]
    (c : α → ℝ) (F : α → V → ℝ) (B : α → ℝ)
    (hB : ∀ a, (∑ v, F a v ^ 2) ≤ B a) :
    (∑ v, (∑ a, c a * F a v)^2) ≤ (∑ a, |c a|) * ∑ a, |c a| * B a := by
  have hp (v : V) : (∑ a, c a*F a v)^2 ≤
      (∑ a, |c a|) * ∑ a, |c a| * F a v^2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun _ _ => abs_nonneg _) (fun _ _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
    intro a _
    rw [mul_pow,← mul_assoc,← sq, sq_abs]
  calc
    _ ≤ ∑ v, (∑ a, |c a|) * ∑ a, |c a| * F a v^2 :=
      Finset.sum_le_sum (fun v _ => hp v)
    _ = (∑ a, |c a|) * ∑ a, |c a| * ∑ v, F a v^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (hB a) (abs_nonneg _)

end TraceReconstruction

namespace TraceReconstruction

/-- The tensor product of finitely supported one-dimensional coefficient
series, represented on its literal vector-valued exponents. -/
def tensorSeries {ι : Type*} [Fintype ι] (f : ι → IntSeries) :
    AddMonoidAlgebra ℝ (ι → ℤ) :=
by
  classical
  exact AddMonoidAlgebra.ofCoeff (Finsupp.onFinset (Fintype.piFinset (fun i => (f i).coeff.support))
    (fun z => ∏ i, (f i).coeff (z i)) (by
      classical
      intro z hz
      simp only [Fintype.mem_piFinset,Finsupp.mem_support_iff]
      exact fun i => (Finset.prod_ne_zero_iff.mp hz) i (Finset.mem_univ i)))

theorem tensorSeries_coeff {ι : Type*} [Fintype ι] (f : ι → IntSeries) (z : ι → ℤ) :
    (tensorSeries f).coeff z = ∏ i, (f i).coeff (z i) := rfl

theorem tensorSeries_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → IntSeries) :
    (tensorSeries f).coeff.support = Fintype.piFinset (fun i => (f i).coeff.support) := by
  classical
  ext z
  simp [tensorSeries_coeff,Finset.prod_ne_zero_iff]

/-- Literal tensor multiplication is coordinatewise convolution. -/
theorem tensorSeries_mul {ι : Type*} [Fintype ι] (f g : ι → IntSeries) :
    tensorSeries (fun i => f i*g i) = tensorSeries f * tensorSeries g := by
  classical
  ext z
  rw [tensorSeries_coeff,AddMonoidAlgebra.coeff_mul_apply_left,Finsupp.sum,tensorSeries_support]
  simp_rw [tensorSeries_coeff,← Finset.prod_mul_distrib]
  simp only [Pi.add_apply, Pi.neg_apply]
  rw [← Finset.prod_univ_sum (fun i => (f i).coeff.support)
    (fun i j => (f i).coeff j * (g i).coeff (-j + z i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [AddMonoidAlgebra.coeff_mul_apply_left,Finsupp.sum]

theorem tensorSeries_one {ι : Type*} [Fintype ι] :
    tensorSeries (fun _ : ι => (1 : IntSeries)) = 1 := by
  classical
  ext z
  rw [tensorSeries_coeff]
  change (∏ i, Finsupp.single 0 (1:ℝ) (z i)) = Finsupp.single 0 (1:ℝ) z
  simp only [Finsupp.single_apply]
  by_cases hz : z = 0
  · subst z; simp
  · have he : ∃ i, z i ≠ 0 := by simpa [funext_iff] using hz
    obtain ⟨i,hi⟩ := he
    rw [ite_eq_right (Ne.symm hz)]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Ne.symm hi])


/-- Embedding one integral exponent into its own gap coordinate. -/
def coordinateExponent {ι : Type*} [DecidableEq ι] (i : ι) : ℤ →+ (ι → ℤ) where
  toFun := fun a => Pi.single (M := fun _ => ℤ) i a
  map_zero' := Pi.single_zero i
  map_add' := fun a b => by
    ext j
    by_cases h : j=i
    · subst j; simp
    · simp [Pi.single_eq_of_ne h]

def coordinateSeriesHom {ι : Type*} [DecidableEq ι] (i : ι) :
    IntSeries →+* AddMonoidAlgebra ℝ (ι → ℤ) :=
  AddMonoidAlgebra.mapDomainRingHom ℝ (coordinateExponent i)

theorem coordinateExponent_injective {ι : Type*} [DecidableEq ι] (i : ι) :
    Function.Injective (coordinateExponent i) := by
  intro a b h
  simpa only [coordinateExponent,AddMonoidHom.coe_mk,ZeroHom.coe_mk,Pi.single_eq_same]
    using congrFun h i

theorem tensorSeries_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (f : IntSeries) :
    tensorSeries (fun j => if j=i then f else 1) = coordinateSeriesHom i f := by
  classical
  ext z
  rw [tensorSeries_coeff]
  change (∏ j, (if j=i then f else (1:IntSeries)).coeff (z j)) =
    (Finsupp.mapDomain (coordinateExponent i) f.coeff) z
  by_cases hz : ∀ j, j ≠ i → z j = 0
  · have he : coordinateExponent i (z i) = z := by
      funext j
      by_cases hj : j=i
      · subst j; simp [coordinateExponent]
      · simp [coordinateExponent,Pi.single_eq_of_ne hj,hz j hj]
    rw [← he,Finsupp.mapDomain_apply_of_injective (coordinateExponent_injective i)]
    rw [Finset.prod_eq_single i]
    · simp [coordinateExponent]
    · intro j _ hj
      simp [hj,coordinateExponent]
    · simp
  · push Not at hz
    obtain ⟨j,hji,hj⟩ := hz
    have hn : z ∉ Set.range (coordinateExponent i) := by
      rintro ⟨a,ha⟩
      have h := congrFun ha j
      simp [coordinateExponent,Pi.single_eq_of_ne hji] at h
      exact hj h.symm
    rw [Finsupp.mapDomain_of_notMem_range _ _ hn]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp only [ite_eq_right hji]
    change Finsupp.single 0 (1:ℝ) (z j) = 0
    simp [Ne.symm hj]

theorem tensorSeries_prod {ι α : Type*} [Fintype ι]
    (s : Finset α) (f : α → ι → IntSeries) :
    tensorSeries (fun i => ∏ a ∈ s, f a i) = ∏ a ∈ s, tensorSeries (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tensorSeries_one]
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    rw [tensorSeries_mul,ih]

/-- The literal product of the coordinate embeddings has precisely the
independent product coefficients, with no external tensor-product axioms. -/
theorem tensorSeries_eq_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → IntSeries) :
    tensorSeries f = ∏ i, coordinateSeriesHom i (f i) := by
  have he : f = fun j => ∏ i, if j=i then f i else 1 := by
    funext j
    simp
  conv_lhs => rw [he,tensorSeries_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact tensorSeries_coordinate i (f i)

end TraceReconstruction

namespace TraceReconstruction

/-- Explicit fixed-order gap derivative bound, uniformly over translated
rank restrictions and the choice of the eliminated gap. -/
theorem rank_gap_derivatives_bound {l r : ℕ}
    (g s : Fin (r+1) → ℕ) (shift : Fin (r+1) → ℤ)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (e : Fin (r+1)) :
    (∑ v : IncreasingTuple l r,
      signedRankProduct (fun i => binomialLengthDifference (g i) (s i) p) shift v ^ 2) ≤
    (lengthDifferenceConstant (s e) p)^(2*s e+2) / ((g e:ℝ)+1)^(s e+1) *
      ∏ i : Fin r,
        (lengthDifferenceConstant (s (Equiv.swap 0 e i.succ)) p)^(2*s (Equiv.swap 0 e i.succ)+1) /
        (((g (Equiv.swap 0 e i.succ):ℝ)+1)^(s (Equiv.swap 0 e i.succ)) *
          Real.sqrt ((g (Equiv.swap 0 e i.succ):ℝ)+1)) := by
  have hC := (lengthDifferenceConstant_pos (s e) hp).le
  refine (signedRankProduct_square_sum_le _ shift e _ (by positivity)
    (binomialLengthDifference_numeric (g e) (s e) hp).1).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.prod_le_prod₀ (fun _ _ => seriesL2Sq_nonneg _)
  intro i _
  exact (binomialLengthDifference_numeric _ _ hp).2

/-- Increasing an order increases only its explicit smoothing constant. -/
theorem lengthDifferenceConstant_mono {s t : ℕ} (hst : s ≤ t)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    lengthDifferenceConstant s p ≤ lengthDifferenceConstant t p := by
  unfold lengthDifferenceConstant
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.sqrt_le_sqrt
  exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hst)
    (mul_pos hp.1 (sub_pos.mpr hp.2)).le

end TraceReconstruction

namespace TraceReconstruction

inductive GapDifference
  | unchanged | first | second
  deriving DecidableEq

def GapDifference.order : GapDifference → ℕ
  | .unchanged => 0 | .first => 1 | .second => 2

def adjacentGap {r : ℕ} (h : Fin r) (b : Bool) : Fin (r+1) :=
  if b then h.succ else h.castSucc

def gapTermWeight (k : GapDifference) (a : Bool × Bool) : ℝ :=
  match k with
  | .unchanged => 1/4
  | .first => (if a.1 then -1 else 1)/2
  | .second => (if a.1 then -1 else 1)*(if a.2 then -1 else 1)/2

def gapTermOrder {r : ℕ} (h : Fin r) (k : GapDifference) (a : Bool × Bool)
    (i : Fin (r+1)) : ℕ :=
  match k with
  | .unchanged => 0
  | .first => if i = adjacentGap h a.1 then 1 else 0
  | .second => (if i = adjacentGap h a.1 then 1 else 0) +
      (if i = adjacentGap h a.2 then 1 else 0)

def gapTermExtra {r : ℕ} (h : Fin r) (k : GapDifference) (a : Bool × Bool)
    (i : Fin (r+1)) : ℕ :=
  match k with
  | .unchanged => (if i = h.castSucc then 1 else 0) + (if i = h.succ then 1 else 0)
  | .first => if i = adjacentGap h a.2 then 1 else 0
  | .second => 0

/-- Polynomial of a centered positional operator after removing from
both incident gaps the one unit needed for either direction of movement. -/
def gapOperator {r : ℕ} (h : Fin r) (k : GapDifference) (p : ℝ) :
    AddMonoidAlgebra ℝ (Fin (r+1) → ℤ) :=
  let L := coordinateSeriesHom h.castSucc (biasedSeries 1 p)
  let R := coordinateSeriesHom h.succ (biasedSeries 1 p)
  match k with
  | .unchanged => L*R
  | .first => (1/2:ℝ) • (L^2-R^2)
  | .second => (1/2:ℝ) • (L^2+R^2-2*L*R)

theorem tensorSeries_two_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι) (f g : IntSeries) :
    tensorSeries (fun i => f^(if i=a then 1 else 0) * g^(if i=b then 1 else 0)) =
      coordinateSeriesHom a f * coordinateSeriesHom b g := by
  rw [tensorSeries_mul]
  have h (c : ι) (u : IntSeries) :
      (fun i => u^(if i=c then 1 else 0)) = (fun i => if i=c then u else 1) := by
    funext i
    split <;> simp
  rw [h,h,tensorSeries_coordinate,tensorSeries_coordinate]

theorem gapLocalTerm_factor {r : ℕ} (h : Fin r) (k : GapDifference)
    (a : Bool × Bool) (p : ℝ) :
    tensorSeries (fun i => (biasedSeries 1 p-1)^gapTermOrder h k a i *
      (biasedSeries 1 p)^gapTermExtra h k a i) =
      match k with
      | .unchanged => coordinateSeriesHom h.castSucc (biasedSeries 1 p) *
          coordinateSeriesHom h.succ (biasedSeries 1 p)
      | .first => (coordinateSeriesHom (adjacentGap h a.1) (biasedSeries 1 p)-1) *
          coordinateSeriesHom (adjacentGap h a.2) (biasedSeries 1 p)
      | .second => (coordinateSeriesHom (adjacentGap h a.1) (biasedSeries 1 p)-1) *
          (coordinateSeriesHom (adjacentGap h a.2) (biasedSeries 1 p)-1) := by
  cases k <;> simp only [gapTermOrder,gapTermExtra,pow_zero,pow_add,one_mul,mul_one]
  all_goals rw [tensorSeries_two_coordinates]
  all_goals simp only [map_sub,map_one]

/-- Exact four-term assignment of positional differences to the adjacent
binomial gap lengths, including all signs and all bounded shifts. -/
theorem gapOperator_expansion {r : ℕ} (h : Fin r) (k : GapDifference) (p : ℝ) :
    gapOperator h k p = ∑ a : Bool × Bool, gapTermWeight k a •
      tensorSeries (fun i => (biasedSeries 1 p-1)^gapTermOrder h k a i *
        (biasedSeries 1 p)^gapTermExtra h k a i) := by
  simp_rw [gapLocalTerm_factor]
  cases k <;> simp only [gapOperator,gapTermWeight,Fintype.sum_prod_type,
    Fintype.sum_bool,adjacentGap,Bool.false_eq_true,ite_false,ite_true]
  · module
  all_goals simp only [Algebra.smul_def]
  all_goals norm_num
  all_goals ring

theorem gapTermWeight_l1 (k : GapDifference) :
    (∑ a : Bool × Bool, |gapTermWeight k a|) ≤ 2 := by
  cases k <;> norm_num [gapTermWeight,Fintype.sum_prod_type,Fintype.sum_bool]

theorem gapTermOrder_total {r : ℕ} (h : Fin r) (k : GapDifference) (a : Bool × Bool) :
    (∑ i, gapTermOrder h k a i) = k.order := by
  cases k <;> simp [gapTermOrder,GapDifference.order,Finset.sum_add_distrib]

/-- Exact global expansion inside the unconstrained vector of gap counts. -/
theorem gapOperators_expansion {r : ℕ} (g : Fin (r+1) → ℕ)
    (k : Fin r → GapDifference) (p : ℝ) :
    tensorSeries (fun i => biasedSeries (g i) p) * (∏ h, gapOperator h (k h) p) =
      ∑ a : Fin r → Bool × Bool, (∏ h, gapTermWeight (k h) (a h)) •
        tensorSeries (fun i => binomialLengthDifference
          (g i + ∑ h, gapTermExtra h (k h) (a h) i)
          (∑ h, gapTermOrder h (k h) (a h) i) p) := by
  classical
  simp_rw [gapOperator_expansion]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.prod_smul, mul_smul_comm, ← tensorSeries_prod, ← tensorSeries_mul]
  congr 2
  funext i
  simp only [binomialLengthDifference,biasedSeries,
    Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  ring

theorem gapOperators_weight_l1 {r : ℕ} (k : Fin r → GapDifference) :
    (∑ a : Fin r → Bool × Bool, |∏ h, gapTermWeight (k h) (a h)|) ≤ (2:ℝ)^r := by
  simp_rw [Finset.abs_prod]
  rw [← Fintype.prod_sum (fun h a => |gapTermWeight (k h) a|)]
  calc
    _ ≤ ∏ _h : Fin r, (2:ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
      intro h _
      exact gapTermWeight_l1 (k h)
    _ = _ := by simp

end TraceReconstruction



noncomputable section
namespace TraceReconstruction

theorem prod_eliminate_fin {α : Type*} [CommMonoid α] {r : ℕ}
    (f : Fin (r+1) → α) (e : Fin (r+1)) :
    f e * (∏ i : Fin r, f (Equiv.swap 0 e i.succ)) = ∏ i, f i := by
  calc
    _ = ∏ i : Fin (r+1), f (Equiv.swap 0 e i) := by
      rw [Fin.prod_univ_succ,Equiv.swap_apply_left]
    _ = _ := Equiv.prod_comp (Equiv.swap 0 e) f

/-- Uniform smoothing with the individual gap scale retained, and a common
lower gap scale reserved for every derivative order. -/
theorem lengthDifference_uniform (g b s : ℕ) {p C G : ℝ}
    (hp : p ∈ Set.Ioo 0 1) (hC : lengthDifferenceConstant s p ≤ C)
    (hG : 0 < G) (hb : b ≤ g) (hGg : G ≤ (g:ℝ)+1) :
    (∀ z : ℤ, (binomialLengthDifference g s p).coeff z^2 ≤
      (C/Real.sqrt ((b:ℝ)+1)) * (C^(2*s+1)/(G^s*Real.sqrt ((b:ℝ)+1)))) ∧
    seriesL2Sq (binomialLengthDifference g s p) ≤
      C^(2*s+1)/(G^s*Real.sqrt ((b:ℝ)+1)) := by
  have hC0 : 0 < C := (lengthDifferenceConstant_pos s hp).trans_le hC
  have hb0 : 0 < (b:ℝ)+1 := by positivity
  have hg0 : 0 < (g:ℝ)+1 := by positivity
  have hb' : (b:ℝ)+1 ≤ (g:ℝ)+1 := by exact_mod_cast Nat.add_le_add_right hb 1
  have hpow : G^s ≤ ((g:ℝ)+1)^s := pow_le_pow_left₀ hG.le hGg s
  have hx := binomialLengthDifference_numeric g s hp
  constructor
  · intro z
    refine (hx.1 z).trans ?_
    have hc := pow_le_pow_left₀ (lengthDifferenceConstant_pos s hp).le hC (2*s+2)
    have hd : G^s*((b:ℝ)+1) ≤ ((g:ℝ)+1)^(s+1) := by
      rw [pow_succ]
      exact mul_le_mul hpow hb' hb0.le (by positivity)
    calc
      _ ≤ C^(2*s+2)/(G^s*((b:ℝ)+1)) := by
        apply div_le_div₀ (by positivity) hc (by positivity) hd
      _ = _ := by
        have hsq := Real.sq_sqrt hb0.le
        have hs : Real.sqrt ((b:ℝ)+1) ≠ 0 := (Real.sqrt_pos.mpr hb0).ne'
        rw [show 2*s+2=(2*s+1)+1 by omega,pow_succ]
        field_simp
        nlinarith only [hsq]
  · refine hx.2.trans ?_
    apply div_le_div₀ (by positivity)
      (pow_le_pow_left₀ (lengthDifferenceConstant_pos s hp).le hC (2*s+1))
      (by positivity)
    exact mul_le_mul hpow (Real.sqrt_le_sqrt hb') (Real.sqrt_nonneg _) (by positivity)

/-- A single translated signed rank product, with every smoothing scale
and the largest-gap constraint exposed. -/
theorem rank_derivatives_uniform {l r : ℕ}
    (g b s : Fin (r+1) → ℕ) (shift : Fin (r+1) → ℤ)
    {p C G : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (hC : ∀ i, lengthDifferenceConstant (s i) p ≤ C) (hG : 0 < G)
    (hb : ∀ i, b i ≤ g i) (hGg : ∀ i, G ≤ (g i:ℝ)+1) (e : Fin (r+1)) :
    (∑ v : IncreasingTuple l r,
      signedRankProduct (fun i => binomialLengthDifference (g i) (s i) p) shift v ^ 2) ≤
      C^(2*(∑ i, s i)+r+2) /
        (G^(∑ i, s i) * Real.sqrt ((b e:ℝ)+1) * ∏ i, Real.sqrt ((b i:ℝ)+1)) := by
  let F (i : Fin (r+1)) : ℝ := C^(2*s i+1)/(G^(s i)*Real.sqrt ((b i:ℝ)+1))
  have hC0 : 0 < C := (lengthDifferenceConstant_pos (s e) hp).trans_le (hC e)
  have hF : ∀ i, 0 ≤ F i := fun i => by dsimp [F]; positivity
  have hbound (i : Fin (r+1)) := lengthDifference_uniform (g i) (b i) (s i) hp (hC i) hG (hb i) (hGg i)
  calc
    _ ≤ (C/Real.sqrt ((b e:ℝ)+1)*F e) *
        ∏ i : Fin r, seriesL2Sq (binomialLengthDifference (g (Equiv.swap 0 e i.succ))
          (s (Equiv.swap 0 e i.succ)) p) := by
      apply signedRankProduct_square_sum_le _ shift e _ (by positivity [hF e])
      exact (hbound e).1
    _ ≤ (C/Real.sqrt ((b e:ℝ)+1)*F e) * ∏ i : Fin r, F (Equiv.swap 0 e i.succ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity [hF e])
      apply Finset.prod_le_prod₀ (fun _ _ => seriesL2Sq_nonneg _)
      intro i _
      exact (hbound _).2
    _ = (C/Real.sqrt ((b e:ℝ)+1))*∏ i, F i := by
      rw [mul_assoc,prod_eliminate_fin]
    _ = _ := by
      simp only [F,Finset.prod_div_distrib,Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum,Finset.sum_add_distrib,← Finset.mul_sum,
        Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]
      rw [show 2*(∑ i, s i)+r+2=(2*(∑ i, s i)+(r+1))+1 by omega,pow_succ]
      ring

end TraceReconstruction



noncomputable section
namespace TraceReconstruction

/-- Enough vacant slots for independent one-step displacements of every tag. -/
def SafeTaggedTuple {n r : ℕ} (p : Fin r → Fin n) : Prop :=
  (∀ i, 1 ≤ (p i).val ∧ (p i).val+1 < n) ∧
  ∀ i j, i < j → (p i).val+3 ≤ (p j).val

def shiftedTag {n r : ℕ} (p : Fin r → Fin n) (hp : SafeTaggedTuple p)
    (a : Fin r → Fin 3) (i : Fin r) : Fin n :=
  ⟨(p i).val+(a i).val-1, by
    have h := hp.1 i
    have ha := (a i).isLt
    omega⟩

theorem shiftedTag_strictMono {n r : ℕ} (p : Fin r → Fin n) (hp : SafeTaggedTuple p)
    (a : Fin r → Fin 3) : StrictMono (shiftedTag p hp a) := by
  intro i j hij
  change (p i).val+(a i).val-1 < (p j).val+(a j).val-1
  have h := hp.2 i j hij
  have hi := hp.1 i
  have hj := hp.1 j
  have hai := (a i).isLt
  omega

def gapIncidence (r : ℕ) (i : Fin (r+1)) : ℕ :=
  Fin.cons (α := fun _ => ℕ) 0 (fun _ : Fin r => 1) i + Fin.snoc (α := fun _ => ℕ) (fun _ : Fin r => 1) 0 i

def shiftGapExtra {r : ℕ} (a : Fin r → Fin 3) (i : Fin (r+1)) : ℕ :=
  Fin.cons (α := fun _ => ℕ) 0 (fun h => 2-(a h).val) i + Fin.snoc (α := fun _ => ℕ) (fun h => (a h).val) 0 i

/-- Literal adjacent-gap allocation of the units used by a displacement.
Value zero means translate left, one leave fixed, two translate right. -/
def localShiftExtra {r : ℕ} (h : Fin r) (a : Fin 3) (i : Fin (r+1)) : ℕ :=
  (if i=h.castSucc then a.val else 0) + (if i=h.succ then 2-a.val else 0)

theorem sum_castSucc_indicator {r : ℕ} (f : Fin r → ℕ) (i : Fin (r+1)) :
    (∑ h, if i=h.castSucc then f h else 0) = Fin.snoc (α := fun _ => ℕ) f 0 i := by
  induction i using Fin.lastCases with
  | last => simp [eq_comm]
  | cast h => simp

theorem sum_succ_indicator {r : ℕ} (f : Fin r → ℕ) (i : Fin (r+1)) :
    (∑ h, if i=h.succ then f h else 0) = Fin.cons (α := fun _ => ℕ) 0 f i := by
  induction i using Fin.cases with
  | zero => simp [eq_comm]
  | succ h => simp

theorem shiftGapExtra_eq_sum {r : ℕ} (a : Fin r → Fin 3) (i : Fin (r+1)) :
    shiftGapExtra a i = ∑ h, localShiftExtra h (a h) i := by
  simp only [localShiftExtra,Finset.sum_add_distrib,sum_castSucc_indicator,
    sum_succ_indicator,shiftGapExtra]
  omega

theorem gapIncidence_le {n r : ℕ} (p : Fin r → Fin n) (hp : SafeTaggedTuple p)
    (i : Fin (r+1)) : gapIncidence r i ≤ tupleGap p i := by
  cases r with
  | zero =>
    have hi : i=0 := Fin.eq_zero i
    subst i
    simp [gapIncidence,Fin.snoc_zero]
  | succ r =>
    induction i using Fin.cases with
    | zero => simpa only [gapIncidence,Fin.cons_zero,zero_add,Fin.snoc_apply_zero,
        tupleGap_zero] using (hp.1 0).1
    | succ i =>
      induction i using Fin.lastCases with
      | last =>
        simp only [gapIncidence,Fin.succ_last,Fin.cons_last,Fin.snoc_last,add_zero,
          tupleGap_last]
        have h := (hp.1 (Fin.last r)).2
        omega
      | cast i =>
        simp only [gapIncidence,Fin.cons_succ]
        rw [Fin.succ_castSucc,Fin.snoc_castSucc]
        rw [← Fin.succ_castSucc,tupleGap_middle]
        have h := hp.2 i.castSucc i.succ (by simp)
        omega

/-- The exact geometric identity relating translated tag positions to
nonnegative binomial-gap lengths. -/
theorem tupleGap_shifted {n r : ℕ} (p : Fin r → Fin n) (hp : SafeTaggedTuple p)
    (a : Fin r → Fin 3) (i : Fin (r+1)) :
    tupleGap (shiftedTag p hp a) i =
      tupleGap p i - gapIncidence r i + shiftGapExtra a i := by
  cases r with
  | zero =>
    have hi : i=0 := Fin.eq_zero i
    subst i
    simp [tupleGap,tupleLower,tupleUpper,gapIncidence,shiftGapExtra,Fin.snoc_zero]
  | succ r =>
    induction i using Fin.cases with
    | zero =>
      simp only [tupleGap_zero,gapIncidence,shiftGapExtra,Fin.cons_zero,zero_add,
        Fin.snoc_apply_zero,shiftedTag]
      have h := (hp.1 0).1
      omega
    | succ i =>
      induction i using Fin.lastCases with
      | last =>
        simp only [gapIncidence,shiftGapExtra,Fin.succ_last,Fin.cons_last,
          Fin.snoc_last,add_zero,tupleGap_last,shiftedTag]
        have h := hp.1 (Fin.last r)
        have ha := (a (Fin.last r)).isLt
        omega
      | cast i =>
        simp only [gapIncidence,shiftGapExtra,Fin.cons_succ]
        rw [Fin.succ_castSucc,Fin.snoc_castSucc,Fin.snoc_castSucc]
        rw [← Fin.succ_castSucc,tupleGap_middle,tupleGap_middle]
        change (p i.succ).val+(a i.succ).val-1-((p i.castSucc).val+(a i.castSucc).val-1+1) = _
        have hi := hp.1 i.castSucc
        have hj := hp.1 i.succ
        have hij := hp.2 i.castSucc i.succ (by simp)
        have hai := (a i.castSucc).isLt
        have haj := (a i.succ).isLt
        omega


/-- Coefficients of the unchanged, centered first, and centered second
one-step positional operators. -/
def positionalWeight (k : GapDifference) (a : Fin 3) : ℝ :=
  match k with
  | .unchanged => if a=1 then 1 else 0
  | .first => if a=0 then -1/2 else if a=2 then 1/2 else 0
  | .second => if a=1 then -1 else 1/2

theorem localShift_factor {r : ℕ} (h : Fin r) (a : Fin 3) (p : ℝ) :
    tensorSeries (fun i => (biasedSeries 1 p)^localShiftExtra h a i) =
      coordinateSeriesHom h.castSucc (biasedSeries 1 p)^a.val *
        coordinateSeriesHom h.succ (biasedSeries 1 p)^(2-a.val) := by
  have hpow (u : IntSeries) (t : ℕ) (c i : Fin (r+1)) :
      u^(if i=c then t else 0) = (u^t)^(if i=c then 1 else 0) := by
    split <;> simp
  have he : (fun i => (biasedSeries 1 p)^localShiftExtra h a i) =
      (fun i => ((biasedSeries 1 p)^a.val)^(if i=h.castSucc then 1 else 0) *
        ((biasedSeries 1 p)^(2-a.val))^(if i=h.succ then 1 else 0)) := by
    funext i
    rw [localShiftExtra,pow_add,hpow _ _ h.castSucc i,hpow _ _ h.succ i]
  rw [he,tensorSeries_two_coordinates,map_pow,map_pow]

theorem gapOperator_positional_expansion {r : ℕ} (h : Fin r) (k : GapDifference)
    (p : ℝ) :
    gapOperator h k p = ∑ a : Fin 3, positionalWeight k a •
      tensorSeries (fun i => (biasedSeries 1 p)^localShiftExtra h a i) := by
  simp_rw [localShift_factor]
  rw [Fin.sum_univ_three]
  cases k <;> norm_num [positionalWeight,gapOperator,Fin.ext_iff]
  all_goals try simp only [two_mul,add_mul]
  all_goals module

/-- Literal centered differences of all rank kernels are coefficients of
the adjacent-gap operator product, with no formal negative trial lengths. -/
theorem shifted_gap_series_expansion {n r : ℕ} (p : Fin r → Fin n)
    (hp : SafeTaggedTuple p) (k : Fin r → GapDifference) (θ : ℝ) :
    (∑ a : Fin r → Fin 3, (∏ h, positionalWeight (k h) (a h)) •
      tensorSeries (fun i => biasedSeries (tupleGap (shiftedTag p hp a) i) θ)) =
    tensorSeries (fun i => biasedSeries (tupleGap p i-gapIncidence r i) θ) *
      ∏ h, gapOperator h (k h) θ := by
  classical
  simp_rw [gapOperator_positional_expansion]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.prod_smul,mul_smul_comm,← tensorSeries_prod,← tensorSeries_mul]
  congr 2
  funext i
  rw [tupleGap_shifted,shiftGapExtra_eq_sum]
  simp only [biasedSeries,pow_one,Finset.prod_pow_eq_pow_sum,pow_add]


/-- Simultaneous literal positional operators applied to the actual
conditional retained-subset kernel. -/
def positionalRankDifference {n l r : ℕ} (hl : l ≤ n) (p : Fin r → Fin n)
    (hp : SafeTaggedTuple p) (k : Fin r → GapDifference) (v : IncreasingTuple l r) : ℝ :=
  ∑ a : Fin r → Fin 3, (∏ h, positionalWeight (k h) (a h)) *
    subsetRankKernel hl (shiftedTag p hp a) v.val

theorem positionalRankDifference_expansion {n l r : ℕ} (hl : l ≤ n)
    (p : Fin r → Fin n) (hp : SafeTaggedTuple p) (k : Fin r → GapDifference)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 1) (v : IncreasingTuple l r) :
    positionalRankDifference hl p hp k v = θ^r / binomialMass n θ l *
      ∑ a : Fin r → Bool × Bool, (∏ h, gapTermWeight (k h) (a h)) *
        signedRankProduct (fun i => binomialLengthDifference
          (tupleGap p i-gapIncidence r i + ∑ h, gapTermExtra h (k h) (a h) i)
          (∑ h, gapTermOrder h (k h) (a h) i) θ) (fun _ => 0) v := by
  have h := shifted_gap_series_expansion p hp k θ
  rw [gapOperators_expansion] at h
  have hh := congrArg (fun f : AddMonoidAlgebra ℝ (Fin (r+1) → ℤ) =>
    f.coeff (fun i => (tupleGap v.val i:ℤ))) h
  simp only [AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_smul,Finsupp.smul_apply,smul_eq_mul,tensorSeries_coeff,
    biasedSeries_coeff_nat] at hh
  unfold positionalRankDifference
  simp_rw [subsetRankKernel_binomial_formula hl _ (shiftedTag_strictMono p hp _) _ v.property θ hθ]
  calc
    _ = θ^r / binomialMass n θ l *
        ∑ a : Fin r → Fin 3, (∏ h, positionalWeight (k h) (a h)) *
          ∏ i, binomialMass (tupleGap (shiftedTag p hp a) i) θ (tupleGap v.val i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by
      exact congrArg (fun t => θ^r / binomialMass n θ l * t) (by
        simpa only [signedRankProduct,sub_zero] using hh)

/-- The total derivative order is the source value |D|+2|V|. -/
theorem gap_global_order {r : ℕ} (k : Fin r → GapDifference) (a : Fin r → Bool × Bool) :
    (∑ i : Fin (r+1), ∑ h, gapTermOrder h (k h) (a h) i) = ∑ h, (k h).order := by
  rw [Finset.sum_comm]
  simp_rw [gapTermOrder_total]

end TraceReconstruction



noncomputable section
namespace TraceReconstruction

theorem gapTermOrder_sum_le_global {r : ℕ} (k : Fin r → GapDifference)
    (a : Fin r → Bool × Bool) (i : Fin (r+1)) :
    (∑ h, gapTermOrder h (k h) (a h) i) ≤ ∑ h, (k h).order := by
  rw [← gap_global_order k a]
  exact Finset.single_le_sum (f := fun j : Fin (r+1) => ∑ h, gapTermOrder h (k h) (a h) j)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- Literal mixed centered positional differences of a conditional rank
kernel, with a single explicit constant depending only on the total order
and the Bernoulli parameter. Every gap scale remains available for summing
over the period tuples in the signed initial construction. -/
theorem positionalRankDifference_square_sum_le {n l r : ℕ} (hl : l ≤ n)
    (p : Fin r → Fin n) (hp : SafeTaggedTuple p) (k : Fin r → GapDifference)
    {θ G : ℝ} (hθ : θ ∈ Set.Ioo 0 1) (hG : 0 < G)
    (hgap : ∀ i, G ≤ (tupleGap p i-gapIncidence r i : ℕ)+1)
    (e : Fin (r+1)) :
    (∑ v : IncreasingTuple l r, positionalRankDifference hl p hp k v ^ 2) ≤
      (θ^r / binomialMass n θ l)^2 * (2:ℝ)^(2*r) *
        (lengthDifferenceConstant (∑ h, (k h).order) θ)^(2*(∑ h, (k h).order)+r+2) /
      (G^(∑ h, (k h).order) * Real.sqrt ((tupleGap p e-gapIncidence r e:ℕ)+1) *
        ∏ i, Real.sqrt ((tupleGap p i-gapIncidence r i:ℕ)+1)) := by
  let d := ∑ h, (k h).order
  let C := lengthDifferenceConstant d θ
  let b (i : Fin (r+1)) := tupleGap p i-gapIncidence r i
  let B := C^(2*d+r+2) / (G^d*Real.sqrt ((b e:ℝ)+1)*∏ i,Real.sqrt ((b i:ℝ)+1))
  let c (a : Fin r → Bool × Bool) := ∏ h, gapTermWeight (k h) (a h)
  let F (a : Fin r → Bool × Bool) (v : IncreasingTuple l r) :=
    signedRankProduct (fun i => binomialLengthDifference
      (b i+∑ h, gapTermExtra h (k h) (a h) i)
      (∑ h, gapTermOrder h (k h) (a h) i) θ) (fun _ => 0) v
  have hC : 0 < C := lengthDifferenceConstant_pos d hθ
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hB (a : Fin r → Bool × Bool) : (∑ v, F a v^2) ≤ B := by
    have hd (i : Fin (r+1)) : lengthDifferenceConstant (∑ h, gapTermOrder h (k h) (a h) i) θ ≤ C :=
      lengthDifferenceConstant_mono (gapTermOrder_sum_le_global k a i) hθ
    have h := rank_derivatives_uniform (l := l)
      (fun i => b i+∑ h, gapTermExtra h (k h) (a h) i) b
      (fun i => ∑ h, gapTermOrder h (k h) (a h) i) (fun _ => 0)
      hθ hd hG (fun _ => Nat.le_add_right _ _) (by
        intro i
        exact (hgap i).trans (by exact_mod_cast Nat.add_le_add_right (Nat.le_add_right (b i) _) 1)) e
    simpa only [F,B,d,gap_global_order] using h
  have hmix := rank_mixture_square_sum_le c F (fun _ => B) hB
  have hM : (∑ a, |c a|) ≤ (2:ℝ)^r := gapOperators_weight_l1 k
  have hM0 : 0 ≤ ∑ a, |c a| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hmix' : (∑ v, (∑ a, c a*F a v)^2) ≤ (2:ℝ)^(2*r)*B := by
    refine hmix.trans ?_
    rw [← Finset.sum_mul,← mul_assoc]
    have hs : (∑ a, |c a|)^2 ≤ ((2:ℝ)^r)^2 := (sq_le_sq₀ hM0 (by positivity)).mpr hM
    calc
      _ = (∑ a, |c a|)^2*B := by ring
      _ ≤ ((2:ℝ)^r)^2*B := mul_le_mul_of_nonneg_right hs hB0
      _ = _ := by rw [← pow_mul,Nat.mul_comm r 2]
  simp_rw [positionalRankDifference_expansion hl p hp k hθ,mul_pow]
  rw [← Finset.mul_sum]
  calc
    _ ≤ (θ^r / binomialMass n θ l)^2 * ((2:ℝ)^(2*r)*B) :=
      mul_le_mul_of_nonneg_left hmix' (sq_nonneg _)
    _ = _ := by dsimp [B,C,d,b]; ring

end TraceReconstruction



noncomputable section
namespace TraceReconstruction

theorem gapIncidence_le_two (r : ℕ) (i : Fin (r+1)) : gapIncidence r i ≤ 2 := by
  have h₁ : Fin.cons (α := fun _ => ℕ) 0 (fun _ : Fin r => 1) i ≤ 1 := by
    induction i using Fin.cases <;> simp
  have h₂ : Fin.snoc (α := fun _ => ℕ) (fun _ : Fin r => 1) 0 i ≤ 1 := by
    induction i using Fin.lastCases <;> simp
  exact Nat.add_le_add h₁ h₂

/-- Constant middle-period tags admit every independent left/unchanged/right
choice without violating slot order or either end boundary. -/
theorem constant_period_safe {u m r : ℕ} (off : Fin m)
    (hoff₁ : 1 ≤ off.val) (hoff₂ : off.val+1 < m) (hm : 3 ≤ m)
    (j : Fin r → Fin u) (hj : StrictMono j) :
    SafeTaggedTuple (periodSlot (fun _ => off) ∘ j) := by
  constructor
  · intro i
    change 1 ≤ (j i).val*m+off.val ∧ (j i).val*m+off.val+1 < u*m
    constructor
    · omega
    · have h := Nat.mul_le_mul_right m (Nat.succ_le_of_lt (j i).isLt)
      rw [Nat.succ_mul] at h
      omega
  · intro i h hih
    change (j i).val*m+off.val+3 ≤ (j h).val*m+off.val
    have h := Nat.mul_le_mul_right m (Nat.succ_le_iff.mpr (hj hih))
    rw [Nat.succ_mul] at h
    omega

/-- Removing both incident displacement units still leaves a fixed
fraction of each actual coarse gap. Doubled coarse gaps are used to keep
all combinatorial labels integer-valued. -/
theorem period_derivative_base_lower {u m r : ℕ} (hm : 32 ≤ m) (hr : 0 < r)
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2)
    (j : Fin r → Fin u) (hj : StrictMono j)
    (hsafe : SafeTaggedTuple (periodSlot off ∘ j)) (i : Fin (r+1)) :
    (m:ℝ)*coarsePeriodGap j i/4 ≤
      ((tupleGap (periodSlot off ∘ j) i-gapIncidence r i:ℕ):ℝ)+1 := by
  have he := abs_le.mp (period_gap_rounding hr off hoff hdiff j hj i)
  have hs := gapIncidence_le (periodSlot off ∘ j) hsafe i
  have hs₂ : (gapIncidence r i:ℝ) ≤ 2 := by exact_mod_cast gapIncidence_le_two r i
  have hc : 1 ≤ (coarsePeriodGap j i:ℝ) := by exact_mod_cast coarsePeriodGap_pos j i
  have hm' : (32:ℝ) ≤ m := by exact_mod_cast hm
  rw [Nat.cast_sub hs]
  nlinarith

theorem period_derivative_common_lower {u m r : ℕ} (hm : 32 ≤ m) (hr : 0 < r)
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2)
    (j : Fin r → Fin u) (hj : StrictMono j)
    (hsafe : SafeTaggedTuple (periodSlot off ∘ j)) (i : Fin (r+1)) :
    (m:ℝ)/4 ≤ ((tupleGap (periodSlot off ∘ j) i-gapIncidence r i:ℕ):ℝ)+1 := by
  refine le_trans ?_ (period_derivative_base_lower hm hr off hoff hdiff j hj hsafe i)
  have hc : 1 ≤ (coarsePeriodGap j i:ℝ) := by exact_mod_cast coarsePeriodGap_pos j i
  nlinarith [show (0:ℝ) ≤ m by positivity]

/-- A largest coarse gap supplies the additional square-root improvement
coming from the fixed sum of the observed ranks. -/
theorem period_derivative_largest_lower {u m r : ℕ} (hm : 32 ≤ m) (hr : 0 < r)
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2)
    (j : Fin r → Fin u) (hj : StrictMono j)
    (hsafe : SafeTaggedTuple (periodSlot off ∘ j)) (e : Fin (r+1))
    (he : 2*u ≤ (r+1)*coarsePeriodGap j e) :
    (u:ℝ)*m/(2*(r+1:ℝ)) ≤
      ((tupleGap (periodSlot off ∘ j) e-gapIncidence r e:ℕ):ℝ)+1 := by
  refine le_trans ?_ (period_derivative_base_lower hm hr off hoff hdiff j hj hsafe e)
  have he' : 2*(u:ℝ) ≤ (r+1:ℝ)*coarsePeriodGap j e := by exact_mod_cast he
  apply (div_le_iff₀ (by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_right he' (show (0:ℝ) ≤ m by positivity)
  nlinarith only [hh]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction

theorem binomial_rank_normalization {n l r : ℕ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 1) (hl : l ≤ n)
    (hmean : (n:ℝ)*θ=l) (hv : 1 ≤ (n:ℝ)*θ*(1-θ)) :
    (θ^r/binomialMass n θ l)^2 ≤ 144*(n:ℝ) := by
  have hpow : (θ^r)^2 ≤ 1 := pow_le_one₀ (pow_nonneg hθ.1.le r) (pow_le_one₀ hθ.1.le hθ.2.le) 
  calc
    _ = (θ^r)^2*(binomialMass n θ l)⁻¹^2 := by rw [div_eq_mul_inv,mul_pow]
    _ ≤ (binomialMass n θ l)⁻¹^2 := mul_le_of_le_one_left (sq_nonneg _) hpow
    _ ≤ 144*((n:ℝ)*θ*(1-θ)) := binomialMass_mean_inverse_sq n l hθ hl hmean hv
    _ ≤ _ := by
      have h : θ*(1-θ) ≤ 1 := by nlinarith [sq_nonneg θ]
      have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ (n:ℝ) by positivity)
      nlinarith only [hh]

/-- The exact mean-count version, with arbitrary proven positive lower
scales for all gaps; no asymptotic or analytic estimate is assumed. -/
theorem positionalRankDifference_scale_bound {n l r : ℕ} (hl : l ≤ n)
    (p : Fin r → Fin n) (hp : SafeTaggedTuple p) (k : Fin r → GapDifference)
    {θ G H : ℝ} (hθ : θ ∈ Set.Ioo 0 1) (hG : 0 < G) (hH : 0 < H)
    (hmean : (n:ℝ)*θ=l) (hv : 1 ≤ (n:ℝ)*θ*(1-θ))
    (B : Fin (r+1) → ℝ) (hB : ∀ i, 0 < B i)
    (hgap : ∀ i, G ≤ (tupleGap p i-gapIncidence r i:ℕ)+1)
    (hscale : ∀ i, B i ≤ (tupleGap p i-gapIncidence r i:ℕ)+1)
    (e : Fin (r+1)) (hlarge : H ≤ Real.sqrt ((tupleGap p e-gapIncidence r e:ℕ)+1)) :
    (∑ v : IncreasingTuple l r, positionalRankDifference hl p hp k v ^ 2) ≤
      144*(n:ℝ)*(2:ℝ)^(2*r)*
        (lengthDifferenceConstant (∑ h, (k h).order) θ)^(2*(∑ h, (k h).order)+r+2) /
      (G^(∑ h, (k h).order)*H*∏ i, Real.sqrt (B i)) := by
  refine (positionalRankDifference_square_sum_le hl p hp k hθ hG hgap e).trans ?_
  have hC := (lengthDifferenceConstant_pos (∑ h, (k h).order) hθ).le
  apply div_le_div₀ (by positivity)
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (binomial_rank_normalization hθ hl hmean hv) (by positivity))
      (pow_nonneg hC _)
  · exact mul_pos (mul_pos (pow_pos hG _) hH)
      (Finset.prod_pos (fun i _ => Real.sqrt_pos.mpr (hB i)))
  · apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hlarge (by positivity)
    · exact Finset.prod_le_prod₀ (fun i _ => (Real.sqrt_nonneg (B i)))
        (fun i _ => Real.sqrt_le_sqrt (hscale i))
    · exact Finset.prod_nonneg (fun _ _ => Real.sqrt_nonneg _)
    · positivity

/-- Explicit source rank-difference prefactor. It depends on the period
count, slot length, derivative order and Bernoulli parameter, not the
selected period tuple. -/
def periodDifferencePrefactor (u m r d : ℕ) (θ : ℝ) : ℝ :=
  144*((u*m:ℕ):ℝ)*(2:ℝ)^(2*r)*(lengthDifferenceConstant d θ)^(2*d+r+2) /
    (((m:ℝ)/4)^d*Real.sqrt ((u:ℝ)*m/(2*(r+1:ℝ)))*
      (Real.sqrt ((m:ℝ)/4))^(r+1))

/-- The finite-difference estimate for actual translated tagged slots in
periodic words. The tuple dependence is exactly the product of inverse
square roots of its doubled coarse gaps. -/
theorem period_positionalRankDifference_bound {u m l r : ℕ}
    (hm : 32 ≤ m) (hr : 0 < r) (hl : l ≤ u*m)
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2)
    (j : IncreasingTuple u r) (hsafe : SafeTaggedTuple (periodSlot off ∘ j.val))
    (k : Fin r → GapDifference) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 1)
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ)) :
    (∑ v : IncreasingTuple l r,
      positionalRankDifference hl (periodSlot off ∘ j.val) hsafe k v ^ 2) ≤
      periodDifferencePrefactor u m r (∑ h, (k h).order) θ *
        ∏ i, (Real.sqrt (coarsePeriodGap j.val i))⁻¹ := by
  have hu : 0 < u := lt_of_le_of_lt (Nat.zero_le (j.val ⟨0,hr⟩).val) (j.val ⟨0,hr⟩).isLt
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hu0 : (0:ℝ) < u := by exact_mod_cast hu
  obtain ⟨e,he⟩ := exists_large_period_gap hr j
  have hb (i : Fin (r+1)) := period_derivative_base_lower hm hr off hoff hdiff j.val j.property hsafe i
  have hg (i : Fin (r+1)) := period_derivative_common_lower hm hr off hoff hdiff j.val j.property hsafe i
  have hc (i : Fin (r+1)) : (0:ℝ) < coarsePeriodGap j.val i := by exact_mod_cast coarsePeriodGap_pos j.val i
  have h := positionalRankDifference_scale_bound hl (periodSlot off ∘ j.val) hsafe k hθ
    (G := (m:ℝ)/4) (H := Real.sqrt ((u:ℝ)*m/(2*(r+1:ℝ)))) (by positivity) (by positivity)
    hmean hv (fun i => (m:ℝ)*coarsePeriodGap j.val i/4) (fun i => by positivity [hc i]) hg hb e
    (Real.sqrt_le_sqrt (period_derivative_largest_lower hm hr off hoff hdiff j.val j.property hsafe e he))
  refine h.trans_eq ?_
  have hs (i : Fin (r+1)) : Real.sqrt ((m:ℝ)*coarsePeriodGap j.val i/4) =
      Real.sqrt ((m:ℝ)/4)*Real.sqrt (coarsePeriodGap j.val i) := by
    rw [show (m:ℝ)*coarsePeriodGap j.val i/4=((m:ℝ)/4)*coarsePeriodGap j.val i by ring,
      Real.sqrt_mul (by positivity)]
  simp_rw [hs]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [periodDifferencePrefactor,Finset.prod_inv_distrib]
  ring

end TraceReconstruction

open Filter
open scoped Topology

noncomputable section
namespace TraceReconstruction

/-- Two independent exact sum constraints determine a missing coordinate on
 each side of a fixed cut. This is the second-gap elimination needed when
 a period label has been fixed. -/
theorem two_sums_determine {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset ι) {e d : ι} (he : e∈A) (hd : d∉A)
    (x y : ι → ℕ) (hA : ∑ i∈A, x i = ∑ i∈A, y i)
    (ht : ∑ i, x i = ∑ i, y i)
    (hxy : ∀ i, i≠e → i≠d → x i=y i) : x=y := by
  have hs : (∑ i∈A.erase e, x i) = ∑ i∈A.erase e, y i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_erase.mp hi
    apply hxy i hi'.1
    intro hid
    exact hd (hid ▸ hi'.2)
  have hxe : x e=y e := by
    have hx := Finset.sum_erase_add A x he
    have hy := Finset.sum_erase_add A y he
    omega
  have hs' : (∑ i∈Finset.univ.erase d, x i) = ∑ i∈Finset.univ.erase d, y i := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hie : i=e
    · simpa only [hie] using hxe
    · exact hxy i hie (Finset.mem_erase.mp hi).1
  have hxd : x d=y d := by
    have hx := Finset.sum_erase_add Finset.univ x (Finset.mem_univ d)
    have hy := Finset.sum_erase_add Finset.univ y (Finset.mem_univ d)
    omega
  funext i
  by_cases hie : i=e
  · simpa only [hie] using hxe
  by_cases hid : i=d
  · simpa only [hid] using hxd
  exact hxy i hie hid

abbrev RemainingCoordinates {ι : Type*} (e d : ι) := {i : ι // i≠e ∧ i≠d}

/-- Restricting an injective gap profile to all but the two eliminated
 coordinates is still injective on two fixed-sum fibers. -/
theorem two_sums_restrict_injective {α ι : Type*} [Fintype ι] [DecidableEq ι]
    {U L V : ℕ} (A : Finset ι) {e d : ι} (he : e∈A) (hd : d∉A)
    (p : α → ι → Fin (U+1)) (hp : Function.Injective p)
    (hA : ∀ a, ∑ i∈A, (p a i).val=L) (ht : ∀ a, ∑ i, (p a i).val=V) :
    Function.Injective (fun a => fun i : RemainingCoordinates e d => p a i.val) := by
  intro a b hab
  apply hp
  have hv : (fun i => (p a i).val) = (fun i => (p b i).val) := by
    apply two_sums_determine A he hd
    · rw [hA,hA]
    · rw [ht,ht]
    · intro i hie hid
      exact congrArg Fin.val (congrFun hab ⟨i,hie,hid⟩)
  funext i
  exact Fin.ext (congrFun hv i)

/-- Once the two coordinates are eliminated all remaining gap weights sum
 independently; any additional constraints may be dropped. -/
theorem two_sums_product_bound {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    {U L V : ℕ} (A : Finset ι) {e d : ι} (he : e∈A) (hd : d∉A)
    (p : α → ι → Fin (U+1)) (hp : Function.Injective p)
    (hA : ∀ a, ∑ i∈A, (p a i).val=L) (ht : ∀ a, ∑ i, (p a i).val=V)
    (w : ι → Fin (U+1) → ℝ) (hw : ∀ i k, 0≤w i k) :
    (∑ a, ∏ i : RemainingCoordinates e d, w i.val (p a i.val)) ≤
      ∏ i : RemainingCoordinates e d, ∑ k, w i.val k := by
  classical
  have hh := sum_injective_profile_le
    (fun a => fun i : RemainingCoordinates e d => p a i.val)
    (two_sums_restrict_injective A he hd p hp hA ht)
    (fun _ => True) (fun _ => trivial)
    (fun δ => ∏ i : RemainingCoordinates e d, w i.val (δ i))
    (fun δ => Finset.prod_nonneg (fun i _ => hw i.val (δ i)))
  simp only [ite_true] at hh
  exact hh.trans_eq (by rw [Finset.prod_univ_sum]; simp only [Fintype.piFinset_univ])

/-- The sum of doubled coarse gaps to a specified period label is exact,
 including the half endpoint cells in the source convention. -/
theorem coarsePeriodGap_prefix {u r : ℕ} (j : Fin r → Fin u) (hj : StrictMono j)
    (i : Fin r) : (∑ g∈Finset.Iic i.castSucc, coarsePeriodGap j g) = 2*(j i).val+1 := by
  classical
  have hg := tupleGap_prefix j hj i
  have hz : (0 : Fin (r+1)) ∈ Finset.Iic i.castSucc := by simp
  have hl : ∀ g∈Finset.Iic i.castSucc, g≠Fin.last r := by
    intro g hg he
    have hle := Finset.mem_Iic.mp hg
    have hval : g.val ≤ i.val := hle
    have he' := congrArg Fin.val he
    simp only [Fin.val_last] at he'
    omega
  have hc : (∑ g∈Finset.Iic i.castSucc,
      if g=0 ∨ g=Fin.last r then 1 else 2) = 2*i.val+1 := by
    have hsub : (∑ g∈(Finset.Iic i.castSucc).erase 0,
        if g=0 ∨ g=Fin.last r then 1 else 2) = 2*i.val := by
      have hc : ((Finset.Iic i.castSucc).erase 0).card = i.val := by
        rw [Finset.card_erase_of_mem hz,Fin.card_Iic]
        simp
      calc
        _ = ∑ _g∈(Finset.Iic i.castSucc).erase 0, 2 := by
          apply Finset.sum_congr rfl
          intro g hg
          rw [ite_eq_right (not_or.mpr ⟨(Finset.mem_erase.mp hg).1,
            hl g (Finset.mem_erase.mp hg).2⟩)]
        _ = _ := by simp [hc,Nat.mul_comm]
    have hsum := Finset.sum_erase_add (Finset.Iic i.castSucc)
      (fun g => if g=0 ∨ g=Fin.last r then 1 else 2) hz
    rw [hsub] at hsum
    simpa using hsum.symm
  simp only [coarsePeriodGap,Finset.sum_add_distrib,← Finset.mul_sum]
  omega

/-- The full inverse-square-root sum, including the zero cell (whose
 value is zero), has the same elementary integral bound. -/
theorem fin_sum_inverse_sqrt (U : ℕ) :
    (∑ k : Fin (U+1), (Real.sqrt (k.val:ℝ))⁻¹) ≤ 2*Real.sqrt U := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.cast_zero, Real.sqrt_zero, inv_zero,zero_add,Fin.val_succ]
  have h := sum_inverse_sqrt U
  rw [Finset.sum_range] at h
  simpa only [Nat.cast_add,Nat.cast_one] using h

theorem prod_two_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    {e d : ι} (hed : e≠d) (f : ι → ℝ) :
    (∏ i, f i) = f e*f d*∏ i : RemainingCoordinates e d, f i.val := by
  have hd : d∈Finset.univ.erase e := by simp [hed.symm]
  have h1 := Finset.prod_erase_mul Finset.univ f (Finset.mem_univ e)
  have h2 := Finset.prod_erase_mul (Finset.univ.erase e) f hd
  have hrem : (∏ i∈(Finset.univ.erase e).erase d, f i) =
      ∏ i : RemainingCoordinates e d, f i.val :=
    Finset.prod_subtype _ (by intro i; simp [and_comm]) f
  rw [← h1,← h2,hrem]
  ring

theorem inverse_sqrt_pair {x y R : ℝ} (hR : 0<R) (hx : R≤x) (hy : R≤y) :
    (Real.sqrt x)⁻¹*(Real.sqrt y)⁻¹ ≤ R⁻¹ := by
  have hs : 0<Real.sqrt R := Real.sqrt_pos.mpr hR
  have hix := (inv_le_inv₀ (hs.trans_le (Real.sqrt_le_sqrt hx)) hs).mpr (Real.sqrt_le_sqrt hx)
  have hiy := (inv_le_inv₀ (hs.trans_le (Real.sqrt_le_sqrt hy)) hs).mpr (Real.sqrt_le_sqrt hy)
  calc
    _ ≤ (Real.sqrt R)⁻¹*(Real.sqrt R)⁻¹ := mul_le_mul hix hiy (by positivity) (by positivity)
    _ = _ := by rw [← mul_inv,Real.mul_self_sqrt hR.le]

/-- Explicit two-gap summation on a fixed-sum fiber. Both large gaps
 contribute R^(-1), rather than losing a free label factor. -/
theorem two_large_gaps_inverse_sum {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    {U L V : ℕ} (A : Finset ι) {e d : ι} (he : e∈A) (hd : d∉A)
    (p : α → ι → Fin (U+1)) (hp : Function.Injective p)
    (hA : ∀ a, ∑ i∈A, (p a i).val=L) (ht : ∀ a, ∑ i, (p a i).val=V)
    {R : ℝ} (hR : 0<R) (heR : ∀ a, R≤(p a e).val) (hdR : ∀ a, R≤(p a d).val) :
    (∑ a, ∏ i, (Real.sqrt ((p a i).val:ℝ))⁻¹) ≤
      R⁻¹*(2*Real.sqrt U)^Fintype.card (RemainingCoordinates e d) := by
  classical
  have hed : e≠d := by intro h; exact hd (h ▸ he)
  have hpoint (a) := inverse_sqrt_pair hR (heR a) (hdR a)
  calc
    _ ≤ ∑ a, R⁻¹*∏ i : RemainingCoordinates e d, (Real.sqrt ((p a i.val).val:ℝ))⁻¹ := by
      apply Finset.sum_le_sum
      intro a _
      rw [prod_two_coordinates hed]
      exact mul_le_mul_of_nonneg_right (hpoint a) (by positivity)
    _ = R⁻¹*∑ a, ∏ i : RemainingCoordinates e d, (Real.sqrt ((p a i.val).val:ℝ))⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ R⁻¹*∏ _i : RemainingCoordinates e d, ∑ k : Fin (U+1), (Real.sqrt (k.val:ℝ))⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hR.le)
      exact two_sums_product_bound A he hd p hp hA ht
        (fun _ k => (Real.sqrt (k.val:ℝ))⁻¹) (fun _ _ => by positivity)
    _ ≤ R⁻¹*∏ _i : RemainingCoordinates e d, (2*Real.sqrt U) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hR.le)
      exact Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun _ _ => fin_sum_inverse_sqrt U)
    _ = _ := by simp

/-- The fixed involved label is a genuine geometric fiber, not an extra
 analytic hypothesis on the rank kernel. -/
def FixedPeriodTuple (u r : ℕ) (a : Fin r) (h : Fin u) :=
  {j : IncreasingTuple u r // j.val a=h}

noncomputable instance fixedPeriodTupleFintype (u r : ℕ) (a : Fin r) (h : Fin u) :
    Fintype (FixedPeriodTuple u r a h) := by
  unfold FixedPeriodTuple
  exact Fintype.ofFinite _

def fixedPeriodProfile {u r : ℕ} (a : Fin r) (h : Fin u) (j : FixedPeriodTuple u r a h) :
    Fin (r+1) → Fin (2*u+1) := fun i =>
  ⟨coarsePeriodGap j.val.val i, Nat.lt_succ_of_le
    (coarsePeriodGap_le (Nat.zero_lt_of_lt a.isLt) j.val.val j.val.property i)⟩

theorem fixedPeriodProfile_injective {u r : ℕ} (a : Fin r) (h : Fin u) :
    Function.Injective (fixedPeriodProfile a h) := by
  intro j k hjk
  apply Subtype.ext
  apply Subtype.ext
  apply coarsePeriodGap_injective j.val.property k.val.property
  funext i
  exact congrArg Fin.val (congrFun hjk i)

theorem fixedPeriodProfile_prefix {u r : ℕ} (a : Fin r) (h : Fin u)
    (j : FixedPeriodTuple u r a h) :
    (∑ i∈Finset.Iic a.castSucc, (fixedPeriodProfile a h j i).val)=2*h.val+1 := by
  change (∑ i∈Finset.Iic a.castSucc, coarsePeriodGap j.val.val i)=_
  rw [coarsePeriodGap_prefix _ j.val.property,j.property]

theorem fixedPeriodProfile_total {u r : ℕ} (a : Fin r) (h : Fin u)
    (j : FixedPeriodTuple u r a h) :
    (∑ i, (fixedPeriodProfile a h j i).val)=2*u :=
  coarsePeriodGap_sum (Nat.zero_lt_of_lt a.isLt) j.val.val j.val.property

end TraceReconstruction
noncomputable section
namespace TraceReconstruction

/-- An elementary centered MGF bound valid on both sides of the mean,
 with constants independent of the Bernoulli parameter. -/
theorem binomialMass_centered_mgf (n : ℕ) {p t : ℝ}
    (hp : p∈Set.Icc 0 1) (ht : |t|≤1) :
    (∑ k∈Finset.range (n+1), binomialMass n p k*Real.exp (t*((k:ℝ)-n*p))) ≤
      Real.exp ((n:ℝ)*t^2) := by
  have he := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le ht)).2
  have hn : 0≤(n:ℝ)*p := mul_nonneg (Nat.cast_nonneg _) hp.1
  have hn' : (n:ℝ)*p≤n := mul_le_of_le_one_right (Nat.cast_nonneg _) hp.2
  calc
    _ = Real.exp (-t*(n:ℝ)*p)*
        ∑ k∈Finset.range (n+1), binomialMass n p k*Real.exp (t*k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_left_comm,← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-t*(n:ℝ)*p)*Real.exp ((n:ℝ)*p*(Real.exp t-1)) :=
      mul_le_mul_of_nonneg_left (binomialMass_mgf_le n hp t) (Real.exp_nonneg _)
    _ ≤ Real.exp ((n:ℝ)*t^2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have he' := mul_le_mul_of_nonneg_left he hn
      have hs := mul_le_mul_of_nonneg_right hn' (sq_nonneg t)
      nlinarith only [he',hs]

/-- Either signed deviation has the same Chernoff estimate. -/
theorem binomialMass_signed_tail (n : ℕ) {p t a ε : ℝ}
    (hp : p∈Set.Icc 0 1) (ht : t∈Set.Icc 0 1) (hε : ε=1 ∨ ε= -1) :
    (∑ k∈(Finset.range (n+1)).filter (fun k : ℕ => a≤ε*((k:ℝ)-n*p)), binomialMass n p k) ≤
      Real.exp (-t*a+(n:ℝ)*t^2) := by
  have heps : |t*ε|≤1 := by rcases hε with rfl | rfl <;> simpa [abs_of_nonneg ht.1] using ht.2
  have hm := finite_exp_markov (Finset.range (n+1)) (binomialMass n p)
    (fun k : ℕ => ε*((k:ℝ)-n*p)) (fun k _ => binomialMass_nonneg n k hp) a t ht.1
  calc
    _ ≤ Real.exp (-t*a)*∑ k∈Finset.range (n+1),
        binomialMass n p k*Real.exp ((t*ε)*((k:ℝ)-n*p)) := by
      simpa only [mul_assoc] using hm
    _ ≤ Real.exp (-t*a)*Real.exp ((n:ℝ)*(t*ε)^2) :=
      mul_le_mul_of_nonneg_left (binomialMass_centered_mgf n hp heps) (Real.exp_nonneg _)
    _ = _ := by rcases hε with rfl | rfl <;> simp [Real.exp_add]

/-- A uniform two-sided tail at any finite cutoff. Unlike a quoted
 concentration theorem, this follows here from the finite binomial MGF. -/
theorem binomialMass_abs_tail (n : ℕ) {p t a : ℝ}
    (hp : p∈Set.Icc 0 1) (ht : t∈Set.Icc 0 1) :
    (∑ k∈(Finset.range (n+1)).filter (fun k : ℕ => a≤|(k:ℝ)-n*p|), binomialMass n p k) ≤
      2*Real.exp (-t*a+(n:ℝ)*t^2) := by
  have hpoint (k : ℕ) : (if a≤|(k:ℝ)-n*p| then binomialMass n p k else 0) ≤
      (if a≤(k:ℝ)-n*p then binomialMass n p k else 0)+
      (if a≤-((k:ℝ)-n*p) then binomialMass n p k else 0) := by
    have hn := binomialMass_nonneg n k hp
    by_cases h : a≤|(k:ℝ)-n*p|
    · rw [ite_eq_left h]
      have hh := le_abs.mp h
      rcases hh with h1 | h2
      · rw [ite_eq_left h1]
        split_ifs <;> linarith
      · rw [ite_eq_left h2]
        split_ifs <;> linarith
    · rw [ite_eq_right h]
      split_ifs <;> linarith
  have hh := Finset.sum_le_sum (s := Finset.range (n+1)) (fun k _ => hpoint k)
  rw [Finset.sum_add_distrib,← Finset.sum_filter,← Finset.sum_filter,← Finset.sum_filter] at hh
  have h1 := binomialMass_signed_tail n (a:=a) hp ht (Or.inl rfl : (1:ℝ)=1 ∨ (1:ℝ)= -1)
  have h2 := binomialMass_signed_tail n (a:=a) hp ht (Or.inr rfl : (-1:ℝ)=1 ∨ (-1:ℝ)= -1)
  simp only [one_mul,neg_one_mul] at h1 h2
  linarith

end TraceReconstruction
noncomputable section
namespace TraceReconstruction

/-- Cardinality bookkeeping for the two eliminated gap coordinates. -/
theorem remainingCoordinates_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    {e d : ι} (hed : e≠d) :
    Fintype.card (RemainingCoordinates e d)=Fintype.card ι-2 := by
  classical
  have hset : (Finset.univ.filter (fun i : ι => i≠e ∧ i≠d)) = (Finset.univ.erase e).erase d := by
    ext i
    simp [and_comm]
  rw [Fintype.card_subtype, hset]
  rw [Finset.card_erase_of_mem (by simp [hed.symm]),
    Finset.card_erase_of_mem (Finset.mem_univ e)]
  simp only [Finset.card_univ]
  omega

/-- A finite sum's largest entry on a nonempty set controls its average,
 with the full number of coordinates in place of the subset cardinality. -/
theorem exists_large_in_subset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset ι) (hA : A.Nonempty) (x : ι → ℝ) (hx : ∀ i, 0≤x i)
    {R : ℝ} (hR : R*Fintype.card ι ≤ ∑ i∈A, x i) :
    ∃ e∈A, R≤x e := by
  obtain ⟨e,he,hm⟩ := A.exists_max_image x hA
  refine ⟨e,he,?_⟩
  have hc : (A.card:ℝ)≤Fintype.card ι := by exact_mod_cast Finset.card_le_univ A
  have hcard : (0:ℝ)<Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨e⟩
  have hs : (∑ i∈A, x i) ≤ (Fintype.card ι:ℝ)*x e := by
    calc
      _ ≤ ∑ _i∈A, x e := Finset.sum_le_sum (fun i hi => hm i hi)
      _ = (A.card:ℝ)*x e := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (hx e)
  nlinarith

/-- Covering the fixed-sum profile by its selected largest coordinates
 costs only the square of its (fixed) dimension. -/
theorem two_sided_large_gaps_sum {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    {U L V : ℕ} (A : Finset ι)
    (p : α → ι → Fin (U+1)) (hp : Function.Injective p)
    (hA : ∀ a, ∑ i∈A, (p a i).val=L) (ht : ∀ a, ∑ i, (p a i).val=V)
    {R : ℝ} (hR : 0<R)
    (hleft : ∀ a, ∃ e∈A, R≤(p a e).val)
    (hright : ∀ a, ∃ d∉A, R≤(p a d).val) :
    (∑ a, ∏ i, (Real.sqrt ((p a i).val:ℝ))⁻¹) ≤
      (Fintype.card ι:ℝ)^2*R⁻¹*(2*Real.sqrt U)^(Fintype.card ι-2) := by
  classical
  choose e he heR using hleft
  choose d hd hdR using hright
  let f (a : α) := (e a,d a)
  let W (a : α) := ∏ i, (Real.sqrt ((p a i).val:ℝ))⁻¹
  have hfiber (z : ι × ι) :
      (∑ a : {a // f a=z}, W a.val) ≤ R⁻¹*(2*Real.sqrt U)^(Fintype.card ι-2) := by
    by_cases hne : Nonempty {a // f a=z}
    · obtain ⟨a⟩ := hne
      have ha := congrArg Prod.fst a.property
      have ha' := congrArg Prod.snd a.property
      have hz1 : z.1∈A := by simpa only [f] using ha ▸ he a.val
      have hz2 : z.2∉A := by simpa only [f] using ha' ▸ hd a.val
      have hzd : z.1≠z.2 := by intro h; exact hz2 (h ▸ hz1)
      have hh := two_large_gaps_inverse_sum A hz1 hz2
        (fun a : {a // f a=z} => p a.val) (hp.comp Subtype.val_injective)
        (fun a => hA a.val) (fun a => ht a.val) hR
        (fun a => by have h := congrArg Prod.fst a.property; simpa only [f] using h ▸ heR a.val)
        (fun a => by have h := congrArg Prod.snd a.property; simpa only [f] using h ▸ hdR a.val)
      simpa only [W,remainingCoordinates_card hzd] using hh
    · have : IsEmpty {a // f a=z} := not_nonempty_iff.mp hne
      simp only [Fintype.sum_empty]
      positivity
  calc
    _ = ∑ z : ι × ι, ∑ a : {a // f a=z}, W a.val := by
      exact (Fintype.sum_fiberwise f W).symm
    _ ≤ ∑ _z : ι × ι, R⁻¹*(2*Real.sqrt U)^(Fintype.card ι-2) :=
      Finset.sum_le_sum (fun z _ => hfiber z)
    _ = _ := by simp [pow_two,mul_assoc]

/-- The fixed central label leaves a macroscopic sum on both sides. -/
theorem fixedPeriodProfile_central_sum {u r : ℕ} (a : Fin r) (h : Fin u)
    (hleft : (u:ℝ)/3≤2*h.val+1)
    (hright : (u:ℝ)/3≤2*u-(2*h.val+1)) :
    (∑ j : FixedPeriodTuple u r a h,
      ∏ i, (Real.sqrt (coarsePeriodGap j.val.val i))⁻¹) ≤
      ((r+1:ℕ):ℝ)^2 * ((u:ℝ)/(3*(r+1:ℝ)))⁻¹ *
        (2*Real.sqrt (2*u:ℕ))^(r-1) := by
  classical
  have hu : (0:ℝ)<u := by exact_mod_cast (Nat.zero_lt_of_lt h.isLt)
  let A := Finset.Iic a.castSucc
  let p := fixedPeriodProfile a h
  have hR : 0<(u:ℝ)/(3*(r+1:ℝ)) := by positivity
  have hL (j : FixedPeriodTuple u r a h) :
      ∃ e∈A, (u:ℝ)/(3*(r+1:ℝ))≤(p j e).val := by
    apply exists_large_in_subset A ⟨0, by simp [A]⟩ (fun i => (p j i).val)
      (fun _ => Nat.cast_nonneg _)
    have hs := fixedPeriodProfile_prefix a h j
    have hs' : (∑ i∈A, ((p j i).val:ℝ))=2*h.val+1 := by exact_mod_cast hs
    rw [hs']
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    convert hleft using 1; field_simp
  have hD (j : FixedPeriodTuple u r a h) :
      ∃ d∉A, (u:ℝ)/(3*(r+1:ℝ))≤(p j d).val := by
    have ha : a.val<r := a.isLt
    have hlast : Fin.last r∈Aᶜ := by simp [A]
    obtain ⟨d,hd,hdR⟩ := exists_large_in_subset Aᶜ ⟨Fin.last r,hlast⟩
      (fun i => ((p j i).val:ℝ)) (fun _ => Nat.cast_nonneg _) (R := (u:ℝ)/(3*(r+1:ℝ))) (by
        have hs := fixedPeriodProfile_prefix a h j
        have ht := fixedPeriodProfile_total a h j
        have hs' : (∑ i∈A, ((p j i).val:ℝ))=2*h.val+1 := by exact_mod_cast hs
        have ht' : (∑ i, ((p j i).val:ℝ))=2*u := by exact_mod_cast ht
        have hc := Finset.sum_compl_add_sum A (fun i => ((p j i).val:ℝ))
        have hsum : (∑ i∈Aᶜ, ((p j i).val:ℝ))=2*u-(2*h.val+1) := by linarith
        rw [hsum]
        simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
        convert hright using 1; field_simp)
    exact ⟨d,Finset.mem_compl.mp hd,hdR⟩
  have hh := two_sided_large_gaps_sum A p (fixedPeriodProfile_injective a h)
    (fixedPeriodProfile_prefix a h) (fixedPeriodProfile_total a h) hR hL hD
  simpa only [p,fixedPeriodProfile,Fin.val_mk,Fintype.card_fin,show r+1-2=r-1 by omega] using hh

end TraceReconstruction


noncomputable section
namespace TraceReconstruction

/-- Any finite cutoff only removes nonnegative mass from the full binomial
 support, even if the cutoff extends beyond that support. -/
theorem binomialMass_cutoff_filter_le (n U : ℕ) {p : ℝ} (hp : p∈Set.Icc 0 1)
    (P : ℕ → Prop) [DecidablePred P] :
    (∑ k : Fin (U+1), if P k.val then binomialMass n p k.val else 0) ≤
      ∑ k∈(Finset.range (n+1)).filter P, binomialMass n p k := by
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if P k then binomialMass n p k else 0) (U+1),Finset.sum_filter]
  by_cases hU : U≤n
  · apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    intro k _ _
    split_ifs
    · exact binomialMass_nonneg n k hp
    · rfl
  · apply le_of_eq
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro k _ hk
    have hnk : n<k := by simp only [Finset.mem_range] at hk; omega
    simp [binomialMass,Nat.choose_eq_zero_of_lt hnk]

/-- A single-coordinate event for any injective family of profiles is
 bounded by the corresponding full product marginal. -/
theorem profile_coordinate_event_le {α ι κ : Type*} [Fintype α] [Fintype ι] [Fintype κ]
    [DecidableEq ι] (p : α → ι → κ) (hp : Function.Injective p)
    (w : ι → κ → ℝ) (hw : ∀ i k, 0≤w i k)
    (hs : ∀ i, ∑ k, w i k≤1) (e : ι) (P : κ → Prop) [DecidablePred P]
    {T : ℝ} (_hT : 0≤T) (ht : (∑ k, if P k then w e k else 0)≤T) :
    (∑ a, if P (p a e) then ∏ i, w i (p a i) else 0) ≤ T := by
  classical
  let w' (i : ι) (k : κ) := if i=e then (if P k then w i k else 0) else w i k
  have hw' (i k) : 0≤w' i k := by
    dsimp [w']
    split_ifs
    · exact hw i k
    · exact le_rfl
    · exact hw i k
  have hprod (δ : ι → κ) : (∏ i, w' i (δ i)) =
      if P (δ e) then ∏ i, w i (δ i) else 0 := by
    by_cases h : P (δ e)
    · rw [ite_eq_left h]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i=e
      · subst i; simp [w',h]
      · simp [w',hi]
    · rw [ite_eq_right h]
      exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp [w',h])
  have hsum (i) : (∑ k, w' i k)≤ if i=e then T else 1 := by
    by_cases hi : i=e
    · subst i; simpa only [w',ite_true] using ht
    · simpa only [w',ite_eq_right hi] using hs i
  calc
    _ = ∑ a, ∏ i, w' i (p a i) := by simp_rw [hprod]
    _ ≤ ∑ δ : ι → κ, ∏ i, w' i (δ i) := by
      have hh := sum_injective_profile_le p hp (fun _ => True) (fun _ => trivial)
        (fun δ => ∏ i, w' i (δ i)) (fun δ => Finset.prod_nonneg (fun i _ => hw' i (δ i)))
      simpa only [ite_true] using hh
    _ = ∏ i, ∑ k, w' i k := (Fintype.prod_sum _).symm
    _ ≤ ∏ i : ι, if i=e then T else 1 :=
      Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg (fun k _ => hw' i k)) (fun i _ => hsum i)
    _ = T := by simp

/-- Exponentially small clipping loss for a single gap of the actual
 conditional retained-subset rank kernel. -/
theorem subsetRankKernel_gap_tail {n l r : ℕ} (hl : l≤n)
    (p : Fin r → Fin n) (hp : StrictMono p) (e : Fin (r+1))
    {θ t a : ℝ} (hθ : θ∈Set.Ioo 0 1) (ht : t∈Set.Icc 0 1) :
    (∑ v : IncreasingTuple l r,
      if a≤|(tupleGap v.val e:ℝ)-(tupleGap p e:ℝ)*θ|
      then subsetRankKernel hl p v.val else 0) ≤
      θ^r / binomialMass n θ l *
        (2*Real.exp (-t*a+(tupleGap p e:ℝ)*t^2)) := by
  classical
  have hθ' : θ∈Set.Icc 0 1 := ⟨hθ.1.le,hθ.2.le⟩
  let prof := rankGapProfile (n := l) (r := r) (Equiv.refl _)
  let w (i : Fin (r+1)) (k : Fin (l-r+1)) := binomialMass (tupleGap p i) θ k.val
  have hw (i k) : 0≤w i k := binomialMass_nonneg _ _ hθ'
  have hs (i) : (∑ k, w i k)≤1 := by
    have hh := binomialMass_cutoff_filter_le (tupleGap p i) (l-r) hθ' (fun _ => True)
    simpa only [ite_true,Finset.filter_true,sum_binomialMass] using hh
  have ht' : (∑ k : Fin (l-r+1),
      if a≤|(k.val:ℝ)-(tupleGap p e:ℝ)*θ| then w e k else 0) ≤
      2*Real.exp (-t*a+(tupleGap p e:ℝ)*t^2) := by
    exact (binomialMass_cutoff_filter_le (tupleGap p e) (l-r) hθ'
      (fun k : ℕ => a≤|(k:ℝ)-(tupleGap p e:ℝ)*θ|)).trans
        (binomialMass_abs_tail _ hθ' ht)
  have hh := profile_coordinate_event_le prof (rankGapProfile_injective _) w hw hs e
    (fun k => a≤|(k.val:ℝ)-(tupleGap p e:ℝ)*θ|) (by positivity) ht'
  have hfac : 0≤θ^r / binomialMass n θ l :=
    div_nonneg (pow_nonneg hθ.1.le _) (binomialMass_nonneg _ _ hθ')
  calc
    _ = θ^r / binomialMass n θ l *
        ∑ v : IncreasingTuple l r,
          if a≤|(tupleGap v.val e:ℝ)-(tupleGap p e:ℝ)*θ|
          then ∏ i, binomialMass (tupleGap p i) θ (tupleGap v.val i) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      split_ifs
      · exact subsetRankKernel_binomial_formula hl p hp v.val v.property θ hθ
      · simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (by
      simpa only [prof,rankGapProfile,Equiv.refl_apply,w] using hh) hfac

/-- A coordinatewise rank region has a union-bound clipping estimate. -/
theorem subsetRankKernel_outside_region {n l r : ℕ} (hl : l≤n)
    (p : Fin r → Fin n) (hp : StrictMono p)
    {θ t a : ℝ} (hθ : θ∈Set.Ioo 0 1) (ht : t∈Set.Icc 0 1) :
    (∑ v : IncreasingTuple l r,
      if ∃ i, a≤|(tupleGap v.val i:ℝ)-(tupleGap p i:ℝ)*θ|
      then subsetRankKernel hl p v.val else 0) ≤
      ((r+1:ℕ):ℝ)*θ^r / binomialMass n θ l *
        (2*Real.exp (-t*a+(n:ℝ)*t^2)) := by
  classical
  have hθ' : θ∈Set.Icc 0 1 := ⟨hθ.1.le,hθ.2.le⟩
  have hpoint (v : IncreasingTuple l r) :
      (if ∃ i, a≤|(tupleGap v.val i:ℝ)-(tupleGap p i:ℝ)*θ|
      then subsetRankKernel hl p v.val else 0) ≤
      ∑ i, if a≤|(tupleGap v.val i:ℝ)-(tupleGap p i:ℝ)*θ|
        then subsetRankKernel hl p v.val else 0 := by
    have hn (i) : 0≤(if a≤|(tupleGap v.val i:ℝ)-(tupleGap p i:ℝ)*θ|
        then subsetRankKernel hl p v.val else 0) := by
      split_ifs
      · exact subsetRankKernel_nonneg hl p v.val
      · rfl
    split_ifs with h
    · obtain ⟨e,he⟩ := h
      have hh := Finset.single_le_sum (fun i _ => hn i) (Finset.mem_univ e)
      simpa only [ite_eq_left he] using hh
    · exact Finset.sum_nonneg (fun i _ => hn i)
  calc
    _ ≤ ∑ v : IncreasingTuple l r, ∑ i,
        if a≤|(tupleGap v.val i:ℝ)-(tupleGap p i:ℝ)*θ|
        then subsetRankKernel hl p v.val else 0 := Finset.sum_le_sum (fun v _ => hpoint v)
    _ = ∑ i, ∑ v : IncreasingTuple l r,
        if a≤|(tupleGap v.val i:ℝ)-(tupleGap p i:ℝ)*θ|
        then subsetRankKernel hl p v.val else 0 := Finset.sum_comm
    _ ≤ ∑ _i : Fin (r+1), θ^r / binomialMass n θ l *
        (2*Real.exp (-t*a+(n:ℝ)*t^2)) := by
      apply Finset.sum_le_sum
      intro i _
      apply (subsetRankKernel_gap_tail hl p hp i hθ ht).trans
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (pow_nonneg hθ.1.le _) (binomialMass_nonneg _ _ hθ'))
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      have hgap : tupleGap p i≤n := (tupleGap_le_remainder ⟨p,hp⟩ i).trans (Nat.sub_le _ _)
      have hg : (tupleGap p i:ℝ)≤n := by exact_mod_cast hgap
      have hh := mul_le_mul_of_nonneg_right hg (sq_nonneg t)
      linarith
    _ = _ := by simp; ring

end TraceReconstruction


noncomputable section
namespace TraceReconstruction

/-- An inverse square root at an integer, extended by zero at zero,
 never exceeds one. -/
theorem inverse_sqrt_nat_le_one (k : ℕ) : (Real.sqrt (k:ℝ))⁻¹≤1 := by
  by_cases hk : k=0
  · simp [hk]
  have hk' : (1:ℝ)≤k := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
  have hs : 1≤Real.sqrt (k:ℝ) := by simpa using Real.sqrt_le_sqrt hk'
  exact (inv_le_one₀ (by positivity : 0<Real.sqrt (k:ℝ))).mpr hs

/-- A bounded gap costs a constant depending only on that bound, rather
 than an additional square root of the ambient period count. -/
theorem fin_bounded_inverse_sqrt (U M : ℕ) :
    (∑ k : Fin (U+1), if k.val≤M then (Real.sqrt (k.val:ℝ))⁻¹ else 0) ≤ M+1 := by
  classical
  calc
    _ ≤ ∑ k : Fin (U+1), if k.val≤M then (1:ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro k _
      split_ifs
      · exact inverse_sqrt_nat_le_one k.val
      · rfl
    _ = ((Finset.univ.filter (fun k : Fin (U+1) => k.val≤M)).card:ℝ) := by simp
    _ ≤ M+1 := by
      have hh : (Finset.univ.filter (fun k : Fin (U+1) => k.val≤M)).card≤M+1 := by
        rw [← Finset.card_range (M+1)]
        apply Finset.card_le_card_of_injOn Fin.val
          (fun k hk => by
            have hh := (Finset.mem_filter.mp hk).2
            exact Finset.mem_range.mpr (Nat.lt_succ_of_le hh))
        intro k _ j _ hkj; exact Fin.ext hkj
      exact_mod_cast hh

theorem prod_one_special {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι) (A B : ℝ) :
    (∏ i : ι, if i=e then A else B)=A*B^(Fintype.card ι-1) := by
  rw [← Finset.mul_prod_erase Finset.univ (fun i => if i=e then A else B) (Finset.mem_univ e)]
  simp only [ite_true]
  have hh : (∏ i∈Finset.univ.erase e, if i=e then A else B)=
      ∏ _i∈Finset.univ.erase e, B := by
    apply Finset.prod_congr rfl
    intro i hi
    exact ite_eq_right (Finset.mem_erase.mp hi).1
  rw [hh]
  simp

/-- Refined two-gap elimination when a third gap has bounded size. -/
theorem two_large_bounded_gap_sum {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    {U L V M : ℕ} (A : Finset ι) {e d c : ι} (he : e∈A) (hd : d∉A)
    (hce : c≠e) (hcd : c≠d)
    (p : α → ι → Fin (U+1)) (hp : Function.Injective p)
    (hA : ∀ a, ∑ i∈A, (p a i).val=L) (ht : ∀ a, ∑ i, (p a i).val=V)
    {R : ℝ} (hR : 0<R) (heR : ∀ a, R≤(p a e).val) (hdR : ∀ a, R≤(p a d).val)
    (hcM : ∀ a, (p a c).val≤M) :
    (∑ a, ∏ i, (Real.sqrt ((p a i).val:ℝ))⁻¹) ≤
      R⁻¹*(M+1)*(2*Real.sqrt U)^(Fintype.card ι-3) := by
  classical
  have hed : e≠d := by intro h; exact hd (h ▸ he)
  let c' : RemainingCoordinates e d := ⟨c,hce,hcd⟩
  let w (i : ι) (k : Fin (U+1)) :=
    if i=c then (if k.val≤M then (Real.sqrt (k.val:ℝ))⁻¹ else 0)
    else (Real.sqrt (k.val:ℝ))⁻¹
  have hw (i k) : 0≤w i k := by dsimp [w]; split_ifs <;> positivity
  have hwP (a i) : w i (p a i)=(Real.sqrt ((p a i).val:ℝ))⁻¹ := by
    by_cases hi : i=c
    · subst i; simp only [w,ite_true,ite_eq_left (hcM a)]
    · simp only [w,ite_eq_right hi]
  have hwS (i : RemainingCoordinates e d) : (∑ k, w i.val k)≤
      if i=c' then (M+1:ℝ) else 2*Real.sqrt U := by
    by_cases hi : i=c'
    · subst i
      simpa only [c',w,ite_true] using fin_bounded_inverse_sqrt U M
    · have hic : i.val≠c := by intro h; apply hi; exact Subtype.ext h
      simpa only [w,ite_eq_right hi,ite_eq_right hic] using fin_sum_inverse_sqrt U
  calc
    _ ≤ ∑ a, R⁻¹*∏ i : RemainingCoordinates e d, w i.val (p a i.val) := by
      apply Finset.sum_le_sum
      intro a _
      simp_rw [hwP]
      rw [prod_two_coordinates hed]
      exact mul_le_mul_of_nonneg_right (inverse_sqrt_pair hR (heR a) (hdR a)) (by positivity)
    _ = R⁻¹*∑ a, ∏ i : RemainingCoordinates e d, w i.val (p a i.val) := by rw [Finset.mul_sum]
    _ ≤ R⁻¹*∏ i : RemainingCoordinates e d, ∑ k, w i.val k :=
      mul_le_mul_of_nonneg_left (two_sums_product_bound A he hd p hp hA ht w hw) (inv_nonneg.mpr hR.le)
    _ ≤ R⁻¹*∏ i : RemainingCoordinates e d, if i=c' then (M+1:ℝ) else 2*Real.sqrt U := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hR.le)
      exact Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg (fun k _ => hw i.val k)) (fun i _ => hwS i)
    _ = _ := by
      rw [prod_one_special,remainingCoordinates_card hed]
      simp only [Nat.sub_sub]
      ring

/-- A small internal gap cannot be either selected macroscopic gap.
 The bound retains the extra factor u^(-1/2) needed for nonlinear terms. -/
theorem two_sided_bounded_gaps_sum {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    {U L V M : ℕ} (A : Finset ι) (c : ι)
    (p : α → ι → Fin (U+1)) (hp : Function.Injective p)
    (hA : ∀ a, ∑ i∈A, (p a i).val=L) (ht : ∀ a, ∑ i, (p a i).val=V)
    {R : ℝ} (hR : 0<R) (hMR : (M:ℝ)<R)
    (hleft : ∀ a, ∃ e∈A, R≤(p a e).val)
    (hright : ∀ a, ∃ d∉A, R≤(p a d).val)
    (hcM : ∀ a, (p a c).val≤M) :
    (∑ a, ∏ i, (Real.sqrt ((p a i).val:ℝ))⁻¹) ≤
      (Fintype.card ι:ℝ)^2*R⁻¹*(M+1)*(2*Real.sqrt U)^(Fintype.card ι-3) := by
  classical
  choose e he heR using hleft
  choose d hd hdR using hright
  let f (a : α) := (e a,d a)
  let W (a : α) := ∏ i, (Real.sqrt ((p a i).val:ℝ))⁻¹
  have hfiber (z : ι × ι) :
      (∑ a : {a // f a=z}, W a.val) ≤ R⁻¹*(M+1)*(2*Real.sqrt U)^(Fintype.card ι-3) := by
    by_cases hne : Nonempty {a // f a=z}
    · obtain ⟨a⟩ := hne
      have ha := congrArg Prod.fst a.property
      have ha' := congrArg Prod.snd a.property
      have hz1 : z.1∈A := by simpa only [f] using ha ▸ he a.val
      have hz2 : z.2∉A := by simpa only [f] using ha' ▸ hd a.val
      have hzR : R≤(p a.val z.1).val := by simpa only [f] using ha ▸ heR a.val
      have hzR' : R≤(p a.val z.2).val := by simpa only [f] using ha' ▸ hdR a.val
      have hc : ((p a.val c).val:ℝ)≤M := by exact_mod_cast hcM a.val
      have hce : c≠z.1 := by intro h; rw [h] at hc; linarith
      have hcd : c≠z.2 := by intro h; rw [h] at hc; linarith
      exact two_large_bounded_gap_sum A hz1 hz2 hce hcd
        (fun a : {a // f a=z} => p a.val) (hp.comp Subtype.val_injective)
        (fun a => hA a.val) (fun a => ht a.val) hR
        (fun a => by have h := congrArg Prod.fst a.property; simpa only [f] using h ▸ heR a.val)
        (fun a => by have h := congrArg Prod.snd a.property; simpa only [f] using h ▸ hdR a.val)
        (fun a => hcM a.val)
    · have : IsEmpty {a // f a=z} := not_nonempty_iff.mp hne
      simp only [Fintype.sum_empty]
      positivity
  calc
    _ = ∑ z : ι × ι, ∑ a : {a // f a=z}, W a.val := (Fintype.sum_fiberwise f W).symm
    _ ≤ ∑ _z : ι × ι, R⁻¹*(M+1)*(2*Real.sqrt U)^(Fintype.card ι-3) :=
      Finset.sum_le_sum (fun z _ => hfiber z)
    _ = _ := by simp [pow_two,mul_assoc]

end TraceReconstruction


noncomputable section
open scoped Classical
namespace TraceReconstruction

/-- The literal rank-clipping rectangles used in the manuscript, with
 doubled coarse gaps to avoid half-integer natural indices. Only the
 first and internal gaps are needed to determine the period tuple. -/
def PeriodRankRegion {u l r : ℕ} (m : ℕ) (θ : ℝ)
    (j : IncreasingTuple u r) (v : IncreasingTuple l r) : Prop :=
  ∀ i : Fin r, |(tupleGap v.val i.castSucc:ℝ)-
    θ*m*(coarsePeriodGap j.val i.castSucc:ℝ)/2| < (m:ℝ)/8

/-- Enough accuracy to distinguish two integer gap lengths. -/
theorem nearby_gap_centers_equal {x y : ℕ} {z θ m : ℝ}
    (hθ : 1 / 2 ≤ θ) (hm : 0 < m)
    (hx : |z - θ * m * x / 2| < m / 8) (hy : |z - θ * m * y / 2| < m / 8) : x = y := by
  have hx' := abs_lt.mp hx
  have hy' := abs_lt.mp hy
  have hscale : m / 4 ≤ θ * m / 2 := by nlinarith
  by_contra hxy
  obtain h | h := lt_or_gt_of_ne hxy
  · have h' : (x:ℝ)+1≤y := by exact_mod_cast h
    have hh := mul_le_mul_of_nonneg_left h' (by positivity : 0 ≤ θ * m / 2)
    nlinarith
  · have h' : (y:ℝ)+1≤x := by exact_mod_cast h
    have hh := mul_le_mul_of_nonneg_left h' (by positivity : 0 ≤ θ * m / 2)
    nlinarith

/-- Regions for distinct tagged period tuples are genuinely disjoint,
 before any coefficient or orientation averaging. -/
theorem periodRankRegion_unique {u l r m : ℕ} (hm : 0 < m) {θ : ℝ} (hθ : 1 / 2 ≤ θ)
    {j k : IncreasingTuple u r} {v : IncreasingTuple l r}
    (hj : PeriodRankRegion m θ j v) (hk : PeriodRankRegion m θ k v) : j=k := by
  apply Subtype.ext
  by_cases hr : r=0
  · subst r; exact Subsingleton.elim _ _
  have hg (i : Fin r) : coarsePeriodGap j.val i.castSucc=coarsePeriodGap k.val i.castSucc :=
    nearby_gap_centers_equal hθ (by exact_mod_cast hm) (hj i) (hk i)
  have hsum := coarsePeriodGap_sum (Nat.pos_of_ne_zero hr) j.val j.property
  have hsum' := coarsePeriodGap_sum (Nat.pos_of_ne_zero hr) k.val k.property
  have hgSum : (∑ i : Fin r, coarsePeriodGap j.val i.castSucc)=
      ∑ i : Fin r, coarsePeriodGap k.val i.castSucc := Finset.sum_congr rfl (fun i _ => hg i)
  rw [Fin.sum_univ_castSucc] at hsum hsum'
  have hlast : coarsePeriodGap j.val (Fin.last r)=coarsePeriodGap k.val (Fin.last r) := by omega
  apply coarsePeriodGap_injective j.property k.property
  funext i
  refine Fin.lastCases hlast (fun i => hg i) i

/-- Orthogonality of a finite family with pointwise disjoint supports. -/
theorem disjoint_support_sum_sq {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) (hf : ∀ a b, a≠b → ∀ v, f a v*f b v=0) :
    (∑ v, (∑ a, f a v)^2) = ∑ a, ∑ v, f a v^2 := by
  classical
  have hp (v) : (∑ a, f a v)^2=∑ a, f a v^2 := by
    rw [pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    rw [Finset.sum_eq_single a]
    · ring
    · intro b _ hba
      exact hf a b hba.symm v
    · intro ha
      exact False.elim (ha (Finset.mem_univ a))
  simp_rw [hp]
  exact Finset.sum_comm

/-- Squared norm of the clipped sum is at most the sum of the original
 squared norms, with arbitrary signed multipliers on each tuple. -/
theorem period_clipped_square_sum {u l r m : ℕ} (hm : 0 < m) {θ : ℝ} (hθ : 1 / 2 ≤ θ)
    (W : IncreasingTuple u r → IncreasingTuple l r → ℝ)
    (a : IncreasingTuple u r → ℝ) :
    (∑ v, (∑ j, if PeriodRankRegion m θ j v then a j*W j v else 0)^2) ≤
      ∑ j, a j^2*∑ v, W j v^2 := by
  classical
  rw [disjoint_support_sum_sq _ (by
    intro j k hjk v
    by_cases hj : PeriodRankRegion m θ j v
    · have hk : ¬PeriodRankRegion m θ k v := fun hk => hjk (periodRankRegion_unique hm hθ hj hk)
      simp only [ite_eq_left hj,ite_eq_right hk,mul_zero]
    · simp only [ite_eq_right hj,zero_mul])]
  apply Finset.sum_le_sum
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  split_ifs
  · exact le_of_eq (mul_pow _ _ _)
  · simp only [zero_pow (by norm_num : 2 ≠ 0)]
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

instance : Fintype GapDifference :=
  ⟨{.unchanged,.first,.second}, by intro k; cases k <;> simp⟩

theorem sum_gapDifference (f : GapDifference → ℝ) :
    (∑ k, f k)=f .unchanged+f .first+f .second := by
  change (∑ k ∈ ({.unchanged,.first,.second} : Finset GapDifference), f k)=_
  simp [Finset.sum_insert]; ring

/-- The sign-dependent displacement in {-1,0,1}, represented by Fin 3. -/
def motifShift (χ β τ : ℝ) : Fin 3 :=
  if χ=0 then 1 else if β*τ=1 then 2 else 0

/-- Coefficients of 1 + χ V + τ β D. -/
def motifDifferenceWeight (χ β τ : ℝ) : GapDifference → ℝ
  | .unchanged => 1 | .first => τ*β | .second => χ

/-- The centered operator expansion is an exact displacement, not an
 approximation of the trace kernel. -/
theorem motif_positional_identity {χ β τ : ℝ} (hβ : IsMotifValue χ β)
    (hτ : IsTypeSign τ) (a : Fin 3) :
    (∑ k, motifDifferenceWeight χ β τ k * positionalWeight k a)=
      if a=motifShift χ β τ then 1 else 0 := by
  rw [sum_gapDifference]
  rcases hβ with ⟨rfl,rfl⟩ | ⟨rfl,rfl | rfl⟩ <;>
  rcases hτ with rfl | rfl <;> fin_cases a <;>
    norm_num [motifDifferenceWeight,motifShift,positionalWeight,Fin.ext_iff]

theorem product_function_delta {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (a b : ι → κ) :
    (∏ i, if a i=b i then (1:ℝ) else 0)=if a=b then 1 else 0 := by
  classical
  by_cases h : a=b
  · subst a; simp
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- Tensorization of the exact local shift identity, with an arbitrary
 array W (in particular any literal retained-subset rank kernel). -/
theorem motif_shift_expansion {r : ℕ} (χ β : Fin r → ℝ) (τ : ℝ)
    (hβ : ∀ h, IsMotifValue (χ h) (β h)) (hτ : IsTypeSign τ)
    (W : (Fin r → Fin 3) → ℝ) :
    W (fun h => motifShift (χ h) (β h) τ)=
      ∑ k : Fin r → GapDifference,
        (∏ h, motifDifferenceWeight (χ h) (β h) τ (k h))*
        (∑ a : Fin r → Fin 3, (∏ h, positionalWeight (k h) (a h))*W a) := by
  classical
  symm
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ a, (∑ k : Fin r → GapDifference,
        ∏ h, motifDifferenceWeight (χ h) (β h) τ (k h)*positionalWeight (k h) (a h))*W a := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.prod_mul_distrib]
      ring
    _ = ∑ a, (∏ h, if a h=motifShift (χ h) (β h) τ then (1:ℝ) else 0)*W a := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← Fintype.prod_sum (fun h k => motifDifferenceWeight (χ h) (β h) τ k * positionalWeight k (a h))]
      simp_rw [motif_positional_identity (hβ _) hτ]
    _ = _ := by simp_rw [product_function_delta]; simp

def firstDifferenceCount {r : ℕ} (k : Fin r → GapDifference) : ℕ :=
  (Finset.univ.filter fun h => k h = .first).card

def secondDifferenceCount {r : ℕ} (k : Fin r → GapDifference) : ℕ :=
  (Finset.univ.filter fun h => k h = .second).card

/-- Every factor of the hypothesis sign comes precisely from a D operator. -/
theorem motifDifferenceWeight_product {r : ℕ} (χ β : Fin r → ℝ) (τ : ℝ)
    (k : Fin r → GapDifference) :
    (∏ h, motifDifferenceWeight (χ h) (β h) τ (k h))=
      τ^firstDifferenceCount k *∏ h, motifDifferenceWeight (χ h) (β h) 1 (k h) := by
  classical
  have hw (h) : motifDifferenceWeight (χ h) (β h) τ (k h)=
      (if k h=.first then τ else 1)*motifDifferenceWeight (χ h) (β h) 1 (k h) := by
    cases k h <;> simp [motifDifferenceWeight]
  simp_rw [hw]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_filter]
  simp [firstDifferenceCount]

/-- The signed difference retains exactly the patterns having an odd
 number of centered first differences, with the source's factor two. -/
theorem motif_signed_shift_expansion {r : ℕ} (χ β : Fin r → ℝ)
    (hβ : ∀ h, IsMotifValue (χ h) (β h)) (W : (Fin r → Fin 3) → ℝ) :
    W (fun h => motifShift (χ h) (β h) 1)-
      W (fun h => motifShift (χ h) (β h) (-1))=
      ∑ k : Fin r → GapDifference,
        (if Odd (firstDifferenceCount k) then
          2*∏ h, motifDifferenceWeight (χ h) (β h) 1 (k h) else 0)*
        (∑ a : Fin r → Fin 3, (∏ h, positionalWeight (k h) (a h))*W a) := by
  rw [motif_shift_expansion χ β 1 hβ (Or.inl rfl) W,
    motif_shift_expansion χ β (-1) hβ (Or.inr rfl) W,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [motifDifferenceWeight_product χ β 1 k,motifDifferenceWeight_product χ β (-1) k]
  rw [sign_pow_parity (Or.inr rfl : IsTypeSign (-1))]
  simp only [one_pow,one_mul]
  split_ifs <;> ring

theorem difference_order_eq_counts {r : ℕ} (k : Fin r → GapDifference) :
    (∑ h, (k h).order)=firstDifferenceCount k+2*secondDifferenceCount k := by
  classical
  have hd (h) : (k h).order=(if k h=.first then 1 else 0)+
      2*(if k h=.second then 1 else 0) := by cases k h <;> simp [GapDifference.order]
  simp_rw [hd]
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  simp [firstDifferenceCount,secondDifferenceCount]

/-- The only signed pattern of order below three is the singleton D term. -/
theorem odd_pattern_linear_or_order_three {r : ℕ} (k : Fin r → GapDifference)
    (hk : Odd (firstDifferenceCount k)) :
    (firstDifferenceCount k=1 ∧ secondDifferenceCount k=0) ∨
      3≤∑ h, (k h).order := by
  rw [difference_order_eq_counts]
  obtain ⟨n,hn⟩ := hk
  omega

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem shiftGapExtra_le {r : ℕ} (a : Fin r → Fin 3) (i : Fin (r+1)) :
    shiftGapExtra a i  ≤  2*gapIncidence r i := by
  have hl : Fin.cons (α := fun _ =>  ℕ) 0 (fun h =>  2-(a h).val) i  ≤ 
      2*Fin.cons (α := fun _ =>  ℕ) 0 (fun _ : Fin r =>  1) i := by
    induction i using Fin.cases with
    | zero =>  simp
    | succ i =>  simp
  have hr : Fin.snoc (α := fun _ =>  ℕ) (fun h =>  (a h).val) 0 i  ≤ 
      2*Fin.snoc (α := fun _ =>  ℕ) (fun _ : Fin r =>  1) 0 i := by
    induction i using Fin.lastCases with
    | last =>  simp
    | cast i =>  simpa using Nat.le_of_lt_succ (a i).isLt
  dsimp [shiftGapExtra,gapIncidence]
  omega

/-- A unit positional shift changes each actual rank gap by at most two. -/
theorem tupleGap_shifted_close {n r : ℕ} (p : Fin r → Fin n)
    (hp : SafeTaggedTuple p) (a : Fin r → Fin 3) (i : Fin (r+1)) :
    |(tupleGap (shiftedTag p hp a) i:ℝ)-(tupleGap p i:ℝ)| ≤ 2 := by
  rw [tupleGap_shifted,Nat.cast_add,Nat.cast_sub (gapIncidence_le p hp i)]
  have hi : (gapIncidence r i:ℝ) ≤ 2 := by exact_mod_cast gapIncidence_le_two r i
  have he : (shiftGapExtra a i:ℝ) ≤ 2*(gapIncidence r i:ℝ) := by exact_mod_cast shiftGapExtra_le a i
  have h0 : (0:ℝ) ≤ shiftGapExtra a i := by positivity
  apply abs_le.mpr
  constructor  <;>  linarith

theorem period_shifted_gap_rounding {u m r : ℕ} (hr : 0 < r)
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2)
    (j : IncreasingTuple u r) (hsafe : SafeTaggedTuple (periodSlot off ∘ j.val))
    (a : Fin r → Fin 3) (i : Fin (r+1)) :
    |(tupleGap (shiftedTag (periodSlot off ∘ j.val) hsafe a) i:ℝ)-
      (m:ℝ)*coarsePeriodGap j.val i/2| ≤ 6 := by
  have ht := abs_sub_le (tupleGap (shiftedTag (periodSlot off ∘ j.val) hsafe a) i:ℝ)
    (tupleGap (periodSlot off ∘ j.val) i:ℝ) ((m:ℝ)*coarsePeriodGap j.val i/2)
  have h1 := tupleGap_shifted_close (periodSlot off ∘ j.val) hsafe a i
  have h2 := period_gap_rounding hr off hoff hdiff j.val j.property i
  linarith

theorem coarse_outside_implies_gap_tail {z g c θ m : ℝ}
    (hθ : θ ∈ Set.Icc 0 1) (hm : 128 ≤ m) (hg : |g-m*c/2| ≤ 6)
    (hz : m/8 ≤ |z-θ*m*c/2|) : m/16 ≤ |z-g*θ| := by
  have he : |g*θ-θ*m*c/2| ≤ 6 := by
    have h := mul_le_mul_of_nonneg_right hg hθ.1
    rw [show g*θ-θ*m*c/2=(g-m*c/2)*θ by ring,abs_mul,abs_of_nonneg hθ.1]
    exact h.trans (by nlinarith [hθ.2])
  have ht := abs_sub_le z (g*θ) (θ*m*c/2)
  linarith

/-- The manuscript's rank rectangles lose exponentially little mass for
 every bounded shift of a tagged tuple. -/
theorem period_shifted_outside_region {u m l r : ℕ}
    (hu : 0 < u) (hm : 128 ≤ m) (hr : 0 < r) (hl : l ≤ u*m)
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2)
    (j : IncreasingTuple u r) (hsafe : SafeTaggedTuple (periodSlot off ∘ j.val))
    (a : Fin r → Fin 3) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 1) :
    (∑ v : IncreasingTuple l r,
      if PeriodRankRegion m θ j v then 0 else
        subsetRankKernel hl (shiftedTag (periodSlot off ∘ j.val) hsafe a) v.val)  ≤ 
      ((r+1:ℕ):ℝ)*θ^r /binomialMass (u*m) θ l *
        (2*Real.exp (-(m:ℝ)/(1024*u))) := by
  let p := shiftedTag (periodSlot off ∘ j.val) hsafe a
  have hu' : (0:ℝ) < u := by exact_mod_cast hu
  have ht : (1/(32*(u:ℝ))) ∈ Set.Icc 0 1 := by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      have : (1:ℝ) ≤ u := by exact_mod_cast hu
      linarith
  have hx : -(1/(32*(u:ℝ)))*((m:ℝ)/16)+((u*m:ℕ):ℝ)*(1/(32*(u:ℝ)))^2 =
      -(m:ℝ)/(1024*u) := by push_cast; field_simp; ring
  calc
    _  ≤  ∑ v : IncreasingTuple l r,
      if ∃ i, (m:ℝ)/16 ≤ |(tupleGap v.val i:ℝ)-(tupleGap p i:ℝ)*θ|
      then subsetRankKernel hl p v.val else 0 := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : PeriodRankRegion m θ j v
      · simp only [ite_eq_left hv]
        split_ifs
        · exact subsetRankKernel_nonneg hl p v.val
        · rfl
      · simp only [PeriodRankRegion,not_forall,not_lt] at hv
        obtain ⟨i,hi⟩ := hv
        have he : ∃ i', (m:ℝ)/16 ≤ |(tupleGap v.val i':ℝ)-(tupleGap p i':ℝ)*θ| :=
          ⟨i.castSucc,coarse_outside_implies_gap_tail ⟨hθ.1.le,hθ.2.le⟩
            (by exact_mod_cast hm) (period_shifted_gap_rounding hr off hoff hdiff j hsafe a i.castSucc) hi⟩
        rw [ite_eq_left he]
        split_ifs
        · exact subsetRankKernel_nonneg hl p v.val
        · rfl
    _  ≤  _ := by
      have hh := subsetRankKernel_outside_region hl p (shiftedTag_strictMono _ hsafe a) hθ ht (a := (m:ℝ)/16)
      simpa only [hx] using hh

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The literal support indicator of the length-2^s signed block. -/
def motifIndicator (s : ℕ) (z : ℤ) : ℝ :=
  if 0 ≤ z ∧ z < (2^s : ℕ) then 1 else 0

theorem prouhet_motif_value (s : ℕ) (z : ℤ) :
    IsMotifValue (motifIndicator s z) ((prouhetSeries s).coeff z) := by
  by_cases hz : 0 ≤ z ∧ z < (2^s : ℕ)
  · right
    refine ⟨by simp only [motifIndicator,ite_eq_left hz], ?_⟩
    have hv := (prouhetSeries_coeff_spec s).2 z hz.1 hz.2
    exact (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hv
  · left
    refine ⟨by simp only [motifIndicator,ite_eq_right hz], ?_⟩
    apply (prouhetSeries_coeff_spec s).1 z
    omega

theorem motif_weight_abs_le (χ β : ℝ) (h : IsMotifValue χ β) (k : GapDifference) :
    |motifDifferenceWeight χ β 1 k| ≤ 1 := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl | rfl⟩ <;> cases k <;>
    norm_num [motifDifferenceWeight]

theorem motif_weight_abs_le_indicator (χ β : ℝ) (h : IsMotifValue χ β)
    (k : GapDifference) (hk : k ≠ .unchanged) :
    |motifDifferenceWeight χ β 1 k| ≤ χ := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl | rfl⟩ <;> cases k <;>
    norm_num [motifDifferenceWeight] at *

/-- A kernel-pattern multiplier averaged over the actual finitely supported
 anchor law. No independence of its involved positions is asserted. -/
def motifPatternMultiplier {r : ℕ} (π : IntSeries) (s : ℕ)
    (j : Fin r → ℤ) (k : Fin r → GapDifference) : ℝ :=
  ∑ X ∈ π.coeff.support, π.coeff X *
    ∏ h, motifDifferenceWeight (motifIndicator s (j h-X))
      ((prouhetSeries s).coeff (j h-X)) 1 (k h)

def linearPattern {r : ℕ} (h : Fin r) (a : Fin r) : GapDifference :=
  if a=h then .first else .unchanged

theorem motif_linear_multiplier {r : ℕ} (π : IntSeries) (s : ℕ)
    (j : Fin r → ℤ) (h : Fin r) :
    motifPatternMultiplier π s j (linearPattern h)=
      (prouhetSeries s * π).coeff (j h) := by
  classical
  rw [mul_comm,AddMonoidAlgebra.coeff_mul_apply_left,Finsupp.sum]
  apply Finset.sum_congr rfl
  intro X _
  congr 1
  have hw (a : Fin r) : motifDifferenceWeight (motifIndicator s (j a-X))
      ((prouhetSeries s).coeff (j a-X)) 1 (linearPattern h a)=
      if a=h then (prouhetSeries s).coeff (j h-X) else 1 := by
    by_cases ha : a=h <;> simp [linearPattern,ha,motifDifferenceWeight]
  simp_rw [hw]
  simp [sub_eq_neg_add]

theorem motifPatternMultiplier_abs_le {r : ℕ} (π : IntSeries)
    (hπ : ∀ X, 0 ≤ π.coeff X) (s : ℕ) (j : Fin r → ℤ)
    (k : Fin r → GapDifference) (h : Fin r) (hk : k h ≠ .unchanged) :
    |motifPatternMultiplier π s j k| ≤
      ∑ X ∈ π.coeff.support, π.coeff X*motifIndicator s (j h-X) := by
  classical
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro X _
  rw [abs_mul,abs_of_nonneg (hπ X),Finset.abs_prod]
  apply mul_le_mul_of_nonneg_left _ (hπ X)
  have hi (a) := motif_weight_abs_le _ _ (prouhet_motif_value s (j a-X)) (k a)
  have hh := motif_weight_abs_le_indicator _ _ (prouhet_motif_value s (j h-X)) (k h) hk
  calc
    _ ≤ ∏ a : Fin r, if a=h then motifIndicator s (j h-X) else 1 := by
      apply Finset.prod_le_prod₀
      · intro a _; positivity
      · intro a _
        by_cases ha : a=h
        · subst a; simpa using hh
        · simpa [ha] using hi a
    _ = _ := by simp

/-- A nonzero averaged pattern requires every involved tagged position to
 lie in one common translate of the motif; correlations are retained. -/
theorem motif_multiplier_nonzero_support {r : ℕ} (π : IntSeries) (s : ℕ)
    (j : Fin r → ℤ) (k : Fin r → GapDifference)
    (hm : motifPatternMultiplier π s j k ≠ 0) :
    ∃ X ∈ π.coeff.support, ∀ h, k h ≠ .unchanged →
      0 ≤ j h-X ∧ j h-X < (2^s : ℕ) := by
  classical
  obtain ⟨X,hX,hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  refine ⟨X,hX,?_⟩
  intro h hk
  by_contra hh
  apply hv
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero (Finset.mem_univ h)
  have hi : motifIndicator s (j h-X)=0 := by simp only [motifIndicator,ite_eq_right hh]
  have hw := motif_weight_abs_le_indicator _ _ (prouhet_motif_value s (j h-X)) (k h) hk
  exact abs_nonpos_iff.mp (hw.trans_eq hi)

theorem motif_multiplier_bounded_separation {r : ℕ} (π : IntSeries) (s : ℕ)
    (j : Fin r → ℤ) (k : Fin r → GapDifference)
    (hm : motifPatternMultiplier π s j k ≠ 0)
    (a b : Fin r) (ha : k a ≠ .unchanged) (hb : k b ≠ .unchanged) :
    |j a-j b| < (2^s : ℕ) := by
  obtain ⟨X,_,hX⟩ := motif_multiplier_nonzero_support π s j k hm
  have h1 := hX a ha
  have h2 := hX b hb
  exact abs_lt.mpr ⟨by omega,by omega⟩

/-- Mixing commutes with the exact signed positional expansion. -/
theorem mixed_signed_shift_expansion {r : ℕ} (π : IntSeries) (s : ℕ)
    (j : Fin r → ℤ) (W : (Fin r → Fin 3) → ℝ) :
    (∑ X ∈ π.coeff.support, π.coeff X *
      (W (fun h => motifShift (motifIndicator s (j h-X)) ((prouhetSeries s).coeff (j h-X)) 1)-
       W (fun h => motifShift (motifIndicator s (j h-X)) ((prouhetSeries s).coeff (j h-X)) (-1))))=
      ∑ k : Fin r → GapDifference,
        (if Odd (firstDifferenceCount k) then 2*motifPatternMultiplier π s j k else 0)*
        (∑ a : Fin r → Fin 3, (∏ h, positionalWeight (k h) (a h))*W a) := by
  calc
    _ = ∑ X ∈ π.coeff.support, ∑ k : Fin r → GapDifference,
        π.coeff X*((if Odd (firstDifferenceCount k) then
          2*∏ h, motifDifferenceWeight (motifIndicator s (j h-X))
            ((prouhetSeries s).coeff (j h-X)) 1 (k h) else 0)*
          (∑ a : Fin r → Fin 3, (∏ h, positionalWeight (k h) (a h))*W a)) := by
      apply Finset.sum_congr rfl
      intro X _
      rw [motif_signed_shift_expansion _ _ (fun h => prouhet_motif_value s (j h-X)) W,
        Finset.mul_sum]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : Odd (firstDifferenceCount k)
      · simp only [ite_eq_left hk,motifPatternMultiplier]
        calc
          _ = (∑ X ∈ π.coeff.support, 2*(π.coeff X *
                ∏ h, motifDifferenceWeight (motifIndicator s (j h-X))
                  ((prouhetSeries s).coeff (j h-X)) 1 (k h))) *
              (∑ a : Fin r → Fin 3, (∏ h, positionalWeight (k h) (a h))*W a) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro X _; ring
          _ = _ := by rw [← Finset.mul_sum]
      · simp only [ite_eq_right hk,zero_mul,mul_zero,Finset.sum_const_zero]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- A general weighted fiber sum, including multipliers which vanish on
 inadmissible anchor labels. -/
theorem weighted_fiber_sum_le {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (a : α → ℝ) (w : β → ℝ) (P : α → ℝ) (C : ℝ)
    (hP : ∀ x, 0 ≤ P x) (ha : ∀ x, a x^2 ≤ w (f x)^2)
    (hC : ∀ y, w y ≠ 0 → (∑ x : {x // f x=y}, P x.val) ≤ C) :
    (∑ x, a x^2*P x) ≤ C*∑ y, w y^2 := by
  classical
  calc
    _ ≤ ∑ x, w (f x)^2*P x :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (ha x) (hP x)
    _ = ∑ y, w y^2*∑ x : {x // f x=y}, P x.val := by
      rw [← Fintype.sum_fiberwise f (fun x => w (f x)^2*P x)]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [x.property]
    _ ≤ ∑ y, w y^2*C := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : w y=0
      · simp [hy]
      · exact mul_le_mul_of_nonneg_left (hC y hy) (sq_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Explicit central-anchor summation constant for doubled period gaps. -/
def periodCentralSumConstant (u r : ℕ) : ℝ :=
  ((r+1:ℕ):ℝ)^2*((u:ℝ)/(3*(r+1:ℝ)))⁻¹*(2*Real.sqrt (2*u:ℕ))^(r-1)

theorem weighted_period_gap_sum {u r : ℕ} (a : Fin r)
    (A : IncreasingTuple u r → ℝ) (w : Fin u → ℝ)
    (hA : ∀ j, A j^2 ≤ w (j.val a)^2)
    (hw : ∀ h, w h ≠ 0 → (u:ℝ)/3 ≤ 2*h.val+1 ∧ (u:ℝ)/3 ≤ 2*u-(2*h.val+1)) :
    (∑ j : IncreasingTuple u r, A j^2*∏ i, (Real.sqrt (coarsePeriodGap j.val i))⁻¹) ≤
      periodCentralSumConstant u r *∑ h, w h^2 := by
  apply weighted_fiber_sum_le (fun j : IncreasingTuple u r => j.val a) A w
    (fun j => ∏ i, (Real.sqrt (coarsePeriodGap j.val i))⁻¹)
    (periodCentralSumConstant u r) (fun _ => by positivity) hA
  intro h hh
  calc
    _ = ∑ j : FixedPeriodTuple u r a h,
        ∏ i, (Real.sqrt (coarsePeriodGap j.val.val i))⁻¹ :=
      by
        congr 1
        exact congrArg (fun i : Fintype (FixedPeriodTuple u r a h) => @Finset.univ _ i)
          (Subsingleton.elim _ _)
    _ ≤ _ := fixedPeriodProfile_central_sum a h (hw h hh).1 (hw h hh).2

/-- The two largest gaps exist even after arbitrary restrictions on the
 tuple, provided its anchor label is central. -/
theorem fixedPeriodProfile_large_sides {u r : ℕ} (a : Fin r) (h : Fin u)
    (hleft : (u:ℝ)/3 ≤ 2*h.val+1)
    (hright : (u:ℝ)/3 ≤ 2*u-(2*h.val+1)) (j : FixedPeriodTuple u r a h) :
    (∃ e ∈ Finset.Iic a.castSucc, (u:ℝ)/(3*(r+1:ℝ)) ≤ (fixedPeriodProfile a h j e).val) ∧
    (∃ d ∉ Finset.Iic a.castSucc, (u:ℝ)/(3*(r+1:ℝ)) ≤ (fixedPeriodProfile a h j d).val) := by
  classical
  let A := Finset.Iic a.castSucc
  let p := fixedPeriodProfile a h
  have hL : ∃ e∈A, (u:ℝ)/(3*(r+1:ℝ)) ≤ (p j e).val := by
    apply exists_large_in_subset A ⟨0, by simp [A]⟩ (fun i => (p j i).val)
      (fun _ => Nat.cast_nonneg _)
    have hs := fixedPeriodProfile_prefix a h j
    have hs' : (∑ i∈A, ((p j i).val:ℝ))=2*h.val+1 := by exact_mod_cast hs
    rw [hs']
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    convert hleft using 1; field_simp
  have hD : ∃ d∉A, (u:ℝ)/(3*(r+1:ℝ)) ≤ (p j d).val := by
    have ha : a.val<r := a.isLt
    have hlast : Fin.last r∈Aᶜ := by simp [A]
    obtain ⟨d,hd,hdR⟩ := exists_large_in_subset Aᶜ ⟨Fin.last r,hlast⟩
      (fun i => ((p j i).val:ℝ)) (fun _ => Nat.cast_nonneg _) (R := (u:ℝ)/(3*(r+1:ℝ))) (by
        have hs := fixedPeriodProfile_prefix a h j
        have ht := fixedPeriodProfile_total a h j
        have hs' : (∑ i∈A, ((p j i).val:ℝ))=2*h.val+1 := by exact_mod_cast hs
        have ht' : (∑ i, ((p j i).val:ℝ))=2*u := by exact_mod_cast ht
        have hc := Finset.sum_compl_add_sum A (fun i => ((p j i).val:ℝ))
        have hsum : (∑ i∈Aᶜ, ((p j i).val:ℝ))=2*u-(2*h.val+1) := by linarith
        rw [hsum]
        simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
        convert hright using 1; field_simp)
    exact ⟨d,Finset.mem_compl.mp hd,hdR⟩
  exact ⟨hL,hD⟩

/-- Source's bounded gap refinement at a prescribed central label. -/
theorem fixedPeriodProfile_bounded_central_sum {u r M : ℕ} (a : Fin r) (h : Fin u)
    (c : Fin (r+1)) (hleft : (u:ℝ)/3 ≤ 2*h.val+1)
    (hright : (u:ℝ)/3 ≤ 2*u-(2*h.val+1)) (hM : (M:ℝ) < (u:ℝ)/(3*(r+1:ℝ))) :
    (∑ j : FixedPeriodTuple u r a h,
      if coarsePeriodGap j.val.val c ≤ M then ∏ i, (Real.sqrt (coarsePeriodGap j.val.val i))⁻¹ else 0) ≤
      ((r+1:ℕ):ℝ)^2*((u:ℝ)/(3*(r+1:ℝ)))⁻¹*(M+1)*(2*Real.sqrt (2*u:ℕ))^(r-2) := by
  classical
  let α := {j : FixedPeriodTuple u r a h // coarsePeriodGap j.val.val c ≤ M}
  let p (j : α) := fixedPeriodProfile a h j.val
  have hu : (0:ℝ) < u := by exact_mod_cast (Nat.zero_lt_of_lt h.isLt)
  have hR : 0 < (u:ℝ)/(3*(r+1:ℝ)) := by positivity
  have hs := two_sided_bounded_gaps_sum (Finset.Iic a.castSucc) c p
    ((fixedPeriodProfile_injective a h).comp Subtype.val_injective)
    (fun j => fixedPeriodProfile_prefix a h j.val)
    (fun j => fixedPeriodProfile_total a h j.val) hR hM
    (fun j => (fixedPeriodProfile_large_sides a h hleft hright j.val).1)
    (fun j => (fixedPeriodProfile_large_sides a h hleft hright j.val).2)
    (fun j => j.property)
  have he : (∑ j : FixedPeriodTuple u r a h,
      if coarsePeriodGap j.val.val c ≤ M then ∏ i, (Real.sqrt (coarsePeriodGap j.val.val i))⁻¹ else 0)=
      ∑ j : α, ∏ i, (Real.sqrt (coarsePeriodGap j.val.val.val i))⁻¹ := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by intro j; simp) _
  rw [he]
  simpa only [α,p,fixedPeriodProfile,Fin.val_mk,Fintype.card_fin,
    show r+1-3=r-2 by omega] using hs

def periodBoundedSumConstant (u r M : ℕ) : ℝ :=
  ((r+1:ℕ):ℝ)^2*((u:ℝ)/(3*(r+1:ℝ)))⁻¹*(M+1)*(2*Real.sqrt (2*u:ℕ))^(r-2)

theorem weighted_period_bounded_gap_sum {u r M : ℕ} (a : Fin r) (c : Fin (r+1))
    (A : IncreasingTuple u r → ℝ) (w : Fin u → ℝ)
    (hA : ∀ j, A j^2 ≤ w (j.val a)^2)
    (hsupport : ∀ j, A j ≠ 0 → coarsePeriodGap j.val c ≤ M)
    (hw : ∀ h, w h ≠ 0 → (u:ℝ)/3 ≤ 2*h.val+1 ∧ (u:ℝ)/3 ≤ 2*u-(2*h.val+1))
    (hM : (M:ℝ) < (u:ℝ)/(3*(r+1:ℝ))) :
    (∑ j : IncreasingTuple u r, A j^2*∏ i, (Real.sqrt (coarsePeriodGap j.val i))⁻¹) ≤
      periodBoundedSumConstant u r M *∑ h, w h^2 := by
  have hp (j : IncreasingTuple u r) :
      A j^2*(∏ i, (Real.sqrt (coarsePeriodGap j.val i))⁻¹)=
      A j^2*(if coarsePeriodGap j.val c ≤ M then ∏ i, (Real.sqrt (coarsePeriodGap j.val i))⁻¹ else 0) := by
    by_cases hj : A j=0
    · simp [hj]
    · rw [ite_eq_left (hsupport j hj)]
  simp_rw [hp]
  apply weighted_fiber_sum_le (fun j : IncreasingTuple u r => j.val a) A w
    (fun j => if coarsePeriodGap j.val c ≤ M then ∏ i, (Real.sqrt (coarsePeriodGap j.val i))⁻¹ else 0)
    (periodBoundedSumConstant u r M) (fun _ => by split_ifs <;> positivity) hA
  intro h hh
  calc
    _ = ∑ j : FixedPeriodTuple u r a h,
        if coarsePeriodGap j.val.val c ≤ M then ∏ i, (Real.sqrt (coarsePeriodGap j.val.val i))⁻¹ else 0 :=
      by
        congr 1
        exact congrArg (fun i : Fintype (FixedPeriodTuple u r a h) => @Finset.univ _ i)
          (Subsingleton.elim _ _)
    _ ≤ _ := fixedPeriodProfile_bounded_central_sum a h c (hw h hh).1 (hw h hh).2 hM

end TraceReconstruction


namespace TraceReconstruction

/-- A displaced child window as an actual interval of the deterministic
 parent template. `t` is the realized count of atoms before the window. -/
def childWindowIndex {P T : ℕ} (t : ℕ) (hfit : t+T ≤ P) (h : Fin T) : Fin P :=
  ⟨t+h.val, by omega⟩

theorem templateType_inside_window {P T a L t : ℕ}
    (sign : Fin L → Bool) (τ : Bool) (hfit : t+T ≤ P)
    (hleft : t ≤ a) (h : Fin T) :
    templateType P a L sign τ (childWindowIndex t hfit h)=
      templateType T (a-t) L sign τ h := by
  have he : (a ≤ (childWindowIndex t hfit h).val ∧
      (childWindowIndex t hfit h).val < a+L) ↔
      a-t ≤ h.val ∧ h.val < a-t+L := by dsimp [childWindowIndex]; omega
  unfold templateType
  split_ifs with h1 h2 h2
  · congr 2
    apply Fin.ext
    dsimp [childWindowIndex]
    omega
  · exact False.elim (h2 (he.mp h1))
  · exact False.elim (h1 (he.mpr h2))
  · rfl

/-- When the motif fits its assigned window, every atom outside that
 window has the default pure type, including pieces crossing nominal cuts. -/
theorem templateType_outside_window {P T a L t : ℕ}
    (sign : Fin L → Bool) (τ : Bool) (hleft : t ≤ a) (hright : a+L ≤ t+T)
    (i : Fin P) (hi : i.val < t ∨ t+T ≤ i.val) :
    templateType P a L sign τ i=false := by
  have he : ¬(a ≤ i.val ∧ i.val < a+L) := by omega
  simp [templateType,he]

/-- A literal centered window remains within its own nominal parent unit,
 and contains the motif, whenever its jitter has the source fit bound.
 This elementary statement is independent of the distribution of the jitter. -/
theorem centered_window_fit (P T L a A t : ℕ) (Y : ℤ)
    (hP : 2*T ≤ P) (hA : 2*A=P-T) (ha : 2*a=P)
    (hL : 8*L ≤ T) (hY : |8*Y| ≤ (T:ℤ)) (ht : (t:ℤ)=A+Y) :
    t+T ≤ P ∧ t ≤ a ∧ a+L ≤ t+T := by
  have hy := abs_le.mp hY
  omega

/-- Flattened deterministic parent type, before any random partition. -/
def parentGroupType {R P L : ℕ} (a : ℕ) (sign : Fin L → Bool)
    (τ : Fin R → Bool) (u : Fin R) (h : Fin P) : Bool :=
  templateType P a L sign (τ u) h

theorem parentGroup_window_types {R P T L : ℕ} (a : ℕ) (sign : Fin L → Bool)
    (τ : Fin R → Bool) (t : Fin R → ℕ)
    (hfit : ∀ u, t u+T ≤ P) (hleft : ∀ u, t u ≤ a)
    (u : Fin R) (h : Fin T) :
    parentGroupType a sign τ u (childWindowIndex (t u) (hfit u) h)=
      templateType T (a-t u) L sign (τ u) h :=
  templateType_inside_window sign (τ u) (hfit u) (hleft u) h

end TraceReconstruction

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
