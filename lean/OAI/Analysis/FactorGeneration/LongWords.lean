import Mathlib.Algebra.BigOperators.Fin
import OAI.Analysis.FactorGeneration.Coefficients
import OAI.Analysis.FactorGeneration.Convolution
import OAI.Analysis.FactorGeneration.Exponential
import OAI.Analysis.FactorGeneration.Words

namespace OAI

noncomputable section

namespace Generator

/-! Factorial coefficient majorization in every homogeneous degree. -/
section
open scoped BigOperators
open Generator.CoefficientOrder
variable {G : Type*} [Monoid G]

@[simp] theorem normCoefficients_zero : normCoefficients (0 : MonoidAlgebra ℂ G) = 0 := by
  ext w; simp

@[simp] theorem normCoefficients_one : normCoefficients (1 : MonoidAlgebra ℂ G) = 1 := by
  classical
  ext w
  simp only [normCoefficients_apply, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  split_ifs <;> norm_num

omit [Monoid G] in
@[simp] theorem normCoefficients_single (g : G) (c : ℂ) :
    normCoefficients (MonoidAlgebra.single g c) = MonoidAlgebra.single g ‖c‖ := by
  classical
  ext w
  simp only [normCoefficients_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs <;> simp

theorem normCoefficients_sub_le (f g : MonoidAlgebra ℂ G) :
    normCoefficients (f - g) ≤ normCoefficients f + normCoefficients g := by
  intro w
  simpa using norm_sub_le (f.coeff w) (g.coeff w)

theorem normCoefficients_sum_le {I : Type*} (s : Finset I) (f : I → MonoidAlgebra ℂ G) :
    normCoefficients (∑ i ∈ s, f i) ≤ ∑ i ∈ s, normCoefficients (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact le_trans (normCoefficients_add_le _ _) (add_le_add le_rfl ih)

theorem normCoefficients_pow_le (b : MonoidAlgebra ℂ G) (a : MonoidAlgebra ℝ G)
    (ha : 0 ≤ a) (hb : normCoefficients b ≤ a) (d : ℕ) :
    normCoefficients (b ^ d) ≤ a ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ, pow_succ]
    exact le_trans (normCoefficients_mul_le _ _)
      (mul_le_mul ih hb (fun w => normCoefficients_nonnegative b w) (pow_nonneg ha d))

theorem normCoefficients_real_smul (r : ℝ) (hr : 0 ≤ r) (b : MonoidAlgebra ℂ G) :
    normCoefficients (r • b) = r • normCoefficients b := by
  ext w
  simp [Real.norm_eq_abs, abs_of_nonneg hr]

/-- Original-degree factorial terms are bounded by nondecreasing row words. -/
theorem exponentialDegree_le_orderedWords
    (rows : List (MonoidAlgebra ℂ G × MonoidAlgebra ℝ G))
    (h : ∀ row ∈ rows, 0 ≤ row.2 ∧ normCoefficients row.1 ≤ row.2) (d : ℕ) :
    normCoefficients (exponentialDegree (rows.map Prod.fst) d) ≤
      orderedWords (rows.map Prod.snd) d := by
  induction rows generalizing d with
  | nil =>
    cases d <;> simp [exponentialDegree]
  | cons row rows ih =>
    have hr := h row (by simp)
    have ht : ∀ r ∈ rows, 0 ≤ r.2 ∧ normCoefficients r.1 ≤ r.2 :=
      fun r hm => h r (by simp [hm])
    have hp : ∀ a ∈ rows.map Prod.snd, 0 ≤ a := by
      intro a ha
      obtain ⟨r, hm, rfl⟩ := List.mem_map.mp ha
      exact (ht r hm).1
    simp only [List.map_cons, exponentialDegree]
    rw [orderedWords_cons]
    apply (normCoefficients_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro k _
    have hw0 : 0 ≤ (k.factorial : ℝ)⁻¹ := by positivity
    have hw1 : (k.factorial : ℝ)⁻¹ ≤ 1 := by
      apply inv_le_one_of_one_le₀
      exact_mod_cast Nat.factorial_pos k
    have hpow := normCoefficients_pow_le row.1 row.2 hr.1 hr.2 k
    have hfactor : normCoefficients ((k.factorial : ℝ)⁻¹ • row.1 ^ k) ≤ row.2 ^ k := by
      rw [normCoefficients_real_smul _ hw0]
      intro w
      change (k.factorial : ℝ)⁻¹ * ‖(row.1 ^ k).coeff w‖ ≤ (row.2 ^ k).coeff w
      exact (mul_le_mul_of_nonneg_left (hpow w) hw0).trans
        (by simpa using mul_le_mul_of_nonneg_right hw1 ((pow_nonneg hr.1 k) w))
    exact le_trans (normCoefficients_mul_le _ _)
      (mul_le_mul hfactor (ih ht (d - k))
        (fun w => normCoefficients_nonnegative _ w) (pow_nonneg hr.1 k))

/-- The source's full coefficient inequality, for arbitrary monoids and all d.
The sum on the right is the actual collected convolution power. -/
theorem exponentialDegree_coefficient_majorization
    (rows : List (MonoidAlgebra ℂ G × MonoidAlgebra ℝ G))
    (h : ∀ row ∈ rows, 0 ≤ row.2 ∧ normCoefficients row.1 ≤ row.2) (d : ℕ) :
    normCoefficients (exponentialDegree (rows.map Prod.fst) d) ≤
      (rows.map Prod.snd).sum ^ d := by
  apply (exponentialDegree_le_orderedWords rows h d).trans
  apply orderedWords_le_sum_pow
  intro a ha
  obtain ⟨r, hm, rfl⟩ := List.mem_map.mp ha
  exact (h r hm).1

end

/-! The nonlinear remainder of the actual ordered convolution-operator
exponentials, evaluated at δ₁, without assumed degree estimates. -/
section
open scoped BigOperators
open Generator.CoefficientOrder Generator.FreeConvolution
variable {A : Type*}
local notation "H" => SquareSpace (FreeGroup A)
local notation "Op" => H →L[ℂ] H

/-- All original-degree bounds follow from coefficient majorization and the
norm of the positive total convolution operator. -/
theorem free_exponentialDegree_bound
    (rows : List (MonoidAlgebra ℂ (FreeGroup A) × MonoidAlgebra ℝ (FreeGroup A)))
    (h : ∀ row ∈ rows, 0 ≤ row.2 ∧ normCoefficients row.1 ≤ row.2) (d : ℕ) :
    ‖regular (exponentialDegree (rows.map Prod.fst) d) delta‖ ≤
      ‖realRegular (rows.map Prod.snd).sum‖ ^ d := by
  exact (regular_delta_norm_le (exponentialDegree_coefficient_majorization rows h d)).trans
    (realRegular_pow_delta_norm_le _ d)

/-- Actual nonlinear remainder. The positive total's norm bound is the only
analytic bound required; no degree-bound or series-sum hypothesis is assumed. -/
theorem free_exponential_product_remainder
    (rows : List (MonoidAlgebra ℂ (FreeGroup A) × MonoidAlgebra ℝ (FreeGroup A)))
    (h : ∀ row ∈ rows, 0 ≤ row.2 ∧ normCoefficients row.1 ≤ row.2)
    {α : ℝ} (hα : 0 < α) (hhalf : α < 1 / 2)
    (hbound : ‖realRegular (rows.map Prod.snd).sum‖ ≤ 2 * α) :
    ‖((rows.map (fun r => NormedSpace.exp (regular r.1))).prod - 1 -
      (rows.map (fun r => regular r.1)).sum) delta‖ ≤ 4 * α ^ 2 / (1 - 2 * α) := by
  let xs : List Op := rows.map (fun r => regular r.1)
  let coeff : ℕ → H := fun d => exponentialDegree xs d delta
  have hsum : HasSum coeff ((xs.map NormedSpace.exp).prod delta) := by
    exact (exponentialDegree_hasSum xs).map
      (ContinuousLinearMap.apply ℂ H delta).toAddMonoidHom
      (ContinuousLinearMap.apply ℂ H delta).continuous
  have hid (d : ℕ) : exponentialDegree xs d =
      regular (exponentialDegree (rows.map Prod.fst) d) := by
    simpa [xs, List.map_map, Function.comp_def] using
      (exponentialDegree_map (regular.restrictScalars ℝ) (rows.map Prod.fst) d).symm
  have hdegree (d : ℕ) : ‖coeff d‖ ≤ (2 * α) ^ d := by
    change ‖exponentialDegree xs d delta‖ ≤ _
    rw [hid]
    exact (free_exponentialDegree_bound rows h d).trans
      (pow_le_pow_left₀ (norm_nonneg _) hbound d)
  have ht := perturbation_remainder_from_degree_bounds hα hhalf coeff hsum
    (fun n => hdegree (n + 2))
  simpa [coeff, xs, List.map_map, Function.comp_def, sub_apply] using ht

end

/-! Signed rows B_k and positive rows A_k with free basis indexed by prefix ratios in FreeGroup Nat. -/
section
open scoped BigOperators
open Generator.CoefficientOrder Generator.FreeConvolution
local notation "G" => FreeGroup ℕ
local notation "F" => FreeGroup G
local instance : DecidableEq G := Classical.decEq _
local instance : DecidableEq F := Classical.decEq _

def positiveLetterPair (p : G) : MonoidAlgebra ℝ F :=
  MonoidAlgebra.single (letter (p, true)) 1 + MonoidAlgebra.single (letter (p, false)) 1

def negativeLetterPair (p : G) : MonoidAlgebra ℂ F :=
  MonoidAlgebra.single (letter (p, true)) 1 - MonoidAlgebra.single (letter (p, false)) 1

def perturbationRow {n : ℕ} (α : ℝ) (k : Fin n) : MonoidAlgebra ℂ F × MonoidAlgebra ℝ F :=
  ((α / (2 * n)) • ∑ j : Fin n, negativeLetterPair (pairRatio (k, j)),
   (α / (2 * n)) • ∑ j : Fin n, positiveLetterPair (pairRatio (k, j)))

def perturbationRows (n : ℕ) (α : ℝ) :
    List (MonoidAlgebra ℂ F × MonoidAlgebra ℝ F) := List.ofFn (perturbationRow (n := n) α)

theorem positiveLetterPair_nonnegative (p : G) : 0 ≤ positiveLetterPair p := by
  intro w
  simp only [positiveLetterPair, MonoidAlgebra.coeff_add, Finsupp.add_apply,
    MonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs <;> norm_num

theorem negativeLetterPair_dominated (p : G) :
    normCoefficients (negativeLetterPair p) ≤ positiveLetterPair p := by
  simpa [negativeLetterPair, positiveLetterPair] using
    normCoefficients_sub_le (MonoidAlgebra.single (letter (p, true)) 1)
      (MonoidAlgebra.single (letter (p, false)) 1)

/-- Positivity and domination are proved for the source rows, not assumed. -/
theorem perturbationRows_dominated (n : ℕ) (α : ℝ) (hα : 0 ≤ α) :
    ∀ row ∈ perturbationRows n α, 0 ≤ row.2 ∧ normCoefficients row.1 ≤ row.2 := by
  intro row hr
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp (show row ∈ List.ofFn (perturbationRow (n := n) α) from hr)
  have hc : 0 ≤ α / (2 * n) := by positivity
  have hp : 0 ≤ ∑ j : Fin n, positiveLetterPair (pairRatio (k, j)) :=
    Finset.sum_nonneg (fun j _ => positiveLetterPair_nonnegative _)
  constructor
  · intro w
    change 0 ≤ α / (2 * n) * (∑ j : Fin n, positiveLetterPair (pairRatio (k, j))).coeff w
    exact mul_nonneg hc (hp w)
  · change normCoefficients ((α / (2 * n)) • _) ≤ (α / (2 * n)) • _
    rw [normCoefficients_real_smul _ hc]
    have hb : normCoefficients (∑ j : Fin n, negativeLetterPair (pairRatio (k, j))) ≤
        ∑ j : Fin n, positiveLetterPair (pairRatio (k, j)) :=
      (normCoefficients_sum_le _ _).trans
        (Finset.sum_le_sum (fun j _ => negativeLetterPair_dominated _))
    intro w
    exact mul_le_mul_of_nonneg_left (hb w) hc

/-- Exact regrouping of the ordered-pair sum using the proved fiber counts. -/
theorem pairRatio_sum_multiplicity {R : Type*} [AddCommMonoid R]
    (n : ℕ) (hn : 0 < n) (f : G → R) :
    (∑ k : Fin n, ∑ j : Fin n, f (pairRatio (k, j))) =
      ∑ p ∈ ratioLabels n, multiplicity n p • f p := by
  have hm : ∀ ij ∈ (Finset.univ : Finset (Fin n × Fin n)), pairRatio ij ∈ ratioLabels n := by
    intro ij _
    rw [ratioLabels_eq_image hn]
    exact Finset.mem_image.mpr ⟨ij, Finset.mem_univ _, rfl⟩
  have h := Finset.sum_fiberwise_of_maps_to' hm f
  simpa [multiplicity, Fintype.sum_prod_type] using h.symm

/-- The sum of the source's positive rows is exactly its collected coefficient
family, including the n copies of the identity prefix ratio. -/
theorem perturbationRows_positive_total (n : ℕ) (hn : 0 < n) (α : ℝ) :
    (perturbationRows n α |>.map Prod.snd).sum =
      (α / (2 * n)) • ∑ p ∈ ratioLabels n, multiplicity n p • positiveLetterPair p := by
  simp only [perturbationRows, List.map_ofFn, List.sum_ofFn, Function.comp_def, perturbationRow]
  rw [← Finset.smul_sum, pairRatio_sum_multiplicity n hn]

/-- Identification of λ(A) with the signed-letter operator already bounded. -/
theorem perturbationRows_total_operator (n : ℕ) (hn : 0 < n) (α : ℝ) :
    realRegular (perturbationRows n α |>.map Prod.snd).sum =
      ∑ a ∈ prefixLetterSupport n, (prefixWeight n α a : ℂ) • leftRegular (letter a) := by
  rw [perturbationRows_positive_total n hn]
  simp only [map_smul, map_sum, map_nsmul, Finset.smul_sum]
  simp only [prefixLetterSupport, Finset.product_eq_sprod, prefixWeight,
    Finset.sum_product, Fintype.sum_bool]
  apply Finset.sum_congr rfl
  intro p _
  simp [positiveLetterPair, realRegular, MonoidAlgebra.lift_single, leftRegularHom,
    smul_add]
  simp only [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  norm_cast

/-- Uniform all-degree bound for the manuscript's literal formal rows. -/
theorem perturbationRows_degree_bound (n : ℕ) (hn : 0 < n)
    (α : ℝ) (hα : 0 ≤ α) (d : ℕ) :
    ‖regular (exponentialDegree (perturbationRows n α |>.map Prod.fst) d) delta‖ ≤
      (2 * α) ^ d := by
  apply (free_exponentialDegree_bound _ (perturbationRows_dominated n α hα) d).trans
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [perturbationRows_total_operator n hn]
  exact prefix_convolution_operator_bound n hn α hα

/-- The source's nonlinear estimate on the actual regular representation,
with its exact rows and constants, for every positive word length. -/
theorem perturbationRows_remainder (n : ℕ) (hn : 0 < n)
    (α : ℝ) (hα : 0 < α) (hhalf : α < 1 / 2) :
    ‖((perturbationRows n α |>.map (fun r => NormedSpace.exp (regular r.1))).prod - 1 -
      (perturbationRows n α |>.map (fun r => regular r.1)).sum) delta‖ ≤
        4 * α ^ 2 / (1 - 2 * α) := by
  apply free_exponential_product_remainder _ (perturbationRows_dominated n α hα.le) hα hhalf
  rw [perturbationRows_total_operator n hn]
  exact prefix_convolution_operator_bound n hn α hα.le

end

/-! Transfer of the nonlinear estimate to an algebra with a continuous Hilbert
realization and orthonormal reduced-word images, without an independence hypothesis. -/
section
open scoped BigOperators InnerProductSpace
open Generator.FreeConvolution
variable {B E : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
local notation "F" => FreeGroup (FreeGroup ℕ)

/-- The literal source remainder in any continuous Hilbert realization whose
reduced-word images are orthonormal. -/
theorem perturbationRows_remainder_transfer
    (Φ : MonoidAlgebra ℂ F →ₐ[ℂ] B) (ι : B →L[ℂ] E)
    (horth : Orthonormal ℂ (fun g => ι (Φ (MonoidAlgebra.single g 1))))
    (n : ℕ) (hn : 0 < n) (α : ℝ) (hα : 0 < α) (hhalf : α < 1 / 2) :
    ‖ι ((perturbationRows n α |>.map (fun r => NormedSpace.exp (Φ r.1))).prod -
      1 - (perturbationRows n α |>.map (fun r => Φ r.1)).sum)‖ ≤
        4 * α ^ 2 / (1 - 2 * α) := by
  let xs : List B := (perturbationRows n α).map (fun r => Φ r.1)
  let coeff : ℕ → E := fun d => ι (exponentialDegree xs d)
  have hsum : HasSum coeff (ι (xs.map NormedSpace.exp).prod) :=
    (exponentialDegree_hasSum xs).map ι.toAddMonoidHom ι.continuous
  have hbound : ‖realRegular (perturbationRows n α |>.map Prod.snd).sum‖ ≤ 2 * α := by
    rw [perturbationRows_total_operator n hn]
    exact prefix_convolution_operator_bound n hn α hα.le
  have hid (d : ℕ) : exponentialDegree xs d =
      Φ (exponentialDegree (perturbationRows n α |>.map Prod.fst) d) := by
    simpa [xs, List.map_map, Function.comp_def] using
      (exponentialDegree_map (Φ.restrictScalars ℝ) (perturbationRows n α |>.map Prod.fst) d).symm
  have hdegree (d : ℕ) : ‖coeff d‖ ≤ (2 * α) ^ d := by
    change ‖ι (exponentialDegree xs d)‖ ≤ _
    rw [hid]
    have hiso := groupRing_norm_eq_regular (ι.toLinearMap.comp Φ.toLinearMap) horth
      (exponentialDegree (perturbationRows n α |>.map Prod.fst) d)
    change ‖ι (Φ (exponentialDegree (perturbationRows n α |>.map Prod.fst) d))‖ = _ at hiso
    rw [hiso]
    exact (free_exponentialDegree_bound (perturbationRows n α)
      (perturbationRows_dominated n α hα.le) d).trans
      (pow_le_pow_left₀ (norm_nonneg _) hbound d)
  have ht := perturbation_remainder_from_degree_bounds hα hhalf coeff hsum
    (fun k => hdegree (k + 2))
  simpa [coeff, xs, List.map_map, Function.comp_def, map_sub] using ht

end

/-! The exact finite free basis and its injective realization in a countable free basis. -/
section
open scoped BigOperators
open Generator.FreeConvolution
local notation "G" => FreeGroup ℕ
local notation "F" => FreeGroup G
local instance : DecidableEq G := Classical.decEq _

/-- The manuscript's finite set S, including the identity prefix ratio as a label. -/
def PrefixLabel (n : ℕ) := {p : G // p ∈ ratioLabels n}

def pairLabel {n : ℕ} (k j : Fin n) : PrefixLabel n :=
  ⟨pairRatio (k, j), by
    rw [ratioLabels_eq_image (Nat.zero_lt_of_lt k.isLt)]
    exact Finset.mem_image.mpr ⟨(k, j), Finset.mem_univ _, rfl⟩⟩

def prefixWordEmbedding (n : ℕ) : FreeGroup (PrefixLabel n) →* F :=
  FreeGroup.map Subtype.val

theorem prefixWordEmbedding_injective (n : ℕ) : Function.Injective (prefixWordEmbedding n) :=
  FreeGroup.map_injective Subtype.val_injective

def prefixRingEmbedding (n : ℕ) : MonoidAlgebra ℂ (FreeGroup (PrefixLabel n)) →ₐ[ℂ]
    MonoidAlgebra ℂ F := MonoidAlgebra.mapDomainAlgHom ℂ ℂ (prefixWordEmbedding n)

@[simp] theorem prefixRingEmbedding_single (n : ℕ) (g : FreeGroup (PrefixLabel n)) (c : ℂ) :
    prefixRingEmbedding n (MonoidAlgebra.single g c) =
      MonoidAlgebra.single (prefixWordEmbedding n g) c := by
  exact MonoidAlgebra.mapDomain_single

/-- Literal B_k in the free group on the finite label set S. -/
def finitePerturbationRow {n : ℕ} (α : ℝ) (k : Fin n) :
    MonoidAlgebra ℂ (FreeGroup (PrefixLabel n)) :=
  (α / (2 * n)) • ∑ j : Fin n,
    (MonoidAlgebra.single (FreeGroup.of (pairLabel k j)) 1 -
     MonoidAlgebra.single ((FreeGroup.of (pairLabel k j))⁻¹) 1)

def finitePerturbationRows (n : ℕ) (α : ℝ) :=
  List.ofFn (finitePerturbationRow (n := n) α)

@[simp] theorem finitePerturbationRow_embed {n : ℕ} (α : ℝ) (k : Fin n) :
    prefixRingEmbedding n (finitePerturbationRow α k) = (perturbationRow α k).1 := by
  have hs (c : ℝ) (f : MonoidAlgebra ℂ (FreeGroup (PrefixLabel n))) :
      prefixRingEmbedding n (c • f) = c • prefixRingEmbedding n f :=
    map_smul ((prefixRingEmbedding n).restrictScalars ℝ).toLinearMap c f
  simp only [finitePerturbationRow, perturbationRow, hs, map_sum, map_sub,
    prefixRingEmbedding_single]
  congr 1

theorem finitePerturbationRows_embed (n : ℕ) (α : ℝ) :
    (finitePerturbationRows n α).map (prefixRingEmbedding n) =
      (perturbationRows n α).map Prod.fst := by
  simp [finitePerturbationRows, perturbationRows, List.map_ofFn, Function.comp_def]

def embeddedCoefficientMap (n : ℕ) :
    MonoidAlgebra ℂ (FreeGroup (PrefixLabel n)) →ₗ[ℂ] SquareSpace F :=
  (ContinuousLinearMap.apply ℂ (SquareSpace F) delta).toLinearMap.comp
    (regular.toLinearMap.comp (prefixRingEmbedding n).toLinearMap)

theorem embeddedCoefficientMap_orthonormal (n : ℕ) :
    Orthonormal ℂ (fun g => embeddedCoefficientMap n (MonoidAlgebra.single g 1)) := by
  have h := regular_delta_orthonormal.comp (prefixWordEmbedding n) (prefixWordEmbedding_injective n)
  simpa [embeddedCoefficientMap, LinearMap.comp_apply, Function.comp_def] using h

/-- All-degree estimate on the exact finite formal group F_S. -/
theorem finitePerturbationRows_degree_bound (n : ℕ) (hn : 0 < n)
    (α : ℝ) (hα : 0 ≤ α) (d : ℕ) :
    ‖embeddedCoefficientMap n (exponentialDegree (finitePerturbationRows n α) d)‖ ≤
      (2 * α) ^ d := by
  change ‖regular (prefixRingEmbedding n (exponentialDegree (finitePerturbationRows n α) d)) delta‖ ≤ _
  have hmap := exponentialDegree_map ((prefixRingEmbedding n).restrictScalars ℝ)
    (finitePerturbationRows n α) d
  change prefixRingEmbedding n (exponentialDegree (finitePerturbationRows n α) d) =
    exponentialDegree ((finitePerturbationRows n α).map (prefixRingEmbedding n)) d at hmap
  rw [hmap, finitePerturbationRows_embed]
  exact perturbationRows_degree_bound n hn α hα d

end

/-! Exact finite-basis version of the source's nonlinear estimate. Unlike the
ambient transport lemma, only reduced words in F_S occur in the hypothesis. -/
open scoped BigOperators InnerProductSpace
variable {B E : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Remainder bounds in a continuous Hilbert realization of the finite free group with orthonormal word images. -/
theorem finite_prefix_remainder_transfer (n : ℕ) (hn : 0 < n)
    (Φ : MonoidAlgebra ℂ (FreeGroup (PrefixLabel n)) →ₐ[ℂ] B) (ι : B →L[ℂ] E)
    (horth : Orthonormal ℂ (fun g => ι (Φ (MonoidAlgebra.single g 1))))
    (α : ℝ) (hα : 0 < α) (hhalf : α < 1 / 2) :
    ‖ι ((finitePerturbationRows n α |>.map (fun r => NormedSpace.exp (Φ r))).prod -
      1 - (finitePerturbationRows n α |>.map Φ).sum)‖ ≤
        4 * α ^ 2 / (1 - 2 * α) := by
  let xs : List B := (finitePerturbationRows n α).map Φ
  let coeff : ℕ → E := fun d => ι (exponentialDegree xs d)
  have hsum : HasSum coeff (ι (xs.map NormedSpace.exp).prod) :=
    (exponentialDegree_hasSum xs).map ι.toAddMonoidHom ι.continuous
  have hid (d : ℕ) : exponentialDegree xs d =
      Φ (exponentialDegree (finitePerturbationRows n α) d) := by
    exact (exponentialDegree_map (Φ.restrictScalars ℝ) _ d).symm
  have hdegree (d : ℕ) : ‖coeff d‖ ≤ (2 * α) ^ d := by
    change ‖ι (exponentialDegree xs d)‖ ≤ _
    rw [hid]
    have hiso := groupRing_norm_eq_of_orthonormal (ι.toLinearMap.comp Φ.toLinearMap)
      (embeddedCoefficientMap n) horth (embeddedCoefficientMap_orthonormal n)
      (exponentialDegree (finitePerturbationRows n α) d)
    change ‖ι (Φ (exponentialDegree (finitePerturbationRows n α) d))‖ = _ at hiso
    rw [hiso]
    exact finitePerturbationRows_degree_bound n hn α hα.le d
  have ht := perturbation_remainder_from_degree_bounds hα hhalf coeff hsum
    (fun k => hdegree (k + 2))
  simpa [coeff, xs, List.map_map, Function.comp_def, map_sub] using ht

/-- The unconditional finite-free-group remainder, on the actual left regular
representation of exactly F_S and for every positive word length. -/
theorem finite_prefix_regular_remainder (n : ℕ) (hn : 0 < n)
    (α : ℝ) (hα : 0 < α) (hhalf : α < 1 / 2) :
    ‖((finitePerturbationRows n α |>.map (fun r => NormedSpace.exp (FreeConvolution.regular r))).prod -
      1 - (finitePerturbationRows n α |>.map FreeConvolution.regular).sum)
        FreeConvolution.delta‖ ≤ 4 * α ^ 2 / (1 - 2 * α) := by
  exact finite_prefix_remainder_transfer n hn FreeConvolution.regular
    (ContinuousLinearMap.apply ℂ (SquareSpace (FreeGroup (PrefixLabel n))) FreeConvolution.delta)
    FreeConvolution.regular_delta_orthonormal α hα hhalf

end Generator

end

end OAI
