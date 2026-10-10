import OAI.Analysis.Unitarizability.FiniteSigns
import OAI.Analysis.Unitarizability.NetOperator
import OAI.Analysis.Unitarizability.FiniteSynthesis

namespace OAI

/-! Normalized sign matrices and their finite-dimensional bilinear
tests. The coordinate selections are injective and retain label identities. -/
noncomputable section
namespace Dixmier
namespace SignMatrix
open Finset
variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq J := Classical.decEq J
local instance : DecidableEq K := Classical.decEq K

theorem sum_on_embedding {R : Type*} [AddCommMonoid R] (e : J ↪ I) (f : I → R)
    (hf : ∀ i, (¬ ∃ j, e j = i) → f i = 0) : ∑ i, f i = ∑ j, f (e j) := by
  calc
    _ = ∑ i ∈ univ.map e, f i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i hi hn
      apply hf i
      simpa using hn
    _ = _ := by rw [Finset.sum_map]

def extend (e : J ↪ I) (z : J → ℝ) : I → ℝ := Function.extend e z (fun _ => 0)

omit [Fintype I] [Fintype J] in
@[simp] theorem extend_apply (e : J ↪ I) (z : J → ℝ) (j : J) : extend e z (e j) = z j :=
  e.injective.extend_apply z _ j

omit [Fintype I] [Fintype J] in
theorem extend_off (e : J ↪ I) (z : J → ℝ) (i : I) (hi : ¬ ∃ j, e j = i) : extend e z i = 0 :=
  Function.extend_apply' z _ i hi

theorem sum_extend_sq (e : J ↪ I) (z : J → ℝ) : ∑ i, (extend e z i)^2 = ∑ j, (z j)^2 := by
  rw [sum_on_embedding e _ (fun i hi => by rw [extend_off e z i hi]; simp)]
  simp only [extend_apply]

def vector (σ : K × I → Bool) (i : I) : EuclideanSpace ℝ K :=
  WithLp.toLp 2 (fun a => FiniteSigns.sign (σ (a,i)) / Real.sqrt (Fintype.card K))

omit [Fintype I] in
@[simp] theorem vector_apply (σ : K × I → Bool) (i : I) (a : K) :
    vector σ i a = FiniteSigns.sign (σ (a,i)) / Real.sqrt (Fintype.card K) := rfl

theorem sign_sq (b : Bool) : (FiniteSigns.sign b)^2 = 1 := by cases b <;> norm_num [FiniteSigns.sign]

omit [Fintype I] in
theorem vector_norm [Nonempty K] (σ : K × I → Bool) (i : I) : ‖vector σ i‖ = 1 := by
  have hk : (0 : ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  have h : ‖vector σ i‖^2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [vector_apply, Real.norm_eq_abs, sq_abs, div_pow, sign_sq,
      Real.sq_sqrt hk.le, Finset.sum_const, card_univ, nsmul_eq_mul]
    field_simp
  nlinarith [norm_nonneg (vector σ i)]

def synthesis (σ : K × I → Bool) (e : J ↪ I) : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ K :=
  ∑ j : J, InnerProductSpace.rankOne ℝ (vector σ (e j)) (EuclideanSpace.basisFun J ℝ j)

omit [Fintype I] in
@[simp] theorem synthesis_apply (σ : K × I → Bool) (e : J ↪ I) (z : EuclideanSpace ℝ J) :
    synthesis σ e z = ∑ j, z j • vector σ (e j) := by
  simp only [synthesis, _root_.sum_apply, InnerProductSpace.rankOne_apply, EuclideanSpace.basisFun_inner]

def testCoefficients (e : J ↪ I) (w : EuclideanSpace ℝ K) (z : EuclideanSpace ℝ J) : K × I → ℝ :=
  fun ai => w ai.1 * extend e z ai.2 / Real.sqrt (Fintype.card K)

theorem testCoefficients_sq [Nonempty K] (e : J ↪ I) (w : EuclideanSpace ℝ K) (z : EuclideanSpace ℝ J)
    (hw : ‖w‖ = 1) (hz : ‖z‖ = 1) :
    ∑ ai, (testCoefficients e w z ai)^2 = 1 / (Fintype.card K : ℝ) := by
  have hk : (0 : ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  have hw' : ∑ a, (w a)^2 = 1 := by
    have h : ‖w‖^2 = 1 := by rw [hw]; norm_num
    rw [EuclideanSpace.norm_sq_eq] at h
    simpa only [Real.norm_eq_abs, sq_abs] using h
  have hz' : ∑ j, (z j)^2 = 1 := by
    have h : ‖z‖^2 = 1 := by rw [hz]; norm_num
    rw [EuclideanSpace.norm_sq_eq] at h
    simpa only [Real.norm_eq_abs, sq_abs] using h
  simp only [testCoefficients, Fintype.sum_prod_type, mul_pow,
    div_eq_mul_inv, ← Finset.sum_mul, ← Finset.mul_sum, sum_extend_sq, hw', hz', mul_one, one_mul]
  rw [inv_pow, Real.sq_sqrt hk.le]

theorem bilinear_test (σ : K × I → Bool) (e : J ↪ I) (w : EuclideanSpace ℝ K) (z : EuclideanSpace ℝ J) :
    inner ℝ (synthesis σ e z) w = FiniteSigns.value (testCoefficients e w z) σ := by
  rw [synthesis_apply]
  simp only [sum_inner, inner_smul_left, RCLike.conj_to_real, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Pi.star_apply, star_trivial, vector_apply, FiniteSigns.value, testCoefficients,
    Fintype.sum_prod_type]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [sum_on_embedding e _ (fun i hi => by rw [extend_off e z i hi]; simp)]
  simp only [extend_apply]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The tail bound for each fixed pair of real unit test vectors and
an injective coordinate selection, on the full sign-matrix sample space. -/
theorem bilinear_tail [Nonempty K] (e : J ↪ I) (w : EuclideanSpace ℝ K) (z : EuclideanSpace ℝ J)
    (hw : ‖w‖ = 1) (hz : ‖z‖ = 1) :
    (((univ.filter fun σ : K × I → Bool => (5 : ℝ) < |inner ℝ (synthesis σ e z) w|).card : ℕ) : ℝ) /
      (2 : ℝ)^Fintype.card (K × I) ≤ 2 * Real.exp (-(Fintype.card K : ℝ)*25/2) := by
  simp_rw [bilinear_test]
  have h := FiniteSigns.two_sided_tail (k := (Fintype.card K : ℝ)) (u := 5) (testCoefficients e w z)
    (Nat.cast_pos.mpr (Fintype.card_pos (α := K))) (by norm_num : (0 : ℝ) < 5)
    (testCoefficients_sq e w z hw hz)
  convert h using 1 <;> try norm_num
  congr 1
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end SignMatrix
end Dixmier

end

end OAI
