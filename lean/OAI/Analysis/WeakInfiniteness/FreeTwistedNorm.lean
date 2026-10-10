import Mathlib
import OAI.Analysis.WeakInfiniteness.FellAbsorption

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

abbrev FreeTwo := FreeGroup Bool

abbrev FreeLetter := Bool × Bool

def freeLetter (s : FreeLetter) : FreeTwo :=
  if s.2 then FreeGroup.of s.1 else (FreeGroup.of s.1)⁻¹

def inverseLetter (s : FreeLetter) : FreeLetter := (s.1, !s.2)

@[simp]
lemma freeLetter_inverseLetter (s : FreeLetter) :
    freeLetter (inverseLetter s) = (freeLetter s)⁻¹ := by
  rcases s with ⟨a, b⟩
  cases b <;> simp [freeLetter, inverseLetter]

@[simp]
lemma inverseLetter_inverseLetter (s : FreeLetter) :
    inverseLetter (inverseLetter s) = s := by
  rcases s with ⟨a,b⟩
  cases b <;> rfl

@[simp]
lemma toWord_freeLetter (s : FreeLetter) : (freeLetter s).toWord = [s] := by
  rcases s with ⟨a,b⟩
  cases b <;> simp [freeLetter, FreeGroup.toWord_inv, FreeGroup.invRev]

lemma toWord_freeLetter_mul (s : FreeLetter) (g : FreeTwo) :
    (freeLetter s * g).toWord =
      match g.toWord with
      | [] => [s]
      | t :: l => if s = inverseLetter t then l else s :: t :: l := by
  rw [FreeGroup.toWord_mul, toWord_freeLetter]
  simp only [List.singleton_append, FreeGroup.reduce.cons, FreeGroup.reduce_toWord]
  cases h : g.toWord with
  | nil => rfl
  | cons t l =>
    simp only [inverseLetter, Prod.ext_iff]

def freeTreeWeight (g : FreeTwo) : ℝ := (Real.sqrt 3) ^ (- (g.toWord.length : ℤ))

lemma freeTreeWeight_pos (g : FreeTwo) : 0 < freeTreeWeight g := by
  exact zpow_pos (Real.sqrt_pos.mpr (by norm_num)) _

lemma freeTreeWeight_one : freeTreeWeight 1 = 1 := by
  simp [freeTreeWeight]

lemma freeTreeWeight_step_nil (s : FreeLetter) {g : FreeTwo} (h : g.toWord = []) :
    freeTreeWeight (freeLetter s * g) / freeTreeWeight g = (Real.sqrt 3)⁻¹ := by
  simp [freeTreeWeight, toWord_freeLetter_mul, h]

lemma freeTreeWeight_step_cons (s t : FreeLetter) (l : List FreeLetter)
    {g : FreeTwo} (h : g.toWord = t :: l) :
    freeTreeWeight (freeLetter s * g) / freeTreeWeight g =
      if s = inverseLetter t then Real.sqrt 3 else (Real.sqrt 3)⁻¹ := by
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  rw [freeTreeWeight, toWord_freeLetter_mul, h]
  unfold freeTreeWeight
  rw [h]
  by_cases he : s = inverseLetter t
  · simp only [ite_eq_left he, List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [← zpow_sub₀ hs]
    convert zpow_one (Real.sqrt 3) using 1
    congr 1
    omega
  · simp only [ite_eq_right he, List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [← zpow_sub₀ hs]
    convert zpow_neg_one (Real.sqrt 3) using 1
    congr 1
    omega

theorem freeTreeWeight_sum_le (g : FreeTwo) :
    ∑ s : FreeLetter, freeTreeWeight (freeLetter s * g) / freeTreeWeight g ≤
      2 * Real.sqrt 3 := by
  have hs0 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  cases h : g.toWord with
  | nil =>
    simp_rw [freeTreeWeight_step_nil _ h]
    norm_num
    have hi : Real.sqrt 3 * (Real.sqrt 3)⁻¹ = 1 := mul_inv_cancel₀ hs0.ne'
    nlinarith
  | cons t l =>
    simp_rw [freeTreeWeight_step_cons _ t l h]
    have hsum : (∑ s : FreeLetter, if s = inverseLetter t then Real.sqrt 3
        else (Real.sqrt 3)⁻¹) = Real.sqrt 3 + 3 * (Real.sqrt 3)⁻¹ := by
      rcases t with ⟨a,b⟩
      cases a <;> cases b <;> norm_num [Fintype.sum_prod_type, inverseLetter] <;> ring
    rw [hsum]
    have hi : Real.sqrt 3 * (Real.sqrt 3)⁻¹ = 1 := mul_inv_cancel₀ hs0.ne'
    nlinarith

lemma freeTree_norm_gap : 2 * Real.sqrt 3 < 4 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp := Real.sqrt_nonneg (3 : ℝ)
  nlinarith

theorem norm_freeTwisted_sum_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : FreeTwo →* H ≃ₗᵢ[ℂ] H) :
    ‖∑ s : FreeLetter, HilbertValued.twistedRegular π (freeLetter s)‖ ≤
      2 * Real.sqrt 3 := by
  rw [HilbertValued.norm_twistedRegular_sum freeLetter Finset.univ π]
  apply HilbertValued.norm_permutationSum_le freeTreeWeight freeTreeWeight_pos
    (fun s : FreeLetter => Equiv.mulLeft (freeLetter s)) (2 * Real.sqrt 3)
    (by positivity)
  · intro g
    let e : FreeLetter ≃ FreeLetter :=
      ⟨inverseLetter, inverseLetter, inverseLetter_inverseLetter, inverseLetter_inverseLetter⟩
    have he := e.sum_comp (fun s => freeTreeWeight (freeLetter s * g) / freeTreeWeight g)
    simp only [e, Equiv.coe_fn_mk, freeLetter_inverseLetter] at he
    change (∑ s : FreeLetter, freeTreeWeight ((freeLetter s)⁻¹ * g) / freeTreeWeight g) ≤ _
    rw [he]
    exact freeTreeWeight_sum_le g
  · exact freeTreeWeight_sum_le

end WeakPureInfiniteness
end

end OAI
