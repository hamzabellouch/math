import OAI.NumberTheory.TwoPoint.Bounds.CRTComparison
import Mathlib.Logic.Equiv.Prod

namespace OAI

/-! Elementary finite averaging identities used to assemble encoded marginals. -/

namespace TwoPointCorrelations

open Finset

noncomputable def uniformAverage {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card α

@[simp] lemma uniformAverage_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformAverage (fun _ : α => c) = c := by simp [uniformAverage]

lemma uniformAverage_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : uniformAverage (fun x => f (e x)) = uniformAverage f := by
  unfold uniformAverage
  rw [e.sum_comp, Fintype.card_congr e]

lemma uniformAverage_prod {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    uniformAverage (fun x : α × β => f x.1 x.2) =
      uniformAverage (fun x => uniformAverage (f x)) := by
  unfold uniformAverage
  rw [Fintype.sum_prod_type', Fintype.card_prod, Nat.cast_mul, ← Finset.sum_div]
  rw [div_div]
  congr 1
  ring

/-- A uniform independent family restricted to selected coordinates remains
uniform; coordinates outside the selection integrate out exactly. -/
lemma uniformAverage_restrict {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ι → Type*) [∀ i, Fintype (β i)] [∀ i, Nonempty (β i)] (S : Finset ι)
    (f : (∀ i : S, β i) → ℝ) :
    uniformAverage (fun x : ∀ i, β i => f (fun i : S => x i)) = uniformAverage f := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) β
  calc
    _ = uniformAverage (fun x : (∀ i : S, β i) × (∀ i : {i // i ∉ S}, β i) => f x.1) :=
      uniformAverage_equiv e (fun x => f x.1)
    _ = uniformAverage f := by
      rw [uniformAverage_prod (fun (x : ∀ i : S, β i)
        (_y : ∀ i : {i // i ∉ S}, β i) => f x)]
      simp only [uniformAverage_const]

lemma abs_uniformAverage_le_one {α : Type*} [Fintype α] (f : α → ℝ)
    (hf : ∀ x, |f x| ≤ 1) : |uniformAverage f| ≤ 1 := by
  unfold uniformAverage
  rw [abs_div, show |(Fintype.card α : ℝ)| = (Fintype.card α : ℝ) from
    abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    |∑ x, f x| / (Fintype.card α : ℝ) ≤
        (∑ x, |f x|) / (Fintype.card α : ℝ) :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)
    _ ≤ (∑ _x : α, (1 : ℝ)) / (Fintype.card α : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => hf x)) (Nat.cast_nonneg _)
    _ ≤ 1 := by simp [div_self_le_one]

/-- Grouping an interval average by its actual CRT residue vector. -/
lemma crtJointProbability_expectation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ZMod (∏ i, s i)) (N : ℕ) (F : (∀ i, ZMod (s i)) → ℝ) :
    (∑ r, crtJointProbability s hcop A N r * F r) =
      uniformAverage (fun j : Fin N =>
        F (ZMod.prodEquivPi s hcop (A + (j.val : ZMod (∏ i, s i))))) := by
  simp_rw [crtJointProbability_eq_count, div_mul_eq_mul_div, Finset.sum_mul]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  unfold uniformAverage
  rw [Fintype.card_fin]
  congr 1
  exact (Fin.sum_univ_eq_sum_range
    (fun j : ℕ => F (ZMod.prodEquivPi s hcop (A + (j : ZMod (∏ i, s i))))) N).symm

lemma crtUniform_expectation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)] (F : (∀ i, ZMod (s i)) → ℝ) :
    (∑ r, crtUniform s r * F r) = uniformAverage F := by
  unfold crtUniform uniformAverage
  rw [← Finset.mul_sum]
  simp only [Fintype.card_pi, ZMod.card, Nat.cast_prod]
  ring

/-- Uniform translated interval averages of any bounded observable of the
selected residue coordinates differ from the product law by at most `D/N`. -/
theorem crt_observable_difference {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ZMod (∏ i, s i)) (N : ℕ) (hN : 0 < N)
    (F : (∀ i, ZMod (s i)) → ℝ) (hF : ∀ r, |F r| ≤ 1) :
    |uniformAverage (fun j : Fin N =>
        F (ZMod.prodEquivPi s hcop (A + (j.val : ZMod (∏ i, s i))))) -
      uniformAverage F| ≤ (∏ i, s i : ℕ) / (N : ℝ) := by
  have h := finite_observable_difference (crtJointProbability s hcop A N) (crtUniform s) F hF
  rw [crtJointProbability_expectation, crtUniform_expectation] at h
  calc
    _ ≤ 2 * finiteTotalVariation (crtJointProbability s hcop A N) (crtUniform s) := h
    _ = 2 * residueTotalVariation A N := by rw [crtJointProbability_totalVariation]
    _ ≤ 2 * ((∏ i, s i : ℕ) / (2 * (N : ℝ))) :=
      mul_le_mul_of_nonneg_left (residueTotalVariation_le A N hN) (by norm_num)
    _ = _ := by ring

end TwoPointCorrelations

end OAI
