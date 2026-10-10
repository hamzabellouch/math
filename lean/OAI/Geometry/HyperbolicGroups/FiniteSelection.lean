import Mathlib
import OAI.Geometry.HyperbolicGroups.GeometricAction
import OAI.Geometry.HyperbolicGroups.Random
import OAI.Geometry.HyperbolicGroups.StarError

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace FiniteLaw
variable {α β J : Type*} [Fintype α] [Fintype β] [Fintype J]

/-- All finite tests and any additional table event can be imposed at once.
The only premise is the actual expectation/probability estimate, not the
existence of a good table. -/
theorem exists_good_simultaneously (μ : FiniteLaw α) (f : J → α → ℝ)
    (hf : ∀ j a, 0 ≤ f j a) (bad : α → Prop) [DecidablePred bad]
    {ε : ℝ} (hε : 0 < ε)
    (h : (∑ j, μ.expect (f j)) + ε*μ.prob bad < ε) :
    ∃ a, ¬bad a ∧ ∀ j, f j a < ε := by
  let F (a : α) := (∑ j, f j a) + ε*(if bad a then 1 else 0)
  have he : μ.expect F < ε := by
    dsimp [F]
    rw [μ.expect_add,μ.expect_sum,μ.expect_mul]
    exact h
  obtain ⟨a,ha⟩ := μ.exists_lt_of_expect_lt F ε he
  have hs : 0 ≤ ∑ j, f j a := Finset.sum_nonneg fun j _ => hf j a
  have hb : ¬bad a := by
    intro hb
    dsimp [F] at ha
    simp only [hb,↓reduceIte,mul_one] at ha
    linarith
  refine ⟨a,hb,fun j => ?_⟩
  have hj : f j a ≤ ∑ j, f j a :=
    Finset.single_le_sum (fun j _ => hf j a) (Finset.mem_univ j)
  have hind : 0 ≤ ε * (if bad a then 1 else 0) :=
    mul_nonneg hε.le (by split_ifs; norm_num)
  exact (hj.trans (le_add_of_nonneg_right hind)).trans_lt ha

/-- Product law for the independent master and six-letter arrays. -/
def prod (μ : FiniteLaw α) (ν : FiniteLaw β) : FiniteLaw (α × β) where
  mass a := μ.mass a.1 * ν.mass a.2
  nonneg a := mul_nonneg (μ.nonneg _) (ν.nonneg _)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum,ν.sum_one,mul_one]
    exact μ.sum_one

lemma expect_prod (μ : FiniteLaw α) (ν : FiniteLaw β) (f : α × β → ℝ) :
    (μ.prod ν).expect f = μ.expect (fun a => ν.expect (fun b => f (a,b))) := by
  unfold expect prod
  simp only [Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma expect_prod_fst (μ : FiniteLaw α) (ν : FiniteLaw β) (f : α → ℝ) :
    (μ.prod ν).expect (fun a => f a.1) = μ.expect f := by
  rw [expect_prod]
  simp only [expect_const]

lemma expect_prod_snd (μ : FiniteLaw α) (ν : FiniteLaw β) (f : β → ℝ) :
    (μ.prod ν).expect (fun a => f a.2) = ν.expect f := by
  rw [expect_prod]
  change μ.expect (fun _ => ν.expect f) = _
  exact μ.expect_const _

end FiniteLaw
end HyperbolicObstruction
end
end

section

end
end

end OAI
