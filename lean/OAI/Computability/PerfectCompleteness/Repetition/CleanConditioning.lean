import OAI.Computability.PerfectCompleteness.Foundations.FiniteProduct
import OAI.Computability.UniqueGames.Foundations.Conditioning
import OAI.Computability.UniqueGames.Games.FinishBoundsLemmas

namespace OAI


namespace PerfectCompleteness.CleanConditioning

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open FiniteProduct

noncomputable section

section Product

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

def allEvent (event : (i : I) → Ω i → Bool) (x : (i : I) → Ω i) : Bool :=
  decide (∀ i, event i (x i) = true)

omit [DecidableEq I] in
theorem product_filter (a : I → ℝ) (event : I → Bool) :
    (if ∀ i, event i = true then ∏ i, a i else 0) =
      ∏ i, if event i then a i else 0 := by
  classical
  by_cases h : ∀ i, event i = true
  · simp [h]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem probability_law_all (P : (i : I) → FiniteDistribution (Ω i))
    (event : (i : I) → Ω i → Bool) :
    (law P).probability (allEvent event) = ∏ i, (P i).probability (event i) := by
  classical
  unfold FiniteDistribution.probability law allEvent
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [decide_eq_true_eq]
  exact product_filter (fun i => (P i).weight (x i)) (fun i => event i (x i))

theorem coordinate_probability_positive (P : (i : I) → FiniteDistribution (Ω i))
    (event : (i : I) → Ω i → Bool)
    (positive : 0 < (law P).probability (allEvent event)) (i : I) :
    0 < (P i).probability (event i) := by
  have hne : (P i).probability (event i) ≠ 0 := by
    intro hz
    have hzprod : (∏ j, (P j).probability (event j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hz
    rw [probability_law_all, hzprod] at positive
    exact (lt_irrefl 0) positive
  exact lt_of_le_of_ne ((P i).probability_nonnegative _) hne.symm

theorem condition_law_all (P : (i : I) → FiniteDistribution (Ω i))
    (event : (i : I) → Ω i → Bool)
    (positive : 0 < (law P).probability (allEvent event)) :
    (law P).condition (allEvent event) positive =
      law (fun i => (P i).condition (event i)
        (coordinate_probability_positive P event positive i)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change (if allEvent event x then
      (∏ i, (P i).weight (x i)) / (law P).probability (allEvent event) else 0) =
    ∏ i, if event i (x i) then
      (P i).weight (x i) / (P i).probability (event i) else 0
  rw [← product_filter]
  simp only [allEvent, decide_eq_true_eq, probability_law_all,
    Finset.prod_div_distrib]

theorem pushforward_law {Γ : I → Type*} [∀ i, Fintype (Γ i)]
    (P : (i : I) → FiniteDistribution (Ω i)) (f : (i : I) → Ω i → Γ i) :
    (law P).pushforward (fun x i => f i (x i)) =
      law (fun i => (P i).pushforward (f i)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro y
  symm
  simp only [law, FiniteDistribution.pushforward]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : (fun i => f i (x i)) = y
  · have hp : ∀ i, f i (x i) = y i := congrFun h
    simp [hp]
  · rw [ite_eq_right h]
    have hn : ¬ ∀ i, f i (x i) = y i := fun hp => h (funext hp)
    obtain ⟨i, hi⟩ := not_forall.mp hn
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem condition_clean_mask (P : (i : I) → FiniteDistribution (Ω i))
    (clean : (i : I) → Ω i → Bool) (mask : I → Bool)
    (positive : 0 < (law P).probability
      (allEvent (fun i x => decide (clean i x = mask i)))) :
    (law P).condition (allEvent (fun i x => decide (clean i x = mask i))) positive =
      law (fun i => (P i).condition (fun x => decide (clean i x = mask i))
        (coordinate_probability_positive P _ positive i)) :=
  condition_law_all P _ positive

end Product


variable {E T R : Type*} [Fintype E] [Fintype T] [Fintype R]

def kernelJoint (μ : FiniteDistribution E) (kernel : E → FiniteDistribution T) :
    FiniteDistribution (E × T) where
  weight x := μ.weight x.1 * (kernel x.1).weight x.2
  nonnegative x := mul_nonneg (μ.nonnegative _) ((kernel x.1).nonnegative _)
  normalized := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, FiniteDistribution.normalized, mul_one]
    exact μ.normalized

theorem probability_kernelJoint (μ : FiniteDistribution E)
    (kernel : E → FiniteDistribution T) (event : E × T → Bool) :
    (kernelJoint μ kernel).probability event =
      ∑ e, μ.weight e * (kernel e).probability (fun t => event (e, t)) := by
  simp only [FiniteDistribution.probability, kernelJoint, Fintype.sum_prod_type,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro t _
  by_cases h : event (e, t) = true <;> simp [h]

theorem probability_kernelJoint_fiber [DecidableEq E] (μ : FiniteDistribution E)
    (kernel : E → FiniteDistribution T) (event : E × T → Bool) (e : E) :
    (kernelJoint μ kernel).probability
      (fun x => decide (x.1 = e) && event x) =
      μ.weight e * (kernel e).probability (fun t => event (e, t)) := by
  rw [probability_kernelJoint]
  rw [Finset.sum_eq_single e]
  · simp
  · intro e' _ hne
    simp [hne, FiniteDistribution.probability]
  · simp

theorem probability_kernelJoint_constant (μ : FiniteDistribution E)
    (kernel : E → FiniteDistribution T) (event : E × T → Bool) (p : ℝ)
    (constant : ∀ e, (kernel e).probability (fun t => event (e, t)) = p) :
    (kernelJoint μ kernel).probability event = p := by
  rw [probability_kernelJoint]
  simp_rw [constant]
  rw [← Finset.sum_mul, μ.normalized, one_mul]

theorem source_condition_of_constant [DecidableEq E] (μ : FiniteDistribution E)
    (kernel : E → FiniteDistribution T) (event : E × T → Bool) (p : ℝ)
    (constant : ∀ e, (kernel e).probability (fun t => event (e, t)) = p)
    (positive : 0 < (kernelJoint μ kernel).probability event) :
    ((kernelJoint μ kernel).condition event positive).pushforward Prod.fst = μ := by
  classical
  have hp : 0 < p := by
    rwa [probability_kernelJoint_constant μ kernel event p constant] at positive
  apply FiniteDistribution.eq_of_weight_eq
  intro e
  rw [FiniteDistribution.weight_eq_probability_singleton,
    FiniteDistribution.probability_pushforward, FiniteDistribution.probability_condition]
  have hevent : (fun x : E × T => event x && decide (x.1 = e)) =
      (fun x => decide (x.1 = e) && event x) := by
    funext x
    exact Bool.and_comm _ _
  rw [hevent, probability_kernelJoint_fiber, constant,
    probability_kernelJoint_constant μ kernel event p constant]
  exact mul_div_cancel_right₀ _ (ne_of_gt hp)

theorem designated_source_condition [DecidableEq E] [DecidableEq R]
    (μ : FiniteDistribution E) (ν : FiniteDistribution R)
    (kernel : E → R → FiniteDistribution T) (clean : E → R → T → Bool)
    (p : ℝ) (constant : ∀ e r, (kernel e r).probability (clean e r) = p)
    (record : R)
    (positive : 0 <
      (kernelJoint μ (fun e => kernelJoint ν (kernel e))).probability
        (fun x => decide (x.2.1 = record) && clean x.1 x.2.1 x.2.2)) :
    ((kernelJoint μ (fun e => kernelJoint ν (kernel e))).condition
      (fun x => decide (x.2.1 = record) && clean x.1 x.2.1 x.2.2) positive).pushforward
        Prod.fst = μ := by
  apply source_condition_of_constant μ _ _ (ν.weight record * p) _ positive
  intro e
  rw [probability_kernelJoint_fiber]
  rw [constant]


end
end PerfectCompleteness.CleanConditioning

end OAI
