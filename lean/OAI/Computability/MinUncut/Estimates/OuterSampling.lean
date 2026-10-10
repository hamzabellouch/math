import Mathlib
import OAI.Computability.MinUncut.PCP.SelectionSequence

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncutGames.Foundations.Games
attribute [local instance] Classical.propDecidable
variable {Name S : Type*} [Fintype Name] [Fintype S] [Nonempty S]

lemma ordinary_repetition_formula (equations : S → Equation Name) (r : ℕ)
    (strategy : Strategy (Fin r → Equation Name) (Fin r → Name)
      (Fin r → Triple) (Fin r → F₂)) :
    ((ordinaryGame equations).repetition r).success strategy =
      𝔼 w : Fin r → S × Fin 3,
        if (∀ j, ordinaryAccepts (equations (w j).1)
          ((equations (w j).1).names (w j).2)
          (strategy.1 (fun i => equations (w i).1) j)
          (strategy.2 (fun i => (equations (w i).1).names (w i).2) j)=true)
        then (1 : ℝ) else 0 := by
  unfold Game.success
  change (((ordinaryGame equations).questions.iid r).transport
    (Game.tupleQuestionEquiv r)).probability _ = _
  rw [FiniteDistribution.probability_transport]
  change (((FiniteDistribution.uniform (S × Fin 3)).pushforward
    (fun ip => (equations ip.1,(equations ip.1).names ip.2))).iid r).probability _ = _
  rw [FiniteDistribution.iid_pushforward,FiniteDistribution.iid_uniform,
    FiniteDistribution.probability_pushforward]
  change (∑ w : Fin r → S × Fin 3,
    if decide (∀ j, ordinaryAccepts (equations (w j).1)
      ((equations (w j).1).names (w j).2)
      (strategy.1 (fun i => equations (w i).1) j)
      (strategy.2 (fun i => (equations (w i).1).names (w i).2) j)=true)
    then (1 : ℝ) / Fintype.card (Fin r → S × Fin 3) else 0) = _
  simp only [decide_eq_true_eq,Fintype.expect_eq_sum_div_card,Finset.sum_div,ite_div,zero_div]

theorem ordinary_repetition_on (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s ≤ 3/4)
    {J : Type*} [Fintype J]
    (a : (J → Equation Name) → J → Triple) (b : (J → Name) → J → F₂) :
    (𝔼 w : J → S × Fin 3,
      if (∀ j, ordinaryAccepts (equations (w j).1)
        ((equations (w j).1).names (w j).2)
        (a (fun i => equations (w i).1) j)
        (b (fun i => (equations (w i).1).names (w i).2) j)=true)
      then (1 : ℝ) else 0) ≤ repetitionRate ^ Fintype.card J := by
  classical
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let strategy : Strategy (Fin (Fintype.card J) → Equation Name)
      (Fin (Fintype.card J) → Name) (Fin (Fintype.card J) → Triple)
      (Fin (Fintype.card J) → F₂) :=
    (fun x i => a (fun j => x (e.symm j)) (e i),
     fun y i => b (fun j => y (e.symm j)) (e i))
  have h := ordinary_repetition_success equations hsound (Fintype.card J) strategy
  rw [ordinary_repetition_formula] at h
  convert h using 1
  let ew : (J → S × Fin 3) ≃ (Fin (Fintype.card J) → S × Fin 3) :=
    Equiv.arrowCongr e.symm (Equiv.refl _)
  apply Fintype.expect_equiv ew
  intro w
  simp only [ew,Equiv.arrowCongr_apply,Equiv.coe_refl,Equiv.symm_symm,
    strategy,Function.comp_apply,id_eq,Equiv.apply_symm_apply]
  congr 1
  exact propext e.forall_congr_right.symm

end MinUncut.Outer

end
end

end OAI
