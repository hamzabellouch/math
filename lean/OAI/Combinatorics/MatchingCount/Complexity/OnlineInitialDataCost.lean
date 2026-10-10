import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.OnlineInitialCost

namespace OAI

namespace MatchingFPRAS.OnlineInitial
open TreeTyped TreeFraction OnlineSchedule Polynomial NumericBounds ExecutableSource ExecutableScaling

lemma work_data : WorkBound dataRealizer configSize := by
  have lift {A : Type} [Codec A] {f : Config→A} {F : Realizer f} (hF : PolynomialTime F) :
      WorkBound F configSize := work_of_polynomial hF X (fun x=>by simpa using weight_configSize x)
  have wb : ∀ x : Config,weight x≤X.eval (configSize x) := fun x=>by simpa using weight_configSize x
  have _workK : WorkBound (first.snd : Realizer (fun x : Config=>x.1.2)) configSize := lift (by unfold Realizer.snd; tree_cost)
  have hk : Bound (fun x : Config=>x.1.2) configSize := of_le (fun x=>(config_fields x).2.1)
  have hN : Bound (fun x : Config=>x.2.1) configSize := of_le (fun x=>(config_fields x).2.2.1)
  have hD : Bound (fun x : Config=>x.2.2) configSize := of_le (fun x=>(config_fields x).2.2.2.1)
  have hT : Bound (fun x : Config=>ladderSchedule (x.2,x.1.2)) configSize := of_le (fun x=>(config_fields x).2.2.2.2.1)
  have hq : Bound (fun x : Config=>Transport.ladderQ x.2.1 x.2.2) configSize := of_le (fun x=>(config_fields x).2.2.2.2.2)
  unfold dataRealizer Realizer.fst Realizer.snd
  apply work_congr
  apply work_pair _ _ X wb
  · apply work_pair _ _ X wb
    · exact lift (by tree_cost)
    · apply work_pair _ _ X wb
      · apply work_pair _ (lift (by tree_cost)) X wb
        apply work_pair _ _ X wb
        · apply work_comp_bound (lift (by apply polynomial_addNat (polynomial_mulNat (polynomial_constant _) (by tree_cost)) (polynomial_constant _))) fuel_numeric_work
          exact add (mul (const 2 _) hk) (const 2 _)
        · apply work_comp_bound (lift (by apply polynomial_mulNat (polynomial_constant _) (by tree_cost))) fuel_numeric_work
          exact mul (const 2 _) hk
      · apply work_pair _ _ X wb
        · apply work_comp_bound _ fuel_numeric_work hT
          apply work_comp_bound (lift (by tree_cost)) work_ladderSchedule
          exact add (add (add hN hD) hk) (NumericBounds.weight (lift (by tree_cost)))
        · apply work_comp_bound (lift (polynomial_composition polynomial_second polynomial_q)) fuel_numeric_work hq
  · exact lift (polynomial_composition (by tree_cost) polynomial_scaleVector)

lemma work_trialInput : WorkBound trialInputRealizer configSize := by
  have lift {A : Type} [Codec A] {f : Config→A} {F : Realizer f} (hF : PolynomialTime F) :
      WorkBound F configSize := work_of_polynomial hF X (fun x=>by simpa using weight_configSize x)
  have wb : ∀ x : Config,weight x≤X.eval (configSize x) := fun x=>by simpa using weight_configSize x
  unfold trialInputRealizer Realizer.snd
  apply work_pair _ _ X wb
  · exact work_comp_bound (lift (by tree_cost)) fuel_numeric_work (of_le (fun x=>(config_fields x).2.1))
  · apply work_pair _ _ X wb
    · exact work_pair work_data (lift polynomial_count) X wb
    · apply work_pair _ (lift (polynomial_constant _)) X wb
      apply work_comp_bound (lift (by unfold nRealizer Realizer.fst;tree_cost)) pairingNumber_numeric_work
      exact of_le (fun x=>(config_fields x).1)
lemma work_runInput : WorkBound runInputRealizer configSize := by
  unfold runInputRealizer Realizer.fst Realizer.snd
  apply work_congr
  apply work_pair _ work_trialInput X (fun x=>by simpa using weight_configSize x)
  apply work_of_polynomial (polynomial_composition (by tree_cost) polynomial_repetitions) X
  exact fun x=>by simpa using weight_configSize x
lemma work_initializeInput : WorkBound initializeInputRealizer seedSize :=
  work_comp_bound work_config work_runInput bound_configSize
end MatchingFPRAS.OnlineInitial

end OAI
