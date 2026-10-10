import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSquareProbabilityAverage

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryPairSquareProbability
open HistoryCRTIntegration PrimeSquareResidueLaw

lemma probability_pair_equiv {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (e : α×β≃γ) (P : γ→Prop) :
    probability P=rmean (fun a => probability (fun b => P (e (a,b)))) := by
  rw [probability_eq_rmean,←rmean_equiv e,rmean_prod]
  simp only [probability_eq_rmean]

variable {ι : Type*} (p : ℕ) [Fact p.Prime] (s : Finset ι) (A B : ι→ℤ)

def unitBaseProbability : ℝ := probability (fun z : UnitPair p =>
  Base p s A B (((z.1:ZMod p).val:ℤ)) (((z.2:ZMod p).val:ℤ)))
def mixedBaseProbability : ℝ := probability (fun z : MixedPair p =>
  Base p s A B ((z.1.val:ℤ)) (((z.2:ZMod p).val:ℤ)))
def unitGoodProbability : ℝ := probability (fun z : UnitPair (p^2) =>
  Good p s A B (((z.1:ZMod (p^2)).val:ℤ)) (((z.2:ZMod (p^2)).val:ℤ)))
def mixedGoodProbability : ℝ := probability (fun z : MixedPair (p^2) =>
  Good p s A B ((z.1.val:ℤ)) (((z.2:ZMod (p^2)).val:ℤ)))

lemma unit_good_eq_lift_average :
    unitGoodProbability p s A B=rmean (fun a : UnitPair p =>
      probability (fun z : ZMod p×ZMod p =>
        Good p s A B (((a.1:ZMod p).val:ℤ)+(p:ℤ)*(z.1.val:ℤ))
          (((a.2:ZMod p).val:ℤ)+(p:ℤ)*(z.2.val:ℤ)))) := by
  unfold unitGoodProbability
  rw [probability_pair_equiv (unitPairLiftEquiv p)]
  simp only [unitPairLiftEquiv_fst,unitPairLiftEquiv_snd,lift_val,Nat.cast_add,Nat.cast_mul]

lemma mixed_good_eq_lift_average :
    mixedGoodProbability p s A B=rmean (fun a : MixedPair p =>
      probability (fun z : ZMod p×ZMod p =>
        Good p s A B ((a.1.val:ℤ)+(p:ℤ)*(z.1.val:ℤ))
          (((a.2:ZMod p).val:ℤ)+(p:ℤ)*(z.2.val:ℤ)))) := by
  unfold mixedGoodProbability
  rw [probability_pair_equiv (mixedPairLiftEquiv p)]
  simp only [mixedPairLiftEquiv_fst,mixedPairLiftEquiv_snd,lift_val,Nat.cast_add,Nat.cast_mul]

theorem unit_square_loss
    (hrow : ∀i∈s,(A i:ZMod p)≠0 ∨ (B i:ZMod p)≠0) :
    0 ≤ unitBaseProbability p s A B-unitGoodProbability p s A B ∧
    unitBaseProbability p s A B-unitGoodProbability p s A B ≤ 
      ((s.card:ℝ)/p)*unitBaseProbability p s A B := by
  rw [unit_good_eq_lift_average]
  exact base_average_lift_loss p s A B
    (fun a : UnitPair p => ((a.1:ZMod p).val:ℤ))
    (fun a : UnitPair p => ((a.2:ZMod p).val:ℤ)) hrow

theorem mixed_square_loss
    (hrow : ∀i∈s,(A i:ZMod p)≠0 ∨ (B i:ZMod p)≠0) :
    0 ≤ mixedBaseProbability p s A B-mixedGoodProbability p s A B ∧
    mixedBaseProbability p s A B-mixedGoodProbability p s A B ≤ 
      ((s.card:ℝ)/p)*mixedBaseProbability p s A B := by
  rw [mixed_good_eq_lift_average]
  exact base_average_lift_loss p s A B
    (fun a : MixedPair p => (a.1.val:ℤ))
    (fun a : MixedPair p => ((a.2:ZMod p).val:ℤ)) hrow

end Ostmann.Arithmetic.HistoryPairSquareProbability

end

end OAI
