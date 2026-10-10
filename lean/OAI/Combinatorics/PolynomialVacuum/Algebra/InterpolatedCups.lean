import OAI.Combinatorics.PolynomialVacuum.Algebra.CupSlidePolynomial
import OAI.Combinatorics.PolynomialVacuum.Algebra.LastDegrees

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

 

theorem interpolateState_firstCup {n : ℕ} (ψ : State (n+2)) (χ : State (n+3))
    (φ δ : NatSpectralTensor)
    (hex : LowerExchange (liftState ψ) (n+2))
    (hnode : NaturalCupNodes (liftState ψ) φ n)
    (hcψ : FirstCupReduction (liftState ψ) φ n)
    (hzψ : LastZeroReduction (liftState ψ) δ (n+1))
    (hcχ : FirstCupReduction (liftState χ) δ (n+1))
    (hdψ : ∀ s, (ψ s).degreeOf (Fin.last (n+1)) ≤ n+1)
    (hfψ : ∀ s, s (Fin.last (n+1))=Spin.plus → (ψ s).degreeOf (Fin.last (n+1)) ≤ n) :
    FirstCupReduction (liftState (interpolateState ψ χ)) (liftState ψ) (n+2) := by
  apply firstCup_of_nodes
  · intro s
    exact (interpolateState_last_degrees ψ χ s).1
  · intro s
    exact (interpolateState_last_degrees ψ χ s).2
  · exact hdψ
  · exact hfψ
  · exact firstCup_node_equality _ ψ φ (lift_interpolate_cupNodes ψ χ hex) hnode hex hcψ
  · exact firstCup_zeroNode (interpolateState_lastZero ψ χ) hzψ hcχ

theorem naturalPrescription_last_cup {n : ℕ} (ψ : State n) (X : ℕ → ℂ) :
    naturalPrescription (liftState ψ) n n X=
      naturalFusion n n X • cupLinear n (liftState ψ (skipTwo n X)) := by
  have hp : liftState ψ (skipOne n X)=liftState ψ (skipTwo n X) := by
    apply liftState_params_congr
    intro j hj
    simp [skipOne,skipTwo,hj]
  have hf : leftFusion n X=fusionProduct (X n) (skipTwo n X) n := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [skipTwo,Finset.mem_range.mp hj]
  simp only [naturalPrescription,Nat.sub_self,braidTrain,one_mul,hp,naturalFusion,hf]

theorem interpolateState_all_cups {n : ℕ} (ψ : State n) (χ : State (n+1))
    (hexψ : LowerExchange (liftState ψ) n)
    (hexχ : LowerExchange (liftState χ) (n+1))
    (hc : FirstCupReduction (liftState (interpolateState ψ χ)) (liftState ψ) n) :
    ∀ i, i≤n → CupAt (liftState (interpolateState ψ χ)) (liftState ψ) n i := by
  intro i hi
  rcases lt_or_eq_of_le hi with hi | he
  · exact cupAt_of_first _ ψ (interpolateState_first_exchanges ψ χ hexψ hexχ) hc i hi
  · subst i
    intro X hX
    rw [interpolateState_node_natural ψ χ hexψ n le_rfl X hX,naturalPrescription_last_cup]

end PolynomialVacuumAlgebra

end OAI
