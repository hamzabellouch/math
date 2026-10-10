import OAI.Combinatorics.PolynomialVacuum.Algebra.NaturalCandidateEndpoints
import OAI.Combinatorics.PolynomialVacuum.Algebra.FirstCupRegularNode

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

def NaturalCupNodes (Ψ ψ : NatSpectralTensor) (n : ℕ) : Prop :=
  ∀ X i, i ≤ n → X (n+1)=T*X i → Ψ X=naturalPrescription ψ n i X

theorem lift_interpolate_cupNodes {n : ℕ} (ψ : State n) (χ : State (n+1))
    (hψ : LowerExchange (liftState ψ) n) :
    NaturalCupNodes (liftState (interpolateState ψ χ)) (liftState ψ) n := by
  intro X i hi hX
  exact interpolateState_node_natural ψ χ hψ i hi X hX

theorem naturalFusion_first_congr (n : ℕ) (X Y : ℕ → ℂ)
    (h : ∀ j < n+2, X j=Y j) : naturalFusion n 0 X=naturalFusion n 0 Y := by
  simp only [naturalFusion,h 0 (by omega),fusionProduct,skipTwo_zero_apply]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [h (k+2) (by have:=Finset.mem_range.mp hk; omega)]

theorem insertOne_at_node_congr {α : Type*} (n : ℕ) (c : α) (X : ℕ → α)
    (hX : X n=c) (j : ℕ) (hj : j < n+1) : insertOne n c X j=X j := by
  by_cases h : j < n
  · simp [insertOne,h]
  · have : j=n := by omega
    subst j
    simp [hX]

theorem firstCup_node_equality {n : ℕ} (Ψ : NatSpectralTensor) (ψ : State (n+2))
    (φ : NatSpectralTensor)
    (hΨ : NaturalCupNodes Ψ (liftState ψ) (n+2))
    (hψ : NaturalCupNodes (liftState ψ) φ n)
    (hex : LowerExchange (liftState ψ) (n+2))
    (hcup : FirstCupReduction (liftState ψ) φ n)
    (X : ℕ → ℂ) (hX : X 1=T*X 0) (i : ℕ) (hi : i ≤ n+2)
    (hnode : X (n+3)=T*X i) :
    Ψ X=naturalFusion (n+2) 0 X • cupLinear 0 (liftState ψ (skipTwo 0 X)) := by
  rw [hΨ X i hi hnode]
  have hf : naturalFusion (n+2) 0 (insertOne (n+3) (T*X i) X)=naturalFusion (n+2) 0 X :=
    naturalFusion_first_congr _ _ _ (insertOne_at_node_congr _ _ _ hnode)
  have hp : liftState ψ (skipTwo 0 (insertOne (n+3) (T*X i) X))=liftState ψ (skipTwo 0 X) := by
    apply liftState_params_congr
    intro j hj
    simpa using insertOne_at_node_congr (n+3) (T*X i) X hnode (j+2) (by omega)
  rcases i with _|(_|j)
  · rw [naturalPrescription_firstCup_regular hex X hX,hf,hp]
  · rw [naturalPrescription_firstCup_middle _ _ X hX]
    have hz : naturalFusion (n+2) 0 X=0 := by
      simp only [naturalFusion,fusionProduct]
      suffices hh : (∏ k ∈ Finset.range (n+2), fusionPair (X 0) (skipTwo 0 X k))=0 by rw [hh,mul_zero]
      apply Finset.prod_eq_zero (Finset.mem_range.mpr (by omega : n+1 < n+2))
      simpa only [skipTwo_zero_apply,show n+1+2=n+3 by omega,hnode,hX] using fusionPair_second_successor_zero (X 0)
    rw [hz,zero_smul]
  · rw [naturalPrescription_firstCup_after hcup j (by omega) X hX,hf]
    rw [hψ (skipTwo 0 X) j (by omega) (by simpa only [skipTwo_zero_apply,show n+1+2=n+3 by omega] using hnode)]

end PolynomialVacuumAlgebra

end OAI
