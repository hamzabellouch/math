import OAI.Analysis.Laughlin.FourBody.CoefficientLimit

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem physicalPairCoupling_antisymmetric (Q r j k : ℕ) (ho : Odd r) :
    physicalCouplingCoefficient Q Q r (j+k) k =
      -physicalCouplingCoefficient Q Q r (j+k) j := by
  by_cases h : r ≤ j+k ∧ j+k ≤ Q
  · have h1 : r ≤ j+k ∧ k ≤ j+k ∧ j+k ≤ Q ∧ j+k ≤ Q := by omega
    have h2 : r ≤ j+k ∧ j ≤ j+k ∧ j+k ≤ Q ∧ j+k ≤ Q := by omega
    rw [physicalCouplingCoefficient,dite_eq_left h1,physicalCouplingCoefficient,dite_eq_left h2]
    have hj : j+k-k=j := by omega
    have hk : j+k-j=k := by omega
    simp only [hj,hk]
    exact pairCoupledTensor_antisymmetric Q r (j+k-r) (by omega) ho
      ⟨j,by omega⟩ ⟨k,by omega⟩
  · have h1 : ¬(r ≤ j+k ∧ k ≤ j+k ∧ j+k ≤ Q ∧ j+k ≤ Q) := by omega
    have h2 : ¬(r ≤ j+k ∧ j ≤ j+k ∧ j+k ≤ Q ∧ j+k ≤ Q) := by omega
    simp only [physicalCouplingCoefficient,dite_eq_right h1,dite_eq_right h2,neg_zero]

theorem fourBodyCoefficient_antisymmetric (Q r D T p j k : ℕ) (ho : Odd r) :
    fourBodyCoefficient Q r D T p k j = -fourBodyCoefficient Q r D T p j k := by
  unfold fourBodyCoefficient
  rw [Nat.add_comm k j]
  by_cases hr : r ≤ j+k
  · rw [ite_eq_left hr,ite_eq_left hr,physicalPairCoupling_antisymmetric Q r j k ho]
    ring
  · rw [ite_eq_right hr,ite_eq_right hr,neg_zero]

theorem fourBodyLimitCoefficient_antisymmetric (r D T p j k : ℕ) (ho : Odd r)
    (hrD : r ≤ D) (hDT : D ≤ T) (hT : p+j+k=T) :
    fourBodyLimitCoefficient r D T p k j = -fourBodyLimitCoefficient r D T p j k := by
  apply tendsto_nhds_unique (source_fourBody_coefficient_tendsto r D T p k j hrD hDT (by omega))
  have h := (source_fourBody_coefficient_tendsto r D T p j k hrD hDT hT).neg
  apply h.congr
  intro Q
  exact (fourBodyCoefficient_antisymmetric Q r D T p j k ho).symm

end Laughlin.Spin

end OAI
