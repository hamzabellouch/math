import OAI.Probability.InvariantIsing.Cavity.OffsetBlockSpin
import OAI.Probability.InvariantIsing.Magnetic.RestrictedFullSpinAverage
import OAI.Probability.InvariantIsing.Cavity.CavityOverlapWeightedTest

namespace OAI

/-! The last-block spin average differs from the full overlap only by the
fixed prefix's proportion. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction
namespace InvariantIsing

theorem offset_product_spin_error {n K r m depth : ℕ}
    (hn : 0 < n) (hK : 2 ≤ K) (R : Finset (Spin r)) (hR : R.Nonempty)
    (C : Finset (Spin n)) (hC : C.Nonempty)
    (μ : Measure (SpecialOrthogonal (r+K*n+n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin (r+K*n+n) → ℝ)
    (I : Fin m → Finset (Fin (r+K*n+n))) (u : ℕ → ℝ) (hu : ∀ k, |u k| ≤ 2)
    (Φ : ℝ →ᵇ ℝ) :
    |restrictedFullTest (cavityProductSlice (offsetBlockConstraint K R C) C)
      (cavityProductSlice_nonempty _ (offsetBlockConstraint_nonempty R hR C hC) C hC)
      μ T eig I u (fun σ => Φ (cavityReplicaOverlap σ) * ((n : ℝ)⁻¹ * ∑ i : Fin n,
        spinValue ((σ 0).1 (Fin.natAdd (r+K*n) i)) * spinValue ((σ 1).1 (Fin.natAdd (r+K*n) i)))) -
      restrictedFullTest (cavityProductSlice (offsetBlockConstraint K R C) C)
      (cavityProductSlice_nonempty _ (offsetBlockConstraint_nonempty R hR C hC) C hC)
      μ T eig I u (cavityFullOverlapInsertion (cavityOverlapWeightedTest Φ))| ≤
      ‖Φ‖*(2*(r : ℝ)/(r+K*n+n)) := by
  let P := fun (N : ℕ) (S : Finset (Spin N)) => ∀ (hS : S.Nonempty)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : ℕ → ℝ), (∀ k, |u k| ≤ 2) → ∀ (site : Fin n → Fin N),
    (∀ i, (site i).val=r+K*n+i.val) →
    |restrictedFullTest S hS μ T eig I u (fun σ => Φ (cavityReplicaOverlap σ) *
      ((n : ℝ)⁻¹ * ∑ i, spinValue ((σ 0).1 (site i))*spinValue ((σ 1).1 (site i)))) -
      restrictedFullTest S hS μ T eig I u (cavityFullOverlapInsertion (cavityOverlapWeightedTest Φ))| ≤
      ‖Φ‖*(2*(r : ℝ)/N)
  have hP : P (r+(K+1)*n) (offsetBlockConstraint (K+1) R C) := by
    intro hS μ hμ hμr T eig I u hu site hs
    have he : site=fun i => Fin.natAdd r (finProdFinEquiv (Fin.last K,i)) := by
      funext i
      apply Fin.ext
      rw [hs]
      change r+K*n+i.val=r+(i.val+n*K)
      simp [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]
    rw [he]
    have hw : (cavityFullOverlapInsertion (cavityOverlapWeightedTest Φ) :
        (Fin 2 → Spin (r+(K+1)*n) × LabeledLeaf depth) → ℝ)=
        (fun σ => Φ (cavityReplicaOverlap σ)*cavityReplicaOverlap σ) := by
      funext σ
      exact cavityOverlapWeightedTest_eq Φ (abs_le.mp (abs_cavityTotalSpinOverlap_le _))
    rw [hw]
    simpa only [restrictedFullTest, Nat.cast_add, Nat.cast_mul] using
      offset_block_spin_error hn (by omega : 3≤K+1) C hC R hR μ T eig I u hu Φ (Fin.last K)
  rw [offset_spin_family_succ P K R C] at hP
  simpa only [Nat.cast_add, Nat.cast_mul] using
    hP _ μ T eig I u hu (Fin.natAdd (r+K*n)) (fun _ => rfl)

end InvariantIsing

end

end OAI
