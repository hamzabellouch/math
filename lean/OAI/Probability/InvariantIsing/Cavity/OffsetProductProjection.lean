import OAI.Probability.InvariantIsing.Cavity.OffsetBlockProjection
import OAI.Probability.InvariantIsing.Cavity.CavityFullTail

namespace OAI

/-! Projection moments for the last block with a fixed initial remainder. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

theorem offset_product_projection_mean_le {n K r m depth : ℕ}
    (hn : 0 < n) (hK : 2 ≤ K) (R : Finset (Spin r)) (hR : R.Nonempty)
    (C : Finset (Spin n)) (hC : C.Nonempty)
    (μ : Measure (SpecialOrthogonal (r+K*n+n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin (r+K*n+n) → ℝ)
    (I : Fin m → Finset (Fin (r+K*n+n))) (u : ℕ → ℝ) (hu : ∀ k, |u k| ≤ 2)
    (J : Finset (Fin (r+K*n+n))) (i : Fin n) :
    restrictedCavityFullDisorderTest (cavityProductSlice (offsetBlockConstraint K R C) C)
      (cavityProductSlice_nonempty _ (offsetBlockConstraint_nonempty R hR C hC) C hC)
      μ T eig I u (cavityProjectionSiteTest J (Fin.natAdd (r+K*n) i)) ≤ (r : ℝ)+n := by
  let P := fun (N : ℕ) (S : Finset (Spin N)) => ∀ (hS : S.Nonempty)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : ℕ → ℝ), (∀ k, |u k| ≤ 2) → ∀ (site : Fin n → Fin N),
    (∀ i, (site i).val=r+K*n+i.val) → ∀ (J : Finset (Fin N)) (i : Fin n),
    restrictedCavityFullDisorderTest S hS μ T eig I u (cavityProjectionSiteTest J (site i)) ≤ (r : ℝ)+n
  have hP : P (r+(K+1)*n) (offsetBlockConstraint (K+1) R C) := by
    intro hS μ hμ hμr T eig I u hu site hs J i
    have he : site i=Fin.natAdd r (finProdFinEquiv (Fin.last K,i)) := by
      apply Fin.ext
      rw [hs]
      change r+K*n+i.val=r+(i.val+n*K)
      simp [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]
    rw [he]
    have hb := offset_block_projection_mean_le hn (by omega : 3≤K+1) C hC R hR μ T eig I u hu J i (Fin.last K)
    apply hb.trans
    apply (div_le_iff₀ (Nat.cast_pos.mpr (by omega : 0<K+1))).mpr
    push_cast
    have hk : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    nlinarith [mul_nonneg hk hr]
  rw [offset_spin_family_succ P K R C] at hP
  exact hP _ μ T eig I u hu (Fin.natAdd (r+K*n)) (fun _ => rfl) J i

theorem offset_product_last_axes_mean {n K r m depth : ℕ}
    (hn : 0 < n) (hK : 2 ≤ K) (R : Finset (Spin r)) (hR : R.Nonempty)
    (C : Finset (Spin n)) (hC : C.Nonempty)
    (μ : Measure (SpecialOrthogonal (r+K*n+n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin (r+K*n+n) → ℝ)
    (I : Fin m → Finset (Fin (r+K*n+n))) (u : ℕ → ℝ) (hu : ∀ k, |u k| ≤ 2) :
    restrictedCavityFullDisorderTest (cavityProductSlice (offsetBlockConstraint K R C) C)
      (cavityProductSlice_nonempty _ (offsetBlockConstraint_nonempty R hR C hC) C hC)
      μ T eig I u (cavityProjectionAxesTest I (Fin.natAdd (r+K*n))) ≤ (m : ℝ)*n*(r+n) := by
  change restrictedCavityFullDisorderTest _ _ μ T eig I u
    (fun U σ => ∑ t : Fin m × Fin n,
      cavityProjectionSiteTest (I t.1) (Fin.natAdd (r+K*n) t.2) U σ) ≤ _
  rw [restrictedCavityFullDisorderTest_sum _ _ μ T eig I u
    (fun t : Fin m × Fin n => cavityProjectionSiteTest (I t.1) (Fin.natAdd (r+K*n) t.2))
    (fun _ => measurable_cavityProjectionSiteTest _ _) (Nat.cast_nonneg (r+K*n+n))
    (fun _ => cavityProjectionSiteTest_bound _ _)]
  calc
    _ ≤ ∑ _ : Fin m × Fin n, ((r : ℝ)+n) := Finset.sum_le_sum fun t _ =>
      offset_product_projection_mean_le hn hK R hR C hC μ T eig I u hu (I t.1) t.2
    _ = _ := by simp [Fintype.card_prod, Nat.cast_mul]; ring

end InvariantIsing

end

end OAI
