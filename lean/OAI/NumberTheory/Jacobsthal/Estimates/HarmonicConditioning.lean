import OAI.NumberTheory.Jacobsthal.Paths.ActualSampleWitness

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseCells
open ErdosInverseSampling
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

noncomputable def harmonicMass (Q : Finset ℕ) : ℝ := ∑ q ∈ Q,(q : ℝ)⁻¹

noncomputable def tripleSpace (P Q U : Finset ℕ) : Finset ((ℕ × ℕ) × ℕ) := (P ×ˢ Q) ×ˢ U

noncomputable def tripleWeight (x : (ℕ × ℕ) × ℕ) : ℝ :=
  (x.1.1 : ℝ)⁻¹*(x.1.2 : ℝ)⁻¹*(x.2 : ℝ)⁻¹

noncomputable def weightedWitness (P Q U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop) : ℝ :=
  ∑ x ∈ witnessPairs (P.product Q) U witness,tripleWeight x

noncomputable def cofactorReward (P U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop) (q : ℕ) : ℝ :=
  ∑ p ∈ P,∑ u ∈ U,if witness (p,q) u then (p : ℝ)⁻¹*(u : ℝ)⁻¹ else 0

noncomputable def conditionalReward (P U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop) (q : ℕ) : ℝ :=
  cofactorReward P U witness q/(harmonicMass P*harmonicMass U)

theorem harmonicMass_nonneg (Q : Finset ℕ) : 0 ≤ harmonicMass Q := by unfold harmonicMass;positivity

theorem harmonicMass_pos (Q : Finset ℕ) (hQ : Q.Nonempty) (hp : ∀ q ∈ Q,0 < q) : 0 < harmonicMass Q := by
  apply Finset.sum_pos
  · intro q hq
    exact inv_pos.mpr (by exact_mod_cast hp q hq)
  · exact hQ

theorem tripleWeight_nonneg (x : (ℕ × ℕ) × ℕ) : 0 ≤ tripleWeight x := by unfold tripleWeight;positivity

theorem triple_weight_sum (P Q U : Finset ℕ) :
    (∑ x ∈ tripleSpace P Q U,tripleWeight x) = harmonicMass P*harmonicMass Q*harmonicMass U := by
  simp only [tripleSpace,Finset.sum_product,tripleWeight,harmonicMass,mul_assoc,← Finset.mul_sum,← Finset.sum_mul]

theorem cofactorReward_nonneg (P U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop) (q : ℕ) :
    0 ≤ cofactorReward P U witness q := by unfold cofactorReward;positivity

theorem cofactorReward_upper (P U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop) (q : ℕ) :
    cofactorReward P U witness q ≤ harmonicMass P*harmonicMass U := by
  calc
    _ ≤ ∑ p ∈ P,∑ u ∈ U,(p : ℝ)⁻¹*(u : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro u _
      split_ifs
      · exact le_rfl
      · positivity
    _ = _ := by simp only [harmonicMass,← Finset.mul_sum,← Finset.sum_mul]

theorem conditionalReward_bounds (P U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop) (q : ℕ)
    (hDen : 0 < harmonicMass P*harmonicMass U) : 0 ≤ conditionalReward P U witness q ∧ conditionalReward P U witness q ≤ 1 := by
  refine ⟨div_nonneg (cofactorReward_nonneg P U witness q) hDen.le,?_⟩
  exact (div_le_iff₀ hDen).mpr (by simpa only [one_mul] using cofactorReward_upper P U witness q)

theorem weightedWitness_decomposition (P Q U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop) :
    weightedWitness P Q U witness = ∑ q ∈ Q,(q : ℝ)⁻¹*cofactorReward P U witness q := by
  unfold weightedWitness witnessPairs
  simp only [Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product,tripleWeight]
  have he : ∀ p q u : ℕ,(if witness (p,q) u then (p : ℝ)⁻¹*(q : ℝ)⁻¹*(u : ℝ)⁻¹ else 0) =
      (q : ℝ)⁻¹*(if witness (p,q) u then (p : ℝ)⁻¹*(u : ℝ)⁻¹ else 0) := by
    intro p q u
    split_ifs <;> ring
  simp_rw [he]
  rw [Finset.sum_comm]
  simp only [cofactorReward,Finset.mul_sum]

end ErdosInverseCells

end

section

namespace ErdosInverseCells

theorem weightedWitness_conditioning (P Q U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop) :
    weightedWitness P Q U witness/(harmonicMass P*harmonicMass U) =
      ∑ q ∈ Q,(q : ℝ)⁻¹*conditionalReward P U witness q := by
  rw [weightedWitness_decomposition,Finset.sum_div]
  simp only [conditionalReward,mul_div_assoc]

theorem conditioned_reward_upper (P U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop)
    (hDen : 0 < harmonicMass P*harmonicMass U) (q : ℕ) :
    (q : ℝ)⁻¹*conditionalReward P U witness q ≤ (q : ℝ)⁻¹ := by
  have hh := mul_le_mul_of_nonneg_left (conditionalReward_bounds P U witness q hDen).2
    (inv_nonneg.mpr (Nat.cast_nonneg q))
  simpa only [mul_one] using hh

theorem condition_harmonic_density (P Q U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop)
    (sigma : ℝ) (hDen : 0 < harmonicMass P*harmonicMass U)
    (hBad : sigma*(harmonicMass P*harmonicMass Q*harmonicMass U) < weightedWitness P Q U witness) :
    sigma*(∑ q ∈ Q,(q : ℝ)⁻¹) < ∑ q ∈ Q,(q : ℝ)⁻¹*conditionalReward P U witness q := by
  rw [← weightedWitness_conditioning]
  apply (lt_div_iff₀ hDen).mpr
  have he : (sigma*(∑ q ∈ Q,(q : ℝ)⁻¹))*(harmonicMass P*harmonicMass U) =
      sigma*(harmonicMass P*harmonicMass Q*harmonicMass U) := by unfold harmonicMass;ring
  rwa [he]

theorem uncondition_harmonic_density (P Q U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop)
    (sigma : ℝ) (hDen : 0 < harmonicMass P*harmonicMass U)
    (hBad : sigma*(∑ q ∈ Q,(q : ℝ)⁻¹) < ∑ q ∈ Q,(q : ℝ)⁻¹*conditionalReward P U witness q) :
    sigma*(harmonicMass P*harmonicMass Q*harmonicMass U) < weightedWitness P Q U witness := by
  rw [← weightedWitness_conditioning] at hBad
  have hh := (lt_div_iff₀ hDen).mp hBad
  have he : (sigma*(∑ q ∈ Q,(q : ℝ)⁻¹))*(harmonicMass P*harmonicMass U) =
      sigma*(harmonicMass P*harmonicMass Q*harmonicMass U) := by unfold harmonicMass;ring
  rwa [he] at hh

end ErdosInverseCells

end

end Erdos970

end OAI
