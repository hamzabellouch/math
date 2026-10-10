import OAI.MeasureTheory.Falconer.Angular.FactorizedAngularState

namespace OAI

/-! # Uniform graph budget for factorized angular symbols

The constants are fixed before the descriptor list and scale. Every symbol
in the recursive class then has the same size-one graph control, provided
its explicit mask derivative scale fits inside the displayed graph scale.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

 theorem exists_descriptorJetSymbol_admissible (n K L : ℕ) :
    ∃ B A : ℝ, 1 ≤ B ∧ 1 ≤ A ∧
      ∀ (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
        (N : ℕ) (σ : ℝ) (J i : ℕ) (F : Finset PolicyDescriptor)
        (S : PolicyDescriptor → Finset (Sphere (n+2))),
      (∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ D E H : ℝ, 0 ≤ D → 1 ≤ E → 1 ≤ H →
      (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E) → (F.card:ℝ)*B*E ≤ H →
      ∀ f : DescriptorJetSymbol n K L F D,
        AngularAdmissible L (D+H)
          {z | ∀ b ∈ F, z ∈ descriptorEndpointGood Q ρ m N σ J (i+1) b}
          (f.value Q ρ m N σ J i S A) := by
  obtain ⟨B,C,hB,hC,hcontrol⟩ := descriptorJetProduct_chartControl n K L
  have hA : 1 ≤ C*B^K := by
    calc
      1 = (1:ℝ)*1 := by ring
      _ ≤ C*B^K := mul_le_mul hC (one_le_pow₀ hB) (by norm_num) (zero_le_one.trans hC)
  refine ⟨B,C*B^K,hB,hA,?_⟩
  intro Q ρ m N σ J i F S hsep D E H hD hE hH hscale hEH f
  apply f.value_admissible Q ρ m N σ J i S (zero_lt_one.trans_le hA) hD (zero_le_one.trans hH)
  exact hcontrol Q ρ m N σ J i F id S (fun b => (f.jet b).order)
    (fun b => (f.jet b).vectors) hsep f.order_le
    (fun b _ => (f.jet b).norm_vectors) E H hE hH hscale hEH

end Falconer

end OAI
