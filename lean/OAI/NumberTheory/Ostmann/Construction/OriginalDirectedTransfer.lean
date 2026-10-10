import OAI.NumberTheory.Ostmann.Arithmetic.PrimeTupleResidueRow
import OAI.NumberTheory.Ostmann.Arithmetic.ReconstructedPhaseWeight

namespace OAI

/-! # An arithmetic transfer of the actual supported directed amplitude -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def groupedDirectedAmplitude {A H Y Z : Type*}
    [Fintype A] [Fintype H] [Fintype Y] [Fintype Z]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {n : ℕ}
    (Q : Fin n → Finset ℕ) (S : Finset (Fin n → P))
    (χP : Fin n → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : Fin n → P → ℂ) (ε : Fin n → ℤ)
    (L : A → H → ℕ) (U : Z → Y → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ z y, Fact (U z y).Prime]
    (t : ∀ p : ℕ, ZMod p)
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (ν : Z → A → H → ℂ) (νY : Z → A → Y → ℂ) (v : A → ℤ)
    (W : Z → ℕ → A → ℂ) (μ : Z → ℝ) : ℂ :=
  ∑ z, (μ z : ℂ) * ∑ x ∈ S, (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) *
    ∑ a, primeTupleResidueRow P hP χP κ t (∏ y, U z y) ε x
      (primeTuplePivotKey P hP x (∏ h, L a h) (v a)) *
      retainedWeightedCoefficient L (U z) t χH χY b (ν z) (νY z) v (W z) (∏ i, (x i : ℕ)) a

/-- This is the normalized transfer inequality with its actual prime residue
row and its next copied directed amplitude, rather than an assumed recurrence. -/
theorem original_directed_transfer {A H Y Z : Type*}
    [Fintype A] [Fintype H] [Fintype Y] [Fintype Z]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {n : ℕ}
    (Q : Fin n → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQ : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (S : Finset (Fin n → P)) (hS : ∀ x ∈ S, Function.Injective x)
    (T : Finset ℕ) (hT : ∀ M ∈ T, 0 < M) (hST : ∀ x ∈ S, (∏ i, (x i : ℕ)) ∈ T)
    (χP : Fin n → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : Fin n → P → ℂ) (hκ : ∀ i p, ‖κ i p‖ ≤ 1) (ε : Fin n → ℤ)
    (L : A → H → ℕ) (U : Z → Y → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ z y, Fact (U z y).Prime]
    (t : ∀ p : ℕ, ZMod p)
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (ν : Z → A → H → ℂ) (νY : Z → A → Y → ℂ) (v : A → ℤ)
    (W : Z → ℕ → A → ℂ) (μ : Z → ℝ)
    (hμ : ∀ z, 0 ≤ μ z) (hμsum : ∑ z, μ z ≤ 1)
    (B K V : ℕ)
    (hsupport : ∀ z M, M ∈ T → ∀ a, W z M a ≠ 0 →
      Pairwise (fun i j => (Sum.elim (L a) (U z) i).Coprime (Sum.elim (L a) (U z) j)) ∧
      M.Coprime ((∏ h, L a h) * ∏ y, U z y) ∧ (v a).natAbs ≤ B ∧ (∏ h, L a h) ≤ K)
    (hscale : ∀ M ∈ T, 2 * B * K ≤ V * M)
    (hlargeL : ∀ a h, V < L a h) (hlargeU : ∀ z y, V < U z y)
    (hb : ∀ y, b (some (.inr y)) (some (.inr y)) = 0)
    (d : ℝ) (hcost : ((n.factorial : ℝ) * ∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) ≤ Real.exp d) :
    Real.exp (-d) *
      ‖groupedDirectedAmplitude P hP Q S χP κ ε L U t χH χY b ν νY v W μ‖ ^ 2 ≤
        (∑ z, μ z * ∑ M ∈ T,
          (pivotDiagonal (fun a => ∏ h, L a h) v
            (retainedWeightedCoefficient L (U z) t χH χY b (ν z) (νY z) v (W z) M)).re) +
        ‖∑ z, (μ z : ℂ) * copiedWeightedAmplitude L (U z) t χH χY b
          (ν z) (νY z) v (W z) T V‖ := by
  let c : Z → ℕ → A → ℂ := fun z =>
    retainedWeightedCoefficient L (U z) t χH χY b (ν z) (νY z) v (W z)
  have hW (z M a) (hc : c z M a ≠ 0) : W z M a ≠ 0 := by
    intro hz
    apply hc
    simp only [c, retainedWeightedCoefficient, hz, zero_mul]
  have hcop (z M) (hMT : M ∈ T) (a) (hc : c z M a ≠ 0) : (∏ h, L a h).Coprime M :=
    (Nat.coprime_mul_iff_right.mp (hsupport z M hMT a (hW z M a hc)).2.1).1.symm
  have hpos (z M) (_ : M ∈ T) (a) (_ : c z M a ≠ 0) : 0 < ∏ h, L a h :=
    Finset.prod_pos fun h _ => (Fact.out : (L a h).Prime).pos
  have hv (z M) (hMT : M ∈ T) (a) (hc : c z M a ≠ 0) : (v a).natAbs ≤ B :=
    (hsupport z M hMT a (hW z M a hc)).2.2.1
  have hL (z M) (hMT : M ∈ T) (a) (hc : c z M a ≠ 0) : (∏ h, L a h) ≤ K :=
    (hsupport z M hMT a (hW z M a hc)).2.2.2
  have ht := original_averaged_pivot_transfer P hP Q hQP hQ S hS T hT hST μ hμ hμsum
    (fun z => primeTupleResidueRow P hP χP κ t (∏ y, U z y) ε)
    (fun z x _ u => primeTupleResidueRow_norm_le_one P hP χP κ hκ t (∏ y, U z y) ε x u)
    (fun a => ∏ h, L a h) v c hcop hpos B K V hv hL hscale d hcost
  have hnext (z) : reconstructedOffDiagonal T V (fun a => ∏ h, L a h) v (c z) =
      copiedWeightedAmplitude L (U z) t χH χY b (ν z) (νY z) v (W z) T V :=
    reconstructedOffDiagonal_eq_copiedWeightedAmplitude L (U z) t χH χY b
      (ν z) (νY z) v (W z) T B K V hT (hsupport z) hscale hlargeL (hlargeU z) hb
  simpa only [hnext, groupedDirectedAmplitude, c] using ht

end Ostmann

end OAI
