import OAI.MeasureTheory.Falconer.Fourier.JetStateEnvelope
import OAI.MeasureTheory.Falconer.Angular.AngularEnvelopeGraph

namespace OAI

/-! # Actual graph children in the factorized angular envelope -/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

noncomputable def childJetStateMaximum (n K L : ℕ) (D : ℝ) (F : Finset PolicyDescriptor)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (X Y : List (Fin (n+2) → Bool)) (j : ℕ) (M a v : ℝ) (Ψ : ℝ → ℝ) : ℝ :=
  finiteEnvelopeMaximum
    ((Q.descendant X).occupiedPaths ρ j ×ˢ (Q.descendant Y).occupiedPaths ρ j)
    (fun row => jetStateEnvelope n K L D F F Q ρ m N σ J i S A
      (ρ.restrict ((Q.descendant X).descendant row.1).carrier)
      (ρ.restrict ((Q.descendant Y).descendant row.2).carrier) M M a v Ψ)

 theorem childJetStateMaximum_nonneg (n K L : ℕ) (D : ℝ) (F : Finset PolicyDescriptor)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (X Y : List (Fin (n+2) → Bool)) (j : ℕ) (M a v : ℝ) (Ψ : ℝ → ℝ) :
    0 ≤ childJetStateMaximum n K L D F Q ρ m N σ J i S A X Y j M a v Ψ :=
  finiteEnvelopeMaximum_nonneg _ _

 theorem childJetStateEnvelope_le {n K L : ℕ} (D : ℝ) (F : Finset PolicyDescriptor)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (X Y : List (Fin (n+2) → Bool)) (j : ℕ) (M a v : ℝ) (Ψ : ℝ → ℝ)
    (row : List (Fin (n+2) → Bool) × List (Fin (n+2) → Bool))
    (hrow : row ∈ (Q.descendant X).occupiedPaths ρ j ×ˢ (Q.descendant Y).occupiedPaths ρ j) :
    jetStateEnvelope n K L D F F Q ρ m N σ J i S A
      (ρ.restrict ((Q.descendant X).descendant row.1).carrier)
      (ρ.restrict ((Q.descendant Y).descendant row.2).carrier) M M a v Ψ ≤
    childJetStateMaximum n K L D F Q ρ m N σ J i S A X Y j M a v Ψ := by
  let V : (List (Fin (n+2) → Bool) × List (Fin (n+2) → Bool)) → ℝ := fun c =>
    jetStateEnvelope n K L D F F Q ρ m N σ J i S A
      (ρ.restrict ((Q.descendant X).descendant c.1).carrier)
      (ρ.restrict ((Q.descendant Y).descendant c.2).carrier) M M a v Ψ
  let T := (Q.descendant X).occupiedPaths ρ j ×ˢ (Q.descendant Y).occupiedPaths ρ j
  change V row ≤ sSup (insert 0 (V '' (T : Set _)))
  apply le_csSup ((T.finite_toSet.image V).insert 0).bddAbove
  exact Or.inr ⟨row,hrow,rfl⟩

 theorem childJetStateEnergy_le {n K L : ℕ} {D : ℝ} {F : Finset PolicyDescriptor}
    (Q : DyadicCube (n+2)) (hQ : 0 < Q.side)
    (ρ : Measure (Space (n+2))) [IsFiniteMeasure ρ] (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) {a p : ℕ} (hap : a ≤ p)
    (X Y : List (Fin (n+2) → Bool)) (hX : X.length = a) (hY : Y.length = a)
    (row : List (Fin (n+2) → Bool) × List (Fin (n+2) → Bool))
    (hrow : row ∈ (Q.descendant X).occupiedPaths ρ (p-a) ×ˢ
      (Q.descendant Y).occupiedPaths ρ (p-a))
    {M : ℝ} (hM : 0 < M) (v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (f g : DescriptorJetSymbol n K L F D) :
    jetStateEnergy Q ρ m N σ J i S A
      (ρ.restrict ((Q.descendant X).descendant row.1).carrier)
      (ρ.restrict ((Q.descendant Y).descendant row.2).carrier) M M p v Ψ f g ≤
    ((descriptorJetBound (n+2) K)^K)^2 * ((descriptorJetBound (n+2) K)^K)^2 *
      childJetStateMaximum n K L D (F.filter (fun b => p < descriptorAnchor b))
        Q ρ m N σ J i S A X Y (p-a) M p v Ψ := by
  have hx := Finset.mem_product.mp hrow
  have hxlen : (X++row.1).length = p := by
    rw [List.length_append,hX,(mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hx.1).1]
    omega
  have hylen : (Y++row.2).length = p := by
    rw [List.length_append,hY,(mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hx.2).1]
    omega
  have hstart := jetStateEnergy_le_envelope Q ρ m N σ J i S hF hF hA
    (ρ.restrict ((Q.descendant X).descendant row.1).carrier)
    (ρ.restrict ((Q.descendant Y).descendant row.2).carrier) hM hM p v Ψ f g
  have hremove := jetStateEnvelope_remove_reached (K := K) (L := L) (D := D) F Q hQ ρ m N σ J i S hF hA
    (X++row.1) (Y++row.2) ρ ρ hM hM p v Ψ
  simp only [Q.descendant_append,hxlen,hylen] at hremove
  apply (hstart.trans hremove).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  exact childJetStateEnvelope_le D (F.filter (fun b => p < descriptorAnchor b))
    Q ρ m N σ J i S A X Y (p-a) M p v Ψ row hrow

end Falconer

end OAI
