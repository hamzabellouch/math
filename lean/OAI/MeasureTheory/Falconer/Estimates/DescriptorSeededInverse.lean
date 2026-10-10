import OAI.MeasureTheory.Falconer.Fourier.InverseJetValues

namespace OAI

/-! # The seeded inverse identity for actual recursive amplitudes

Both endpoint symbols use their original ambient masks. Spatial factors
are pulled out exactly, and only newly added derivatives pay radius powers.
-/

namespace Falconer
open MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

variable {m KL KR L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}

noncomputable def descriptorInverseRadius
    (f : DescriptorJetSymbol (m+1) KL L F D) (g : DescriptorJetSymbol (m+1) KR L G D)
    (N : ℕ) (σ : ℝ) : DescriptorInverseLabel F ⊕ DescriptorInverseLabel G → ℝ :=
  Sum.elim (f.seedRadius N σ) (g.seedRadius N σ)

noncomputable def descriptorInverseWeight
    (f : DescriptorJetSymbol (m+1) KL L F D) (g : DescriptorJetSymbol (m+1) KR L G D)
    (j N : ℕ) (σ : ℝ)
    (a : ((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).index) : ℝ :=
  MaskJetExpansion.seededRadiusWeight m j (descriptorInverseSeed f g)
    (descriptorInverseRadius f g N σ) a

theorem descriptorInverseRadius_pos
    (f : DescriptorJetSymbol (m+1) KL L F D) (g : DescriptorJetSymbol (m+1) KR L G D)
    (hD : 0 < D) (N : ℕ) (σ : ℝ)
    (a : DescriptorInverseLabel F ⊕ DescriptorInverseLabel G) :
    0 < descriptorInverseRadius f g N σ a := by
  cases a with
  | inl a => exact f.seedRadius_pos hD N σ a
  | inr a => exact g.seedRadius_pos hD N σ a

theorem descriptorInverseWeight_le
    (f : DescriptorJetSymbol (m+1) KL L F D) (g : DescriptorJetSymbol (m+1) KR L G D)
    (hD : 0 < D) (j N : ℕ) (σ : ℝ) {E : ℝ} (hE : 1 ≤ E) (hDE : D ≤ E)
    (hF : ∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (hG : ∀ b ∈ G, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (a : ((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).index) :
    descriptorInverseWeight f g j N σ a ≤ E^(2*j) := by
  apply MaskJetExpansion.seededRadiusWeight_le m j (descriptorInverseSeed f g)
    (descriptorInverseRadius f g N σ) (descriptorInverseRadius_pos f g hD N σ) hE
  intro l
  rcases l with l | l <;> rcases l with l | b
  · simpa only [descriptorInverseRadius,Sum.elim_inl,DescriptorJetSymbol.seedRadius,inv_inv]
      using hDE
  · exact hF b b.property
  · simpa only [descriptorInverseRadius,Sum.elim_inr,DescriptorJetSymbol.seedRadius,
      Sum.elim_inl,inv_inv] using hDE
  · exact hG b b.property

/-- Exact inverse formula before replacing the endpoint factors by their
normalized output symbols. -/
theorem descriptor_seeded_inverse
    (f : DescriptorJetSymbol (m+1) KL L F D) (g : DescriptorJetSymbol (m+1) KR L G D)
    (hD : 0 < D) (j : ℕ) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
    (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S : PolicyDescriptor → Finset (Sphere (m+3))) (Af Ag : ℝ)
    (x y : Space (m+3)) (e : Sphere (m+3)) :
    localInverseAmplitude m
      (fun z => f.ambient Q ρ profile N σ J i S Af x z *
        g.ambient Q ρ profile N σ J i S Ag y z) j e =
      (f.spatial x*(Af⁻¹ : ℝ))*(g.spatial y*(Ag⁻¹ : ℝ))*
        ((descriptorInverseSeparation f g j Q ρ profile N σ J i S).scaleTerms
          (fun a => (descriptorInverseWeight f g j N σ a : ℂ))).value x y e := by
  let k := descriptorInverseSeed f g
  let r := descriptorInverseRadius f g N σ
  let B := f.seedMask Q ρ profile N σ J i S
  let C := g.seedMask Q ρ profile N σ J i S
  let H := fun z => (∏ l, (f.seedJet l).scaledValue (f.seedRadius N σ l) (B l x) z)*
    (∏ l, (g.seedJet l).scaledValue (g.seedRadius N σ l) (C l y) z)
  have hH : ContDiff ℝ ∞ H :=
    (contDiff_prod (fun l _ => MaskJetIndex.scaledValue_contDiff _ _ _
      (f.seedMask_smooth Q ρ profile N σ J i S l x))).mul
    (contDiff_prod (fun l _ => MaskJetIndex.scaledValue_contDiff _ _ _
      (g.seedMask_smooth Q ρ profile N σ J i S l y)))
  have heq : (fun z => f.ambient Q ρ profile N σ J i S Af x z *
      g.ambient Q ρ profile N σ J i S Ag y z) =
      fun z => ((f.spatial x*(Af⁻¹ : ℝ))*(g.spatial y*(Ag⁻¹ : ℝ)))*H z := by
    funext z
    rw [f.ambient_eq_seedProduct,g.ambient_eq_seedProduct]
    dsimp only [H,B,C]
    ring
  rw [heq,localInverseAmplitude_const_mul m j _ H hH]
  congr 1
  have hinv := seededJetSeparation_exact m j k r
    (fun l => (descriptorInverseRadius_pos f g hD N σ l).ne') B C
    (f.seedMask_smooth Q ρ profile N σ J i S)
    (g.seedMask_smooth Q ρ profile N σ J i S) x y e
  exact hinv

end Falconer

end OAI
