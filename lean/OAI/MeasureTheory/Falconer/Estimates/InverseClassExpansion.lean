import OAI.MeasureTheory.Falconer.Estimates.DescriptorSeededInverse

namespace OAI

/-! # Exact inverse expansion in the recursive symbol class

The finite family is constructed from the actual differentiated masks.
Its constants are uniform in both descriptor lists, and the output keeps
the two original spatial multipliers and the remaining smoothness budget.
-/

namespace Falconer
open MeasureTheory
open PlanarFalconer (PolicyDescriptor)

variable {m KL KR L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}

abbrev DescriptorInverseIndex
    (f : DescriptorJetSymbol (m+1) KL L F D)
    (g : DescriptorJetSymbol (m+1) KR L G D) (j : ℕ) :=
  ((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).index

theorem card_descriptorInverseIndex
    (f : DescriptorJetSymbol (m+1) KL L F D)
    (g : DescriptorJetSymbol (m+1) KR L G D) (j : ℕ) :
    Fintype.card (DescriptorInverseIndex f g j) =
      MaskJetExpansion.inverseMultiplicity (m+2) j *
        (1+(2+F.card+G.card)*(m+3))^(2*j) := by
  rw [MaskJetExpansion.card_inverse_seed]
  simp only [DescriptorInverseLabel,Fintype.card_sum,Fintype.card_unique,
    Fintype.card_coe]
  congr 2
  ring

theorem descriptorInverseWeight_nonneg
    (f : DescriptorJetSymbol (m+1) KL L F D)
    (g : DescriptorJetSymbol (m+1) KR L G D) (hD : 0 < D)
    (j N : ℕ) (σ : ℝ) (a : DescriptorInverseIndex f g j) :
    0 ≤ descriptorInverseWeight f g j N σ a :=
  MaskJetExpansion.seededRadiusWeight_nonneg m j (descriptorInverseSeed f g)
    (descriptorInverseRadius f g N σ) (descriptorInverseRadius_pos f g hD N σ) a

/-- The exact factors delivered by the finite inverse calculation. -/
structure DescriptorInverseSymbols
    (f : DescriptorJetSymbol (m+1) KL L F D)
    (g : DescriptorJetSymbol (m+1) KR L G D) (j R : ℕ) (A B : ℝ) where
  left : DescriptorInverseIndex f g j → DescriptorJetSymbol (m+1) (KL+2*j) R F D
  right : DescriptorInverseIndex f g j → DescriptorJetSymbol (m+1) (KR+2*j) R G D
  left_jet : ∀ a, (left a).jet = f.inverseLeftJets g j a
  right_jet : ∀ a, (right a).jet = f.inverseRightJets g j a
  left_spatial : ∀ a, (left a).spatial = f.spatial
  right_spatial : ∀ a, (right a).spatial = g.spatial
  left_angular : ∀ a, (left a).angular = normalizedAngular A
    (fun z => (((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).term a).coefficient z *
      (((((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).term a).jet
        (.inl (.inl ()))).scaledValue D⁻¹ f.angular z))
  right_angular : ∀ a, (right a).angular = normalizedAngular B
    (((((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).term a).jet
      (.inr (.inl ()))).scaledValue D⁻¹ g.angular)

/-- The constants are selected before the lists, scale, and input symbols. -/
theorem exists_descriptorInverseSymbols (m j R : ℕ) :
    ∃ A B : ℝ, 1 ≤ A ∧ 1 ≤ B ∧
      ∀ (KL KR L : ℕ) (F G : Finset PolicyDescriptor) (D : ℝ)
        (f : DescriptorJetSymbol (m+1) KL L F D)
        (g : DescriptorJetSymbol (m+1) KR L G D),
        1 ≤ D → R+2*j ≤ L → Nonempty (DescriptorInverseSymbols f g j R A B) := by
  obtain ⟨A,hA,hleft⟩ := exists_inverse_left_symbol m j R
  obtain ⟨B,hB,hright⟩ := exists_inverse_right_symbol m j R
  refine ⟨A,B,hA,hB,?_⟩
  intro KL KR L F G D f g hD hL
  classical
  choose u hujet huspatial huangular using hleft KL KR L F G D f g hD hL
  choose v hvjet hvspatial hvangular using hright KL KR L F G D f g hD hL
  exact ⟨⟨u,v,hujet,hvjet,huspatial,hvspatial,huangular,hvangular⟩⟩

namespace DescriptorInverseSymbols

variable {f : DescriptorJetSymbol (m+1) KL L F D}
  {g : DescriptorJetSymbol (m+1) KR L G D} {j R : ℕ} {A B : ℝ}

theorem left_restore (T : DescriptorInverseSymbols f g j R A B)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    {U : ℝ} (hU : 0 < U) (hA : 0 < A)
    (a : DescriptorInverseIndex f g j) (x : Space (m+3)) (e : Sphere (m+3)) :
    ((U*A : ℝ) : ℂ)*(T.left a).value Q ρ profile N σ J i S U x e =
      f.spatial x*(descriptorInverseSeparation f g j Q ρ profile N σ J i S).left a x e := by
  have h := (T.left a).value_normalized_angular_restore Q ρ profile N σ J i S
    hU hA _ (T.left_angular a) x e
  rw [T.left_spatial a,T.left_jet a] at h
  rw [descriptorInverseSeparation_left]
  exact h.trans (by ring)

theorem right_restore (T : DescriptorInverseSymbols f g j R A B)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    {V : ℝ} (hV : 0 < V) (hB : 0 < B)
    (a : DescriptorInverseIndex f g j) (y : Space (m+3)) (e : Sphere (m+3)) :
    ((V*B : ℝ) : ℂ)*(T.right a).value Q ρ profile N σ J i S V y e =
      g.spatial y*(descriptorInverseSeparation f g j Q ρ profile N σ J i S).right a y e := by
  have h := (T.right a).value_normalized_angular_restore Q ρ profile N σ J i S
    hV hB _ (T.right_angular a) y e
  rw [T.right_spatial a,T.right_jet a] at h
  rw [descriptorInverseSeparation_right]
  exact h.trans (by ring)

/-- The exact finite inverse identity expressed using actual recursive
symbols. Every radius loss is on a newly added derivative. -/
theorem expansion (T : DescriptorInverseSymbols f g j R A B)
    (hD : 0 < D) (hA : 0 < A) (hB : 0 < B)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (Af Ag : ℝ) {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    (x y : Space (m+3)) (e : Sphere (m+3)) :
    localInverseAmplitude m
      (fun z => f.ambient Q ρ profile N σ J i S Af x z *
        g.ambient Q ρ profile N σ J i S Ag y z) j e =
      ∑ a : DescriptorInverseIndex f g j,
        ((descriptorInverseWeight f g j N σ a * (U*A) * (V*B) * Af⁻¹ * Ag⁻¹ : ℝ) : ℂ) *
          ((T.left a).value Q ρ profile N σ J i S U x e *
            (T.right a).value Q ρ profile N σ J i S V y e) := by
  rw [descriptor_seeded_inverse f g hD]
  change (f.spatial x*(Af⁻¹ : ℝ))*(g.spatial y*(Ag⁻¹ : ℝ))*
    (∑ a : DescriptorInverseIndex f g j,
      (descriptorInverseWeight f g j N σ a : ℂ)*
        (descriptorInverseSeparation f g j Q ρ profile N σ J i S).left a x e *
        (descriptorInverseSeparation f g j Q ρ profile N σ J i S).right a y e) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hl := T.left_restore Q ρ profile N σ J i S hU hA a x e
  have hr := T.right_restore Q ρ profile N σ J i S hV hB a y e
  simp only [Complex.ofReal_mul]
  calc
    _ = ((Af⁻¹ : ℝ) : ℂ)*((Ag⁻¹ : ℝ) : ℂ)*
        (descriptorInverseWeight f g j N σ a : ℂ)*
        (f.spatial x*(descriptorInverseSeparation f g j Q ρ profile N σ J i S).left a x e)*
        (g.spatial y*(descriptorInverseSeparation f g j Q ρ profile N σ J i S).right a y e) := by ring
    _ = _ := by rw [← hl,← hr]; simp only [Complex.ofReal_mul]; ring

end DescriptorInverseSymbols
end Falconer

end OAI
