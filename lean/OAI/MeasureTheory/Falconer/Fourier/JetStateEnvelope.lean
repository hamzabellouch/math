import OAI.MeasureTheory.Falconer.Angular.FactorizedAngularState

namespace OAI

/-! # Supremum of the factorized recursive angular states

The supremum varies the actual finite jets and the bounded smooth/spatial
multipliers. The displayed descriptor lists and all normalization data stay
fixed. Reached deletion maps each such symbol into the exact shorter list.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

noncomputable def jetStateEnergy {n K L : ℕ} {D : ℝ}
    {F G : Finset PolicyDescriptor}
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (μ ν : Measure (Space (n+2))) (M P a v : ℝ) (Ψ : ℝ → ℝ)
    (f : DescriptorJetSymbol n K L F D) (g : DescriptorJetSymbol n K L G D) : ℝ :=
  independentAngularEnergy a v Ψ
    (fun z => endpointTransform μ M (f.value Q ρ m N σ J i S A) z.1 z.2)
    (fun z => endpointTransform ν P (g.value Q ρ m N σ J i S A) z.1 z.2)

noncomputable def jetStateValues (n K L : ℕ) (D : ℝ) (F G : Finset PolicyDescriptor)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (μ ν : Measure (Space (n+2))) (M P a v : ℝ) (Ψ : ℝ → ℝ) : Set ℝ :=
  insert 0 {h | ∃ (f : DescriptorJetSymbol n K L F D) (g : DescriptorJetSymbol n K L G D),
    h = jetStateEnergy Q ρ m N σ J i S A μ ν M P a v Ψ f g}

noncomputable def jetStateEnvelope (n K L : ℕ) (D : ℝ) (F G : Finset PolicyDescriptor)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (μ ν : Measure (Space (n+2))) (M P a v : ℝ) (Ψ : ℝ → ℝ) : ℝ :=
  sSup (jetStateValues n K L D F G Q ρ m N σ J i S A μ ν M P a v Ψ)

noncomputable def jetStateBound {n : ℕ} (K : ℕ) (A : ℝ)
    (μ ν : Measure (Space (n+2))) (M P a v : ℝ) (Ψ : ℝ → ℝ) : ℝ :=
  (2:ℝ)^(((n+2:ℕ):ℝ)*(v-a))*
    (((descriptorJetBound (n+2) K)^K*A⁻¹*μ.real univ/M)^2*
      ((descriptorJetBound (n+2) K)^K*A⁻¹*ν.real univ/P)^2*
      (sphereMeasure (n+2)).real univ^2)*
    (PlanarFalconer.sourceAngularShellMeasure v Ψ).real univ

theorem jetStateBound_nonneg {n : ℕ} (K : ℕ) (A : ℝ)
    (μ ν : Measure (Space (n+2))) (M P a v : ℝ) (Ψ : ℝ → ℝ) :
    0 ≤ jetStateBound K A μ ν M P a v Ψ := by
  unfold jetStateBound
  positivity

 theorem jetStateEnergy_bound {n K L : ℕ} {D : ℝ} {F G : Finset PolicyDescriptor}
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (μ ν : Measure (Space (n+2)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {M P : ℝ} (hM : 0 < M) (hP : 0 < P)
    (a v : ℝ) (Ψ : ℝ → ℝ) [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (f : DescriptorJetSymbol n K L F D) (g : DescriptorJetSymbol n K L G D) :
    jetStateEnergy Q ρ m N σ J i S A μ ν M P a v Ψ f g ≤
      jetStateBound K A μ ν M P a v Ψ := by
  have hbase : 0 ≤ descriptorJetBound (n+2) K :=
    zero_le_one.trans (descriptorJetBound_one_le _ _)
  unfold jetStateBound
  apply independentAngularEnergy_bound a v Ψ
  · positivity
  · positivity
  · intro z
    exact endpointTransform_norm_le μ hM _ (f.value_norm_le Q ρ m N σ J i S hF hA) z.1 z.2
  · intro z
    exact endpointTransform_norm_le ν hP _ (g.value_norm_le Q ρ m N σ J i S hG hA) z.1 z.2

 theorem jetStateValues_bddAbove {n K L : ℕ} {D : ℝ} {F G : Finset PolicyDescriptor}
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (μ ν : Measure (Space (n+2)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {M P : ℝ} (hM : 0 < M) (hP : 0 < P)
    (a v : ℝ) (Ψ : ℝ → ℝ) [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)] :
    BddAbove (jetStateValues n K L D F G Q ρ m N σ J i S A μ ν M P a v Ψ) := by
  refine ⟨jetStateBound K A μ ν M P a v Ψ,?_⟩
  intro h hh
  rcases hh with rfl | ⟨f,g,rfl⟩
  · exact jetStateBound_nonneg K A μ ν M P a v Ψ
  · exact jetStateEnergy_bound Q ρ m N σ J i S hF hG hA μ ν hM hP a v Ψ f g

 theorem jetStateEnergy_le_envelope {n K L : ℕ} {D : ℝ} {F G : Finset PolicyDescriptor}
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (μ ν : Measure (Space (n+2)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {M P : ℝ} (hM : 0 < M) (hP : 0 < P)
    (a v : ℝ) (Ψ : ℝ → ℝ) [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (f : DescriptorJetSymbol n K L F D) (g : DescriptorJetSymbol n K L G D) :
    jetStateEnergy Q ρ m N σ J i S A μ ν M P a v Ψ f g ≤
      jetStateEnvelope n K L D F G Q ρ m N σ J i S A μ ν M P a v Ψ :=
  le_csSup (jetStateValues_bddAbove Q ρ m N σ J i S hF hG hA μ ν hM hP a v Ψ)
    (Or.inr ⟨f,g,rfl⟩)

 theorem jetStateEnvelope_remove_reached {n K L : ℕ} {D : ℝ} (F : Finset PolicyDescriptor)
    (Q : DyadicCube (n+2)) (hQ : 0 < Q.side) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (X Y : List (Fin (n+2) → Bool))
    (μ ν : Measure (Space (n+2))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)] :
    jetStateEnvelope n K L D F F Q ρ m N σ J i S A
      (μ.restrict (Q.descendant X).carrier) (ν.restrict (Q.descendant Y).carrier) M P a v Ψ ≤
    ((descriptorJetBound (n+2) K)^K)^2 * ((descriptorJetBound (n+2) K)^K)^2 *
      jetStateEnvelope n K L D
        (F.filter (fun b => X.length < descriptorAnchor b))
        (F.filter (fun b => Y.length < descriptorAnchor b))
        Q ρ m N σ J i S A
        (μ.restrict (Q.descendant X).carrier) (ν.restrict (Q.descendant Y).carrier) M P a v Ψ := by
  have hFX : ∀ b ∈ F.filter (fun b => X.length < descriptorAnchor b),
      ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z :=
    fun b hb => hF b (Finset.mem_filter.mp hb).1
  have hFY : ∀ b ∈ F.filter (fun b => Y.length < descriptorAnchor b),
      ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z :=
    fun b hb => hF b (Finset.mem_filter.mp hb).1
  apply csSup_le (show (jetStateValues n K L D F F Q ρ m N σ J i S A
    (μ.restrict (Q.descendant X).carrier) (ν.restrict (Q.descendant Y).carrier) M P a v Ψ).Nonempty
    from ⟨0,Or.inl rfl⟩)
  intro h hh
  rcases hh with rfl | ⟨f,g,rfl⟩
  · have hzero : 0 ≤ jetStateEnvelope n K L D _ _ Q ρ m N σ J i S A
        (μ.restrict (Q.descendant X).carrier) (ν.restrict (Q.descendant Y).carrier) M P a v Ψ :=
      le_csSup (jetStateValues_bddAbove Q ρ m N σ J i S hFX hFY hA _ _ hM hP a v Ψ)
        (Or.inl rfl)
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hzero
  · exact (f.energy_remove_reached g Q hQ ρ m N σ J i S hF hA X Y μ ν hM hP a v Ψ).trans
      (mul_le_mul_of_nonneg_left
        (jetStateEnergy_le_envelope Q ρ m N σ J i S hFX hFY hA _ _ hM hP a v Ψ _ _)
        (mul_nonneg (sq_nonneg _) (sq_nonneg _)))

end Falconer

end OAI
