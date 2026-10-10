import OAI.Combinatorics.Progressions.Sampling.AllocatedScoredFreezing

namespace OAI

section

namespace Erdos3

open Module Submodule VectorPolynomial
open scoped BigOperators TensorProduct Classical

namespace FiniteProbabilityWeights

theorem mass_positive_restriction {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (Q : Finset Ω) :
    p.mass (Q.filter (fun z => 0 < p.weight z)) = p.mass Q := by
  unfold mass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h : 0 < p.weight z
  · simp only [h, ite_true]
  · simp only [h, ite_false]
    exact (le_antisymm (le_of_not_gt h) (p.nonneg z)).symm

end FiniteProbabilityWeights

variable {X G Ω : Type} [Fintype G] [Fintype Ω] {s D E m : ℕ}
variable {A : PolynomialPatch X s (D + E)}
variable (L : RankPreparationFamily X (Fin D) m)
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (L j).space)ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (L j).space))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B (fun j => (L j).space) b R σ)

theorem allocated_productive_freezing
    (F : A.LowestLayerModel m)
    (ip : Fin D → MvPolynomial X ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c : Fin D → ℝ) (err : VectorPolynomial X ℝ (Fin D → ℝ))
    (hprepare : ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + err)
    (hdeg : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (L j).poly)
    (hmem : ∀ j α, coefficients (L j).poly α ∈ (L j).space)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (L j).space))
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (L j).space) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (center : ∀ j, (L j).space)
    (law : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (frame : Ω → Option (LayerSamplerVariables G I n B) → X → ℤ)
    (hframe : ∀ z ∈ productive, 0 < law.weight z →
      allocatedAffineDensity B (fun j => (L j).space) b hb o hR hσ S
        (fun j => (L j).poly) hmem center (fun k v => (frame z k v : ℝ)) ≠ 0)
    {δ gain : ℝ} (hδ : 0 ≤ δ) (hgain : 0 < gain)
    (sites : Finset (LayerSamplerVariables G I n B → ℤ)) (hsites : sites.Nonempty)
    (hbox : ∀ x ∈ sites, ∀ v, |(x v : ℝ)| ≤ layerSamplerBox B (fun j => (L j).space) b S v)
    (herr : ∀ z ∈ productive, ∀ x ∈ sites, ∀ i,
      |VectorPolynomial.eval (fun v => (frame z none v : ℝ) + ∑ k, (frame z (some k) v : ℝ) * (x k : ℝ)) err i| ≤ δ)
    (score : Ω → (LayerSamplerVariables G I n B → ℤ) → ℝ)
    (hscore : ∀ z ∈ productive, ∀ x ∈ sites, |score z x| ≤ 1)
    (hproductive : ∀ z ∈ productive, gain / 2 ≤
      𝔼 x ∈ sites, score z x * A.value (fun v => (frame z none v : ℝ) + ∑ k, (frame z (some k) v : ℝ) * (x k : ℝ)))
    (hmass : gain / 4 ≤ law.mass productive)
    (hbudget : (D : ℝ) * (2 * ((∑ j, (Fintype.card (L j).Coord : ℝ) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * R j))) + δ)) < 1 / 12)
    (hloss : A.kernel.lip * ((D : ℝ) * (2 * ((∑ j, (Fintype.card (L j).Coord : ℝ) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * R j))) + δ))) ≤ gain / 16) :
    ∃ retained : Finset Ω, retained ⊆ productive ∧ gain / 4 ≤ law.mass retained ∧
      ∀ z ∈ retained, 0 < law.weight z ∧
        ∃ A' : PolynomialPatch (LayerSamplerVariables G I n B) s E,
          A'.kernel.lip = A.kernel.lip ∧
          (∀ i, A'.weight i = A.weight (i.natAdd D)) ∧
          7 * gain / 16 ≤ 𝔼 x ∈ sites, score z x * A'.value (fun k => (x k : ℝ)) := by
  refine ⟨productive.filter (fun z => 0 < law.weight z), Finset.filter_subset _ _, ?_, ?_⟩
  · simpa only [law.mass_positive_restriction] using hmass
  · intro z hz
    obtain ⟨hz, hw⟩ := Finset.mem_filter.mp hz
    have hpositive : 0 < 𝔼 x ∈ sites, score z x *
        A.value (fun v => (frame z none v : ℝ) + ∑ k, (frame z (some k) v : ℝ) * (x k : ℝ)) :=
      lt_of_lt_of_le (by positivity : 0 < gain / 2) (hproductive z hz)
    obtain ⟨A', hLip, hweight, _, hmean⟩ := allocated_scored_freezing L B b o hR hσ S
      F ip hip c err hprepare hdeg hmem hb hσ1 C hC hchart hsmall center (frame z)
      (hframe z hz hw) hδ sites hsites hbox (herr z hz) (score z) (hscore z hz)
      hpositive hbudget
    refine ⟨hw, A', hLip, hweight, ?_⟩
    linarith [hproductive z hz]

end Erdos3

end

end OAI
