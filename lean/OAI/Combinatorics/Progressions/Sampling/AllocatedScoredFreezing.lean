import OAI.Combinatorics.Progressions.Estimates.AllocatedRecoveredPreparedFreeze

namespace OAI

section

namespace Erdos3.PolynomialPatch

open scoped BigOperators

theorem exists_contribution_of_positive_score {X Ω : Type*} [Fintype Ω]
    {s d : ℕ} (A : PolynomialPatch X s d) (p : FiniteProbabilityWeights Ω)
    (point : Ω → X → ℝ) (score : Ω → ℝ)
    (hscore : 0 < p.mean (fun x => score x * A.value (point x))) :
    ∃ x b, A.kernel.value ((A.form.slots (point x)).residual b) ≠ 0 := by
  classical
  by_contra! h
  have hz (x : Ω) : A.value (point x) = 0 :=
    (A.form.slots (point x)).patchValue_eq_zero A.kernel (h x)
  simp only [hz, mul_zero, p.mean_const] at hscore
  exact lt_irrefl 0 hscore

theorem score_stability {X Y Ω : Type*} [Fintype Ω] {s d t e : ℕ}
    (A : PolynomialPatch X s d) (B : PolynomialPatch Y t e)
    (p : FiniteProbabilityWeights Ω) (x : Ω → X → ℝ) (y : Ω → Y → ℝ)
    (score : Ω → ℝ) (hscore : ∀ z, |score z| ≤ 1)
    {ε : ℝ} (hclose : ∀ z, dist (A.value (x z)) (B.value (y z)) ≤ ε) :
    p.mean (fun z => score z * A.value (x z)) - ε ≤
      p.mean (fun z => score z * B.value (y z)) := by
  have hpoint (z) : score z * A.value (x z) ≤ score z * B.value (y z) + ε := by
    have h := calc
      |score z * (A.value (x z) - B.value (y z))| =
          |score z| * |A.value (x z) - B.value (y z)| := abs_mul _ _
      _ ≤ 1 * |A.value (x z) - B.value (y z)| :=
        mul_le_mul_of_nonneg_right (hscore z) (abs_nonneg _)
      _ ≤ ε := by simpa only [one_mul, Real.dist_eq] using hclose z
    linarith [le_abs_self (score z * (A.value (x z) - B.value (y z)))]
  have h := p.mean_mono hpoint
  rw [p.mean_add, p.mean_const] at h
  linarith

end Erdos3.PolynomialPatch

end

section

namespace Erdos3

open Module Submodule VectorPolynomial
open scoped BigOperators TensorProduct

variable {X G : Type} [Fintype G] {s D E m : ℕ}
variable {A : PolynomialPatch X s (D + E)}
variable (L : RankPreparationFamily X (Fin D) m)
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (L j).space)ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (L j).space))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B (fun j => (L j).space) b R σ)

theorem allocated_scored_freezing
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
    (frame : Option (LayerSamplerVariables G I n B) → X → ℤ)
    (hframe : allocatedAffineDensity B (fun j => (L j).space) b hb o hR hσ S
      (fun j => (L j).poly) hmem center (fun k v => (frame k v : ℝ)) ≠ 0)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (sites : Finset (LayerSamplerVariables G I n B → ℤ)) (hsites : sites.Nonempty)
    (hbox : ∀ x ∈ sites, ∀ v, |(x v : ℝ)| ≤ layerSamplerBox B (fun j => (L j).space) b S v)
    (herr : ∀ x ∈ sites, ∀ i,
      |VectorPolynomial.eval (fun v => (frame none v : ℝ) + ∑ k, (frame (some k) v : ℝ) * (x k : ℝ)) err i| ≤ δ)
    (score : (LayerSamplerVariables G I n B → ℤ) → ℝ)
    (hscore : ∀ x ∈ sites, |score x| ≤ 1)
    (hpositive : 0 < 𝔼 x ∈ sites, score x * A.value (fun v => (frame none v : ℝ) + ∑ k, (frame (some k) v : ℝ) * (x k : ℝ)))
    (hbudget : (D : ℝ) * (2 * ((∑ j, (Fintype.card (L j).Coord : ℝ) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * R j))) + δ)) < 1 / 12) :
    ∃ A' : PolynomialPatch (LayerSamplerVariables G I n B) s E,
      A'.kernel.lip = A.kernel.lip ∧
      (∀ i, A'.weight i = A.weight (i.natAdd D)) ∧
      (∀ x ∈ sites, dist (A.value (fun v => (frame none v : ℝ) + ∑ k, (frame (some k) v : ℝ) * (x k : ℝ))) (A'.value (fun k => (x k : ℝ))) ≤
        A.kernel.lip * ((D : ℝ) * (2 * ((∑ j, (Fintype.card (L j).Coord : ℝ) *
          (C j * (((Fintype.card (I j) : ℝ) + 1) * R j))) + δ)))) ∧
      (𝔼 x ∈ sites, score x * A.value (fun v => (frame none v : ℝ) + ∑ k, (frame (some k) v : ℝ) * (x k : ℝ))) -
        A.kernel.lip * ((D : ℝ) * (2 * ((∑ j, (Fintype.card (L j).Coord : ℝ) *
          (C j * (((Fintype.card (I j) : ℝ) + 1) * R j))) + δ))) ≤ 𝔼 x ∈ sites, score x * A'.value (fun k => (x k : ℝ)) := by
  classical
  let p := FiniteProbabilityWeights.uniformFinset sites hsites
  let point := fun x : sites =>
    fun v => (frame none v : ℝ) + ∑ k, (frame (some k) v : ℝ) * (x.val k : ℝ)
  have hp : 0 < p.mean (fun x => score x.val * A.value (point x)) := by
    rw [← FiniteProbabilityWeights.uniformFinset_mean sites hsites
      (fun x => score x * A.value (fun v => (frame none v : ℝ) + ∑ k, (frame (some k) v : ℝ) * (x k : ℝ)))] at hpositive
    exact hpositive
  obtain ⟨x₀, bref, href⟩ := A.exists_contribution_of_positive_score p point
    (fun x => score x.val) hp
  let Ω : Set (LayerSamplerVariables G I n B → ℝ) :=
    {x | ∃ z ∈ sites, x = fun k => (z k : ℝ)}
  obtain ⟨A', hLip, hw, hv⟩ := allocated_prepared_freezing L B b o hR hσ S F ip hip c err
    hprepare hdeg hmem hb hσ1 C hC hchart hsmall center frame hframe hδ Ω
    (by rintro x ⟨z, hz, rfl⟩; exact ⟨z, rfl⟩)
    (by rintro x ⟨z, hz, rfl⟩; exact hbox z hz)
    (by rintro x ⟨z, hz, rfl⟩; exact herr z hz)
    (fun k => (x₀.val k : ℝ)) ⟨x₀.val, x₀.property, rfl⟩ bref href hbudget
  have hvs (x) (hx : x ∈ sites) := hv (fun k => (x k : ℝ)) ⟨x, hx, rfl⟩
  refine ⟨A', hLip, hw, hvs, ?_⟩
  have he := A.score_stability A' p point (fun x k => (x.val k : ℝ))
    (fun x => score x.val) (fun x => hscore x.val x.property)
    (fun x => hvs x.val x.property)
  dsimp only [p, point] at he
  rw [FiniteProbabilityWeights.uniformFinset_mean sites hsites
      (fun x => score x * A.value (fun v => (frame none v : ℝ) + ∑ k, (frame (some k) v : ℝ) * (x k : ℝ))),
    FiniteProbabilityWeights.uniformFinset_mean sites hsites
      (fun x => score x * A'.value (fun k => (x k : ℝ)))] at he
  exact he

end Erdos3

end

end OAI
