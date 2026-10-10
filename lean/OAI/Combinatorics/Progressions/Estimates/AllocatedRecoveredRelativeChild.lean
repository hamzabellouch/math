import OAI.Combinatorics.Progressions.Dynamics.RelativeFrozenPatchChildBudget
import OAI.Combinatorics.Progressions.Geometry.AllocatedParameterBoxEarlyFreeze
import OAI.Combinatorics.Progressions.Sampling.AllocatedSamplerRelativeInduction

namespace OAI

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule BooleanCubeKernel
open scoped BigOperators TensorProduct Classical

variable {m s D E : ℕ} {X G : Type} [Fintype X] [Fintype G] [Nonempty G]
variable (L : RankPreparationFamily X (Fin D) m)
variable {I Deck : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (Deck j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ ((L j).Coord → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
local notation "Vars" => LayerSamplerVariables G I n B

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

omit [∀ j, Fintype (Deck j)] in
theorem exists_relative_child_of_allocated_recovery
    {A : PolynomialPatch X s (D + E)} (F : A.LowestLayerModel m)
    (ip : Fin D → MvPolynomial X ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial X ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (hm : ∀ j d, coefficients (L j).poly d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (L j).poly)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (c : ∀ j, U j) (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) (hξ1 : ξ ≤ 1)
    (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))
    (z : trimmedIntegerBox N (spatialTrimMargin τ N) ×
      rectangularWeightIndices 0
        (narrowTrimmedSpatialWidths (G := G)
          (J := PrincipalTupleIndex B (layerSamplerDegree I n))
          (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := Vars) I n)
    (read : AllocatedActualCoefficientIndex G X I Deck n B → ℤ)
    (hread : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ
      (fun j => (L j).poly) hm c z.1.val z.2.val sample read)
    {δ gain : ℝ} (hδ : 0 ≤ δ) (hgain : 0 < gain)
    (hgain1 : gain ≤ 1)
    (herr : ∀ x ∈ integerBox N, ∀ i, |eval (fun z => (x z : ℝ)) err i| ≤ δ)
    {p Pearly : ℝ} (hp0 : 0 ≤ p)
    (hDlog : (D : ℝ) ≤ Real.exp p) (hmlog : (m : ℝ) ≤ Real.exp p)
    (hLlog : (A.kernel.lip : ℝ) ≤ Real.exp p)
    (hNlog : ∀ j, (Fintype.card (L j).Coord : ℝ) ≤ Real.exp p)
    (hClog : ∀ j, C j ≤ Real.exp p) (hgainlog : Real.exp (-p) ≤ gain)
    (hδearly : δ ≤ Real.exp (-(3 * p + 130)))
    (hPearly : 6 * p + 35 ≤ Pearly)
    (hearly : ∀ C' : Fin m → ℝ, (∀ j, 0 ≤ C' j) →
      (∀ j, C' j ≤ Real.exp Pearly) →
      ∀ j, C' j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {n₀ stage d₀ : ℕ} {discount : ℝ} {cutoff cost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage discount cutoff cost)
    {pchild a Λ : ℝ} (hp2 : 2 ≤ p) (hpchild : p+2 ≤ pchild)
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hDim : (Fintype.card Vars : ℝ) ≤ pchild)
    (H : ℕ) (hH : H ≤ S.value) (hHcut : Real.exp (cutoff pchild) ≤ H)
    (hDpos : 0 < D) (hrest : ∀ i : Fin E, m < A.weight (i.natAdd D))
    (hA : relativePatchComplexity A ≤ pchild)
    (hstage : relativePatchDistinctWeights A ≤ stage+1)
    (f : (Vars → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox sides, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox sides ∧ f x ≠ 0} (s+2))
    (hscore : gain / 2 ≤ 𝔼 u : integerBox sides, (f u.val-a) * A.value
      (fun x => (jointIntegerPhysicalSite u.val (z.1.val,z.2.val) x : ℝ))) :
    ∃ fixed : {k : Vars // ¬H ≤ sides k} → ℤ,
      (∀ k, 0 ≤ fixed k ∧ fixed k < sides k) ∧
      RelativePatchSliceConclusion s
        (fun k : {k : Vars // H ≤ sides k} => sides k)
        (fun x => f (finiteSplitPoint (fun k : Vars => H ≤ sides k) x fixed))
        ((1-discount) ^ (stage+1) * Λ) (d₀+s*E) (cost pchild) := by
  have ha0 : 0 ≤ a := (Real.exp_pos _).le.trans ha
  have ha1 : a ≤ 1 := haΛ.trans hΛ
  have hunit : ∀ u : integerBox sides, |f u.val-a| ≤ 1 := by
    intro u
    have hu := hf u.val u.property
    exact abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  obtain ⟨tail, hLip, hweight, htailScore⟩ :=
    F.exists_freeze_allocated_parameter_box_of_early_bounds L B U b hb o S hR hσ
      ip hip c₀ err hprepare hm hp hσ1 C hC hchart c N hN hτ hτhalf hξ1 hsize z
      sample read hread hδ hgain hgain1 herr hp0 hDlog hmlog hLlog hNlog hClog
      hgainlog hδearly hPearly hearly (fun u => f u.val-a) hunit
      (by simpa only [integerAffineMap_jointIntegerFrame] using hscore)
  have hchildComplex : relativePatchComplexity tail ≤ pchild :=
    (relativePatchComplexity_tail_le A tail hLip).trans hA
  have hchildStage : relativePatchDistinctWeights tail ≤ stage :=
    relativePatchDistinctWeights_tail_le A tail hDpos F.weights hrest hweight hstage
  have hchildScore : Real.exp (-pchild) ≤ relativePatchBoxScore sides f a tail := by
    apply (relativeFrozenPatch_child_score_budget hgainlog hpchild).trans
    have hsum := Finset.sum_subtype (F := inferInstanceAs (Fintype (integerBox sides)))
      (integerBox sides) (fun _ => Iff.rfl)
      (fun x => (f x-a) * tail.value (fun k => (x k : ℝ)))
    simpa only [relativePatchBoxScore, Finset.expect_eq_sum_div_card,
      Finset.card_univ, Fintype.card_coe, ← hsum] using htailScore
  exact exists_allocatedSampler_relative_induction B U b S ih hp2 (by linarith)
    ha haΛ hΛ habsolute hDim H hH hHcut f hf hfree tail hchildComplex hchildStage hchildScore

end Erdos3.PolynomialPatch.LowestLayerModel

end

end OAI
