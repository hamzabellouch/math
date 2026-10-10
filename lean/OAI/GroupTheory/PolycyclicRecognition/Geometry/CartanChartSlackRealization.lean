import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanChartSlack
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorCharts

namespace OAI

/-! # Cartan chart slack using only the published linear realization -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter
open scoped Manifold Topology Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {EG G W Z I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) [Fintype I] [DecidableEq I]

/-- The sampled suffix-conjugation estimate has no extra faithful
representation premise: it is supplied by the cited realization theorem. -/
theorem chart_suffix_conjugation_of_published_realization
    [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    {δ c lo hi : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi)
    (ht : 0 ≤ 1 - c * δ)
    (hcost : ∀ w : M.wordList,
      lo ≤ M.boxCost T hunimod eW E w ∧ M.boxCost T hunimod eW E w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
    (X : I → H) (S : Finset (FreeMagma I)) (βD : WordBasisSelections X S)
    (z : Z → Fin (finrank ℝ H) → ℝ) {R : ℝ} (hR : 0 ≤ R) (hz : ∀ u, ‖z u‖ ≤ R)
    (hdomain : ∀ u, eW (heightProjection T.character
      ((WordBasisSelections.basis X S βD).equivFun.symm (z u) : GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈
        (fun x => (1 - c * δ) • x) '' E)
    {c₀ : ℕ} (aN : DynkinCoefficients c₀ 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (ε : ℝ → ℝ) (hεpos : ∀ r, 0 ≤ ε r) (hε : Tendsto ε atTop (𝓝 0))
    (k : ℝ → cartanRootIdeal H)
    (hk : ∀ᶠ r : ℝ in atTop,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) r).equivFun (k r)‖ ≤
          Real.exp (r * ε r))
    (v : cartanRootIdeal H) :
    let bN := fun r => M.boxBasis T hunimod eW E β r
    let bD := fun r => exponentialRescaleBasis (WordBasisSelections.basis X S βD)
      (fun i => (bracketWordLength (βD.val i : FreeMagma I) : ℝ)) (Real.log r)
    TendstoUniformly (fun r u => dynkinProduct aN (basisBracket (bN r))
      (dynkinProduct aN (basisBracket (bN r)) ((bN r).equivFun (k r))
        ((bN r).equivFun (cartanIdealAdjointAutomorphism T H
          ((bD r).equivFun.symm (z u)) v))) (-((bN r).equivFun (k r))))
      (fun _ => 0) atTop := by
  obtain ⟨m, hmpos, ρ, j, hind, hmatch⟩ := realize ⟨a, ⟨T⟩⟩ ExpG hExpG
  let _ : NeZero m := ⟨Nat.ne_of_gt hmpos⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  have hbij : Function.Bijective (F.ExpN ∘ F.N.equiv) :=
    (funext hchartN ▸ chartN.bijective).comp F.N.equiv.bijective
  apply M.chart_suffix_conjugation_tendstoUniformly T hunimod eW b₀ hE hne β γ hβ
    hδ hc hhi ht hcost hgap X S βD z hR hz hdomain
    (F.ExpN ∘ F.N.equiv) hbij.injective (fun x => by simp [F.isExpN.map_neg])
    aN (model_binary_dynkin F.N.equiv F.ExpN aN hm)
    (j.comp (cartanRootIdeal H).incl) (ρ.comp F.inclusionN)
    (hρ.comp F.closedN.injective) _ ε hεpos hε k hk v
  intro x
  change ρ (F.inclusionN (F.ExpN (F.N.equiv x))) = _
  rw [F.compatibleN, hmatch]
  rfl

end PolycyclicRecognition.CartanWordModel

end

end OAI
