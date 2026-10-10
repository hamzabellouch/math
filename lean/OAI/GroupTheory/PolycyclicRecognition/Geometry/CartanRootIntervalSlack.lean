import OAI.GroupTheory.PolycyclicRecognition.Geometry.RootIntervalSlack
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorCharts
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGroupBoxes

namespace OAI

/-! # Root-interval recurrence slack in the actual Cartan factor -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter
open scoped Manifold Topology Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The previously published linear realization supplies the actual
conjugation law. All interval and enlarged-suffix decay estimates are proved
from the finite root-word model. -/
theorem root_interval_slack_of_published_realization
    [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (q : Fin M.letterCount → ℝ)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    {δ c lo hi R : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (hR : 0 ≤ R)
    (hcost : ∀ w : M.wordList,
      lo ≤ M.boxCost T hunimod eW E w ∧ M.boxCost T hunimod eW E w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
    (hq : ∀ i, q i ≤ (1 - c * δ) * (M.supportIn T hunimod eW).weightSupport E i)
    {c₀ : ℕ} (aN : DynkinCoefficients c₀ 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (ε : ℝ → ℝ) (hεpos : ∀ r, 0 ≤ ε r) (hε : Tendsto ε atTop (𝓝 0))
    (k : ℝ → cartanRootIdeal H)
    (hk : ∀ᶠ r in atTop,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) r).equivFun (k r)‖ ≤
          Real.exp (r * ε r)) :
    ∀ᶠ r in atTop, ∀ i t, |t| ≤ R →
      F.ExpN (F.N.equiv (k r)) *
        F.ExpN (F.N.equiv ((t * Real.exp (r * q i)) • M.letter i)) *
          (F.ExpN (F.N.equiv (k r)))⁻¹ ∈
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1 := by
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
  have hletters (i : Fin M.letterCount) : FreeMagma.of i ∈ M.wordList := by
    apply M.mem_wordList_of_eval_ne_zero
    simp only [evalBracketWord_of]
    intro he
    have hh := M.letter_quotient i
    rw [he, map_zero] at hh
    exact M.abelianBasis.ne_zero i hh.symm
  apply root_interval_conjugation_mem_box M.letter M.bound_zero hletters b₀
    ((M.supportIn T hunimod eW).weightSupport E) q β hβ
    (F.ExpN ∘ F.N.equiv) hbij.injective (fun x => by simp [F.isExpN.map_neg])
    aN (model_binary_dynkin F.N.equiv F.ExpN aN hm)
    (j.comp (cartanRootIdeal H).incl) (ρ.comp F.inclusionN)
    (hρ.comp F.closedN.injective) _ hδ hc hhi hR hcost hgap hq ε hεpos hε k hk
  intro x
  change ρ (F.inclusionN (F.ExpN (F.N.equiv x))) = _
  rw [F.compatibleN, hmatch]
  rfl

end PolycyclicRecognition.CartanWordModel

end

end OAI
