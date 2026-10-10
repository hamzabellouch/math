import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularRealizationInput
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanIntegratedAction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanAmbientWords

namespace OAI

/-! # Exponential compatibility in the published faithful realization

Onshuus–Post (2022), Proposition 2.4 and proof, give a faithful inducing
linear Lie realization of a simply connected real triangular group.
Lee, *Introduction to Smooth Manifolds*, second edition (2013), Theorem 8.44
(p.195) and Proposition 20.8(g) (p.520), give its Lie algebra map and
exponential compatibility. Only these properties are retained below.

https://doi.org/10.1112/blms.12574
https://doi.org/10.1007/978-1-4419-9982-5

The action and all bounds remain proved consequences, not part of the input.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]

/-- Faithful linear realization with its intrinsic exponential identity.
No metric distortion estimate is included. -/
def ExponentialLinearRealizationInput [SimplyConnectedSpace G] : Prop :=
  (∃ a, Nonempty (TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)) →
    ∀ (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G), IsGroupExponential Exp →
      ∃ m : ℕ, 0 < m ∧ ∃ (ρ : G →* (Matrix (Fin m) (Fin m) ℝ)ˣ)
        (j : GroupLieAlgebra (𝓘(ℝ, EG)) G →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ),
        Topology.IsInducing (fun g => (ρ g : Matrix (Fin m) (Fin m) ℝ)) ∧
        ∀ x, ρ (Exp x) = algebraExpUnit (j x)

variable [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

/-- The published representation identifies the actual factor action with
the explicit full Cartan adjoint automorphism. -/
theorem cartan_action_eq_adjoint_of_published_realization
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (d : F.D.carrier) :
    F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN hbijN dynkinN
      (cartanLog H F.D.equiv F.ExpD hbijD d) := by
  obtain ⟨m, hm, ρ, j, hind, hExp⟩ := realize ⟨a, ⟨T⟩⟩ ExpG hExpG
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  exact M.action_eq_adjoint_of_representation T F.N.equiv F.ExpN F.isExpN hbijN dynkinN
    F.D.equiv F.ExpD hbijD F.action j ρ hρ F.inclusionN F.closedN.injective F.inclusionD
    F.conjugation (fun x => by rw [F.compatibleN, hExp])
    (fun x => by rw [F.compatibleD, hExp]) d

open Module LieAlgebra LieModule

/-- The ambient word estimate now depends only on the published exponential,
Dynkin and representation inputs. No action or factor-path estimate is an
extra premise. -/
theorem exists_ambient_word_box_bound_of_published_inputs
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
      LinearMap.trace ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G) (ad ℝ _ x) = 0)
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ : M.Bases) {K : Set G} (hK : IsCompact K) :
    ∃ (C : ℝ) (q : ℕ), 0 ≤ C ∧ ∀ {E : Set W}, IsCompact E → E.Nonempty →
      ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ (m : ℕ) (u : ℕ → G),
      (∀ i < m, u i ∈ K) →
      (∀ i < m, ∃ w ∈ E, (π (wordPrefix u i)).toAdd = r • w) →
      ∃ (n : F.N.carrier) (d : F.D.carrier),
        F.inclusionN n * F.inclusionD d = wordPrefix u m ∧
        n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r
          (C * (1 + (m : ℝ)) ^ q) := by
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  obtain ⟨⟨chartD, hchartD⟩, _⟩ := haarD.2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
  exact M.exists_ambient_word_box_bound T F hunimod eW π hπExp
    chartN hchartN chartD hchartD dynkinN dynkinD b₀ γ hK
    (fun d => cartan_action_eq_adjoint_of_published_realization T M F hExpG realize
      _ _ dynkinN d)

/-- The ambient word estimate now depends only on the published exponential,
Dynkin and representation inputs. No action or factor-path estimate is an
extra premise. -/
theorem exists_ambient_word_factor_bound_of_published_inputs
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
      LinearMap.trace ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G) (ad ℝ _ x) = 0)
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ : M.Bases) {K : Set G} (hK : IsCompact K)
    (hbijD : Function.Bijective F.ExpD) :
    ∃ (C A : ℝ) (q c : ℕ), 0 ≤ C ∧ 0 ≤ A ∧ ∀ {E : Set W}, IsCompact E → E.Nonempty →
      ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ (m : ℕ) (u : ℕ → G),
      (∀ i < m, u i ∈ K) →
      (∀ i < m, ∃ w ∈ E, (π (wordPrefix u i)).toAdd = r • w) →
      ∃ (n : F.N.carrier) (d : F.D.carrier),
        F.inclusionN n * F.inclusionD d = wordPrefix u m ∧
        n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r
          (C * (1 + (m : ℝ)) ^ q) ∧
        ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD d)‖ ≤
          A * (1 + (m : ℝ)) ^ c := by
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  obtain ⟨⟨chartD, hchartD⟩, _⟩ := haarD.2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
  exact M.exists_ambient_word_factor_bound T F hunimod eW π hπExp
    chartN hchartN chartD hchartD dynkinN dynkinD b₀ γ hK
    (fun d => cartan_action_eq_adjoint_of_published_realization T M F hExpG realize
      _ _ dynkinN d)

end PolycyclicRecognition

end

end OAI
