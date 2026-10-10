import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGeneratorSchemes
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledInverseSections

namespace OAI

/-! # Continuous inverse schemes in actual Cartan boxes

The same published exponential and Dynkin inputs now supply a uniformly
bounded continuous endpoint coding on a fixed ball in every actual
rescaled Cartan root-ideal chart.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric
open scoped Manifold Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

include T in
/-- Common continuous endpoint coding for all actual Cartan rescalings. -/
theorem exists_uniform_cartan_inverse_sections
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ (ε : ℝ) (N : ℕ) (C : ℝ), 0 < ε ∧ 1 ≤ C ∧
      ∀ (s : Fin M.letterCount → ℝ) (β : M.Bases),
        IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
          (fun w => bracketWordExponent s w) β.val →
        ∀ r : ℝ, 0 ≤ r →
        let b := exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
          (fun j => bracketWordExponent s (β.val j)) r
        ∃ (w : Fin (finrank ℝ (cartanRootIdeal H)) → List (Fin M.letterCount × ℝ))
          (i : Fin (finrank ℝ (cartanRootIdeal H)) → Fin M.letterCount)
          (σ : (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →
            Fin (finrank ℝ (cartanRootIdeal H)) → ℝ),
          ContinuousOn σ (ball 0 ε) ∧ ∀ y ∈ ball (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ε,
            ‖σ y‖ < 1 ∧ (generatorSchemeWord w i (σ y)).length ≤ N ∧
            (∀ z ∈ generatorSchemeWord w i (σ y), |z.2| ≤ C) ∧
            generatorGroupWord (fun i => Real.exp (r * s i) • M.letter i)
              (F.ExpN ∘ F.N.equiv) (generatorSchemeWord w i (σ y)) =
                F.ExpN (F.N.equiv (b.equivFun.symm y)) := by
  obtain ⟨m, hm, ρ, j, hind, hExp⟩ := realize ⟨a, ⟨T⟩⟩ ExpG hExpG
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  have hbij : Function.Bijective (F.ExpN ∘ F.N.equiv) :=
    (funext hchartN ▸ chartN.bijective).comp F.N.equiv.bijective
  obtain ⟨coeff, _, hprod⟩ := model_finiteDynkinExpansion dynkinN F.N.equiv F.ExpN
    F.isExpN M.bound_zero 2
  apply exists_uniform_rescaled_inverse_sections M.letter M.bound_zero
    M.letter_mem_wordList b₀ (F.ExpN ∘ F.N.equiv) hbij.injective
    (by simp [F.isExpN.map_zero]) (fun v => by simp [F.isExpN.map_neg])
    (fun v s t => by
      simpa only [Function.comp_apply, map_smul] using F.isExpN.map_add_smul (F.N.equiv v) s t)
    coeff (fun x y => ?_) (j.comp (cartanRootIdeal H).incl) (ρ.comp F.inclusionN)
    (hρ.comp F.closedN.injective) (fun v => ?_)
  · simpa [List.ofFn_succ] using (hprod ![x, y]).symm
  · change ρ (F.inclusionN (F.ExpN (F.N.equiv v))) = _
    rw [F.compatibleN, hExp]
    rfl

end PolycyclicRecognition.CartanWordModel

end

end OAI
