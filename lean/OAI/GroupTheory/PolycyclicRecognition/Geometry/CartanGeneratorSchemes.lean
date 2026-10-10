import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialRepresentationInput
import OAI.GroupTheory.PolycyclicRecognition.Algebra.BoundedGeneratorSchemes

namespace OAI

/-! # Local generator schemes for the actual Cartan nilpotent factor

The published faithful realization and finite Dynkin formula instantiate the
proved local generator scheme with the actual homogeneous Cartan generators.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
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
/-- A concrete scheme in the homogeneous generator exponentials covers a
nonzero logarithmic neighborhood in the constructed nilpotent factor. -/
theorem exists_local_cartan_generator_scheme
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier) :
    ∃ (w : Fin (finrank ℝ (cartanRootIdeal H)) → List (Fin M.letterCount × ℝ))
      (i : Fin (finrank ℝ (cartanRootIdeal H)) → Fin M.letterCount)
      (ε : ℝ), 0 < ε ∧ ∀ v : cartanRootIdeal H,
      ‖(finBasis ℝ (cartanRootIdeal H)).equivFun v‖ < ε →
      ∃ t : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ, ‖t‖ < 1 ∧
        generatorGroupWord M.letter (F.ExpN ∘ F.N.equiv) (generatorSchemeWord w i t) =
          F.ExpN (F.N.equiv v) := by
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
    F.isExpN M.bound_zero (finrank ℝ (cartanRootIdeal H))
  exact exists_local_generator_scheme M.letter (F.ExpN ∘ F.N.equiv) M.generates
    hbij (by simp [F.isExpN.map_zero]) (fun v => by simp [F.isExpN.map_neg])
    (j.comp (cartanRootIdeal H).incl) (ρ.comp F.inclusionN)
    (hρ.comp F.closedN.injective) (fun v => by
      change ρ (F.inclusionN (F.ExpN (F.N.equiv v))) = _
      rw [F.compatibleN, hExp]
      rfl) coeff hprod

include T in
/-- A bounded logarithmic set in the actual Cartan factor has a common
finite bound on generator word length and on all amplitudes. -/
theorem exists_bounded_cartan_generator_words
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (R : ℝ) :
    ∃ (N : ℕ) (C : ℝ), 1 ≤ C ∧ ∀ v : cartanRootIdeal H,
      ‖(finBasis ℝ (cartanRootIdeal H)).equivFun v‖ ≤ R →
      ∃ u : List (Fin M.letterCount × ℝ), u.length ≤ N ∧
        (∀ p ∈ u, |p.2| ≤ C) ∧
        generatorGroupWord M.letter (F.ExpN ∘ F.N.equiv) u = F.ExpN (F.N.equiv v) := by
  obtain ⟨w, i, ε, hε, hlocal⟩ := M.exists_local_cartan_generator_scheme T F
    hExpG realize haarN dynkinN
  exact bounded_generation_of_local_scheme M.letter (F.ExpN ∘ F.N.equiv) w i
    (by simp [F.isExpN.map_zero]) (fun v s t => by
      simpa only [Function.comp_apply, map_smul] using F.isExpN.map_add_smul (F.N.equiv v) s t)
    hε hlocal R

end PolycyclicRecognition.CartanWordModel

end

end OAI
