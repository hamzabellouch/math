import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeAdaptedPathBasis
import OAI.GroupTheory.PolycyclicRecognition.Analysis.IdealSectionBoxCoordinates

namespace OAI

/-! # The source ideal-section probes lie in one ambient word box -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped Manifold

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ)) {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]

/-- In the adapted maximal basis an intrinsic ideal box is contained in
the ambient word box with exactly the same radius and exponents. -/
theorem exists_ideal_probe_box
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (E : Set W) (hs : ∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport E i)
    (hzero : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
      (M.supportIn T hunimod eW).weightSupport E i = 0)
    (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C bI
      ((M.supportIn T hunimod eW).weightSupport E) β) :
    ∃ γ : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
        (M.boxCost T hunimod eW E) γ.val ∧
      ∀ {X : Type*} (Exp : cartanRootIdeal H → X) (r R : ℝ), 0 ≤ R →
        M.coneIdealBox C (fun v => Exp v.val)
          ((M.supportIn T hunimod eW).weightSupport E) β r R ⊆
            M.groupBox T hunimod eW Exp E γ r R := by
  obtain ⟨bQ, lift, hlift, γ, hγ, hbox, _⟩ :=
    M.exists_cone_adapted_path_basis C T hunimod eW bN bI E hs hzero β hβ
  refine ⟨γ, hγ, ?_⟩
  intro X Exp r R hR x hx
  obtain ⟨v, hv, hb⟩ := hx
  rw [hbox]
  refine ⟨v.val, hv, ?_⟩
  exact (ideal_scaled_coordinates_le_iff (M.coneWordIdeal C)
    (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β)
    bQ lift hlift _ r R hR v).mpr hb

/-- Completing a maximal ideal basis by pure quotient words places every
unit ideal-section probe in one fixed-radius full word box. The radius
is uniform in the scale, by the actual finite Dynkin product formula. -/
theorem exists_section_probe_box
    (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
    (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExpN : IsGroupExponential ExpN)
    (dynkinN : NilpotentDynkinExpansionInput EN N)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (E : Set W) (hs : ∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport E i)
    (hzero : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
      (M.supportIn T hunimod eW).weightSupport E i = 0)
    (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C bI
      ((M.supportIn T hunimod eW).weightSupport E) β) :
    ∃ (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
        ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
      (lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
        cartanRootIdeal H),
      (∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j) ∧
      ∃ (γ : M.Bases) (R : ℝ), 0 ≤ R ∧
        IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
          (M.boxCost T hunimod eW E) γ.val ∧
        ∀ r : ℝ, 0 ≤ r → ∀ (i : M.coneWordIdeal C)
          (q : cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule),
          ‖(M.coneIdealBoxBasis C ((M.supportIn T hunimod eW).weightSupport E) β r).equivFun i‖ ≤ 1 →
          ‖bQ.equivFun q‖ ≤ 1 →
          ExpN (eN (i : cartanRootIdeal H)) *
            ExpN (eN (quotientLinearSection (M.coneWordIdeal C) bQ lift q)) ∈
              M.groupBox T hunimod eW (ExpN ∘ eN) E γ r R := by
  obtain ⟨bQ, lift, hlift, γ, hγ, hbox, K, hK, hbr⟩ :=
    M.exists_cone_adapted_path_basis C T hunimod eW bN bI E hs hzero β hβ
  obtain ⟨coeff, hcoeff, hprod⟩ := model_finiteDynkinExpansion dynkinN eN ExpN hExpN M.bound_zero 2
  have hmul (v w : cartanRootIdeal H) :
      ExpN (eN (finiteDynkinPolynomial coeff ![v, w])) = ExpN (eN v) * ExpN (eN w) := by
    simpa using (hprod ![v, w]).symm
  let R := sectionDynkinConstant
    (Fintype.card (Fin (finrank ℝ (M.coneWordIdeal C)) ⊕
      Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))) M.bound K *
        (1 + (1 : ℝ)) ^ M.bound
  have hR : 0 ≤ R := by dsimp [R, sectionDynkinConstant]; positivity
  refine ⟨bQ, lift, hlift, γ, R, hR, hγ, ?_⟩
  intro r hr i q hi hq
  rw [hbox]
  exact weighted_section_box_product (M.coneWordIdeal C)
    (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β)
    bQ lift hlift (ExpN ∘ eN) coeff hcoeff hmul
    (fun j => M.coneIdealWordCost C ((M.supportIn T hunimod eW).weightSupport E) (β.val j))
    K hK hbr r 1 hr zero_le_one i q hi hq

end PolycyclicRecognition.CartanWordModel

end

end OAI
