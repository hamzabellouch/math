import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConeSectionBasis
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGroupBoxes

namespace OAI

/-! # One adapted basis for path lifting and ideal bridge absorption

The maximizing ambient word basis and the ideal/quotient basis describe
exactly the same boxes. Keeping this identification prevents a change of
coordinates from introducing an extra exponential error in the bridge.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Set

variable {V I J : Type*} [LieRing V] [LieAlgebra ℝ V] [Fintype I] [Fintype J]

/-- Reindexing a finite basis preserves its coordinate supremum norm. -/
theorem norm_basis_equivFun_reindex (b : Basis I ℝ V) (e : I ≃ J) (v : V) :
    ‖(b.reindex e).equivFun v‖ = ‖b.equivFun v‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    simpa only [Basis.equivFun_apply, Basis.repr_reindex_apply] using
      norm_le_pi_norm (b.equivFun v) (e.symm j)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa only [Basis.equivFun_apply, Basis.repr_reindex_apply,
      Equiv.symm_apply_apply] using
      norm_le_pi_norm ((b.reindex e).equivFun v) (e i)

/-- Consequently the actual exponential coordinate boxes are unchanged. -/
theorem exponentialCoordinateBox_reindex {N : Type*} (Exp : V → N)
    (b : Basis I ℝ V) (e : I ≃ J) (R : ℝ) :
    exponentialCoordinateBox Exp (b.reindex e) R = exponentialCoordinateBox Exp b R := by
  ext n
  simp only [exponentialCoordinateBox, norm_basis_equivFun_reindex]

namespace CartanWordModel

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (LieAlgebra.ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The same ideal-maximizing choice supplies an ambient path box, an exact
ideal/quotient coordinate identification and a uniform bracket bound. -/
theorem exists_cone_adapted_path_basis
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (E : Set W)
    (hs : ∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport E i)
    (hzero : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
      (M.supportIn T hunimod eW).weightSupport E i = 0)
    (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C bI
      ((M.supportIn T hunimod eW).weightSupport E) β) :
    ∃ (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
        ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
      (lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
        cartanRootIdeal H),
      ∃ hlift : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j,
      ∃ γ : M.Bases,
        IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
          (M.boxCost T hunimod eW E) γ.val ∧
        (∀ {N : Type*} (Exp : cartanRootIdeal H → N) (r R : ℝ),
          M.groupBox T hunimod eW Exp E γ r R =
          exponentialCoordinateBox Exp
            (exponentialRescaleBasis
              (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule
                (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β)
                bQ lift hlift)
              (Sum.elim
                (fun j => M.coneIdealWordCost C
                  ((M.supportIn T hunimod eW).weightSupport E) (β.val j))
                (fun _ => 0)) r) R) ∧
        ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, 0 ≤ r →
          let B := exponentialRescaleBasis
            (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule
              (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β)
              bQ lift hlift)
            (Sum.elim
              (fun j => M.coneIdealWordCost C
                ((M.supportIn T hunimod eW).weightSupport E) (β.val j))
              (fun _ => 0)) r
          ∀ i j k, |B.repr ⁅B i, B j⁆ k| ≤ K := by
  obtain ⟨bQ, q, _hpure, hq, e, γ, hγ, hcost, hmax, _hsum⟩ :=
    M.exists_cone_adapted_maximal_basis_data C bN bI
      ((M.supportIn T hunimod eW).weightSupport E) hs hzero β hβ
  obtain ⟨K, hK, hbound⟩ := exists_uniform_rescaled_structureConstant_bound
    M.letter M.bound_zero bN
  let B := basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule
    (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β)
    bQ (fun j => evalBracketWord M.letter (q j)) hq
  let cost : (Fin (finrank ℝ (M.coneWordIdeal C)) ⊕
      Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))) → ℝ := Sum.elim
    (fun j => M.coneIdealWordCost C
      ((M.supportIn T hunimod eW).weightSupport E) (β.val j)) (fun _ => (0 : ℝ))
  have heq (r : ℝ) : M.boxBasis T hunimod eW E γ r =
      (exponentialRescaleBasis B cost r).reindex e := by
    change exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γ)
      (fun j => bracketWordExponent ((M.supportIn T hunimod eW).weightSupport E)
        (γ.val j)) r = _
    rw [hγ]
    simp_rw [hcost]
    exact exponentialRescaleBasis_reindex B cost e r
  refine ⟨bQ, (fun j => evalBracketWord M.letter (q j)), hq, γ, hmax, ?_, K, hK, ?_⟩
  · intro N Exp r R
    change exponentialCoordinateBox Exp (M.boxBasis T hunimod eW E γ r) R = _
    rw [heq, exponentialCoordinateBox_reindex]
  · intro r hr
    dsimp only
    intro i j k
    have hh := hbound ((M.supportIn T hunimod eW).weightSupport E) γ hmax r hr
      (e i) (e j) (e k)
    change |(M.boxBasis T hunimod eW E γ r).repr
      ⁅M.boxBasis T hunimod eW E γ r (e i), M.boxBasis T hunimod eW E γ r (e j)⁆
        (e k)| ≤ K at hh
    rw [heq] at hh
    simpa only [Basis.reindex_apply, Basis.repr_reindex_apply,
      Equiv.symm_apply_apply] using hh

end CartanWordModel
end PolycyclicRecognition

end

end OAI
