import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanJacobian
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanActualConjugation
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentHaarAutomorphisms

namespace OAI

/-! # A common Haar measure for Cartan boxes and conjugation

The determinant computation gives exact invariance under the actual Cartan
adjoint automorphisms. The same measure retains the explicit weighted-box
volume, so the lower packing argument and box rates use compatible measures.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory
open scoped Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  [hNsc : SimplyConnectedSpace N] [MeasurableSpace N] [BorelSpace N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
  (hbij : Function.Bijective Exp) (dynkin : NilpotentDynkinExpansionInput EN N)
  (haar : NilpotentExponentialHaarInput EN N)

include hunimod haar hNsc

/-- One Haar measure has both the exact word-box formula and invariance
under every Cartan adjoint action. -/
theorem exists_haar_adjoint_invariant_weighted_boxes
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ μ : Measure N, μ.IsHaarMeasure ∧
      (∀ h : H, MeasurePreserving (M.adjointGroupAutomorphism T eN Exp hExp hbij dynkin h) μ μ) ∧
      ∀ (cost : M.wordList → ℝ) (β : M.Bases) (r R : ℝ), 0 ≤ R →
        μ (exponentialCoordinateBox (Exp ∘ eN)
          (exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
            (fun i => cost (β.val i)) r) R) =
          ENNReal.ofReal |(columnBasisMatrix (wordListCoordinates M.letter M.wordList b₀) β.val).det| *
            ENNReal.ofReal (Real.exp (r * columnBasisWeight cost β.val)) *
              ENNReal.ofReal (2 * R) ^ finrank ℝ (cartanRootIdeal H) := by
  let _ : SimplyConnectedSpace N := hNsc
  have hn : LieRing.IsNilpotent (cartanRootIdeal H) :=
    (LieModule.isNilpotent_iff ℝ _ _).mpr ⟨M.bound, M.bound_zero⟩
  obtain ⟨⟨chart, hc⟩, hhaar⟩ := haar.2 Exp hExp (eN.nilpotent_iff_equiv_nilpotent.mp hn)
  let b := b₀.map eN.toLinearEquiv
  let f := (Exp ∘ eN) ∘ b₀.equivFun.symm
  have hf : f = Exp ∘ b.equivFun.symm := by
    funext t
    change Exp (eN (b₀.equivFun.symm t)) = Exp ((b₀.map eN.toLinearEquiv).equivFun.symm t)
    rw [Basis.map_equivFun]
    rfl
  refine ⟨Measure.map f volume, ?_, ?_, ?_⟩
  · rw [hf]
    exact hhaar _ b
  · intro h
    exact exponentialConjugate_measurePreserving eN Exp hbij chart hc b₀
      (cartanIdealAdjointAutomorphism T H h) (M.det_idealAdjointAutomorphism_eq_one T hunimod h)
  · intro cost β r R hR
    exact exponentialCoordinate_weighted_box_measure eN Exp chart hc b₀ M.letter M.wordList
      cost β r R hR

/-- The conjugation-invariant Haar measure has the same exponential lower
and upper rates as all maximizing Cartan boxes. -/
theorem exists_haar_adjoint_invariant_box_bounds
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (eW : HeightSpace T.character ≃ₗ[ℝ] W)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ (μ : Measure N) (c C : ℝ), μ.IsHaarMeasure ∧ 0 < c ∧ 0 < C ∧
      (∀ h : H, MeasurePreserving (M.adjointGroupAutomorphism T eN Exp hExp hbij dynkin h) μ μ) ∧
      ∀ (E : Set W) (β : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ (r R : ℝ), 0 ≤ R →
        ENNReal.ofReal c * ENNReal.ofReal (Real.exp (r * (M.supportIn T hunimod eW).templateSupport E)) *
          ENNReal.ofReal (2 * R) ^ finrank ℝ (cartanRootIdeal H) ≤
            μ (M.groupBox T hunimod eW (Exp ∘ eN) E β r R) ∧
        μ (M.groupBox T hunimod eW (Exp ∘ eN) E β r R) ≤
          ENNReal.ofReal C * ENNReal.ofReal (Real.exp (r * (M.supportIn T hunimod eW).templateSupport E)) *
            ENNReal.ofReal (2 * R) ^ finrank ℝ (cartanRootIdeal H) := by
  obtain ⟨μ, hμ, hinv, hvol⟩ := M.exists_haar_adjoint_invariant_weighted_boxes T hunimod
    eN Exp hExp hbij dynkin haar b₀
  obtain ⟨c, C, hc, hC, hdet⟩ := M.exists_uniform_wordBasis_determinant_bounds b₀
  refine ⟨μ, c, C, hμ, hc, hC, hinv, ?_⟩
  intro E β hβ r R hR
  have hv := hvol (M.boxCost T hunimod eW E) β r R hR
  rw [M.columnBasisWeight_eq_templateSupport_of_maximizing T hunimod eW b₀ E β hβ] at hv
  change μ (M.groupBox T hunimod eW (Exp ∘ eN) E β r R) = _ at hv
  rw [hv]
  constructor
  · exact mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal (hdet β).1) le_rfl) le_rfl
  · exact mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal (hdet β).2) le_rfl) le_rfl

end PolycyclicRecognition.CartanWordModel

end

end OAI
