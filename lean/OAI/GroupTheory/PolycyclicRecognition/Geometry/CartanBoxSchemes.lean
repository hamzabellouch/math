import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledSubmersiveScheme
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGeneratorSchemes
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxExponents
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoordinateChartSampling

namespace OAI

/-! # Fixed submersive words in the actual Cartan box coordinates -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Filter Set
open scoped Manifold Topology Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The endpoint word is fixed from the limiting genuine Cartan box law.
The only external inputs are the stated exponential realization and Haar
chart, which provide the faithful realization and injective exponential. -/
theorem exists_box_normalized_bound
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (b : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {c : ℕ} (aN : DynkinCoefficients c 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (E : Set W) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b)
      (M.boxCost T hunimod eW E) β.val)
    : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
      rescaledLieData M.letter M.wordList β ((M.supportIn T hunimod eW).weightSupport E) r ∈
        normalizedExponentialParameters aN
          (fun i => (β.val i : FreeMagma (Fin M.letterCount))) (fun i => Pi.single i 1) C := by
  obtain ⟨d, hd, ρ, j, hind, hmatch⟩ := realize ⟨a, ⟨T⟩⟩ Exp hExp
  let _ : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin d) (Fin d) ℝ)ˣ =>
      (u : Matrix (Fin d) (Fin d) ℝ)) he)
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  have hinj : Function.Injective (F.ExpN ∘ F.N.equiv) :=
    ((funext hchartN ▸ chartN.bijective).comp F.N.equiv.bijective).injective
  have hmul (x y : cartanRootIdeal H) :
      (F.ExpN ∘ F.N.equiv) (finiteDynkinPolynomial aN ![x, y]) =
        (F.ExpN ∘ F.N.equiv) x * (F.ExpN ∘ F.N.equiv) y :=
    model_binary_dynkin F.N.equiv F.ExpN aN hm x y
  obtain ⟨C, hC, hb⟩ := exists_rescaledExponentialData_bound M.letter M.bound_zero M.letter_mem_wordList b
    (F.ExpN ∘ F.N.equiv) hinj (by simp [F.isExpN.map_zero])
    (fun x => by simp [F.isExpN.map_neg])
    (fun x s t => by
      simpa only [Function.comp_apply, map_smul] using F.isExpN.map_add_smul (F.N.equiv x) s t)
    aN hmul (j.comp (cartanRootIdeal H).incl) (ρ.comp F.inclusionN)
    (hρ.comp F.closedN.injective) (fun x => by
      change ρ (F.inclusionN (F.ExpN (F.N.equiv x))) = _
      rw [F.compatibleN, hmatch]
      rfl)

  exact ⟨C, hC, fun r hr => hb ((M.supportIn T hunimod eW).weightSupport E) β hβ r hr⟩


/-- The endpoint word is fixed from the limiting genuine Cartan box law.
The only external inputs are the stated exponential realization and Haar
chart, which provide the faithful realization and injective exponential. -/
theorem exists_box_submersive_scheme
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (b : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {c : ℕ} (aN : DynkinCoefficients c 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (E : Set W) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b)
      (M.boxCost T hunimod eW E) β.val)
    (scale : ℕ → ℝ) (hscale : ∀ n, 0 ≤ scale n) :
    ∃ C : ℝ, 0 ≤ C ∧ HasSubmersiveWordSubsequence aN
      (normalizedExponentialParameters aN (fun i => (β.val i : FreeMagma (Fin M.letterCount)))
        (fun i => Pi.single i 1) C)
      (fun n => rescaledLieData M.letter M.wordList β
        ((M.supportIn T hunimod eW).weightSupport E) (scale n)) := by
  obtain ⟨C, hC, hb⟩ := M.exists_box_normalized_bound T F hunimod eW hExp realize haarN
    b aN hm E β hβ
  refine ⟨C, hC, ?_⟩
  exact exists_submersive_scheme_of_normalized_sequence aN
    (fun i => (β.val i : FreeMagma (Fin M.letterCount))) C
    (fun n => rescaledLieData M.letter M.wordList β
      ((M.supportIn T hunimod eW).weightSupport E) (scale n))
    (fun n => hb (scale n) (hscale n))

end PolycyclicRecognition.CartanWordModel

end

end OAI
