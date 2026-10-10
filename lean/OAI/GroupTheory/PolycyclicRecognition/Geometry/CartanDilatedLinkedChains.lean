import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanLinkedProbeChains
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanDilatedProbeChains
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanAllowedProbeChains

namespace OAI

/-! # Actual linked samplers in the enlarged sampling coordinates -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter
open scoped Manifold Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

omit [SimplyConnectedSpace G] [Nonempty (Fin M.letterCount)] in
/-- Dilate all three normalized chains to the actual contact pivot, put
all their prefixes in the enlarged sampling box, and attach the two original
allowed suffixes. The produced linked chains retain the exact sampled group
endpoints. -/
theorem exists_dilated_linked_probe_chains
    (hbij : Function.Bijective F.ExpN)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (B C : Set W)
    (hE : ∀ k, IsCompact (E k)) (hne : ∀ k, (E k).Nonempty)
    (hB : IsCompact B) (hBne : B.Nonempty) (hC : IsCompact C)
    (w : W) (hBC : (fun x => x + w) '' B ⊆ C)
    (hw : ∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport C i)
    (γ β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW C) β.val)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale1 : ∀ n, 1 ≤ scale n)
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
    (probe : Fin 3 → ∀ n, Y n → F.N.carrier)
    (P : ∀ k, M.BoxProbeChains T F hunimod eW b₀ (E k) γ
      ((M.supportIn T hunimod eW).weightSupport B) scale (probe k))
    (origin base : ∀ n, Y n → cartanRootIdeal H)
    (horiginMeas : ∀ n, Measurable (fun y => b₀.equivFun (origin n y)))
    (hbaseMeas : ∀ n, Measurable (fun y => b₀.equivFun (base n y)))
    (ε : ℕ → ℝ) (hε0 : ∀ n, 0 ≤ ε n) (hε : Tendsto ε atTop (𝓝 0))
    (horigin : ∀ n y,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => (1 + δ) * M.boxCost T hunimod eW C (β.val j)) (scale n)).equivFun
          (origin n y)‖ ≤ Real.exp (scale n * ε n))
    (hbase : ∀ n y,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => (1 + δ) * M.boxCost T hunimod eW C (β.val j)) (scale n)).equivFun
          (base n y)‖ ≤ Real.exp (scale n * ε n)) :
    let S := fun n => integrateNilpotentLieEquiv F.N.equiv F.ExpN hbij dynkinN F.isExpN
      M.bound_zero (cartanIdealWeightDilation T H
        (scale n • cartanHeightSection T H (eW.symm w)))
    let E' := fun k => (fun x => x + w) '' E k
    let probe' := fun k n y => S n (probe k n y)
    let t := fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport C i
    ∃ (P' : ∀ k, M.BoxProbeChains T F hunimod eW b₀ (E' k) β t scale (probe' k))
      (η : ℕ → ℝ), (∀ n, 0 ≤ η n) ∧ Tendsto η atTop (𝓝 0) ∧
      Nonempty (M.LinkedProbeChains T F hunimod eW b₀ E' β t scale probe' P' origin base η) := by
  classical
  dsimp only
  let E' := fun k => (fun x => x + w) '' E k
  let B' := (fun x => x + w) '' B
  let t := fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport C i
  let S := fun n => integrateNilpotentLieEquiv F.N.equiv F.ExpN hbij dynkinN F.isExpN
    M.bound_zero (cartanIdealWeightDilation T H
      (scale n • cartanHeightSection T H (eW.symm w)))
  let probe' := fun k n y => S n (probe k n y)
  have hdom (i) : (M.supportIn T hunimod eW).weightSupport B' i ≤
      (M.supportIn T hunimod eW).weightSupport C i :=
    (M.supportIn T hunimod eW).weightSupport_mono
      (hB.image (continuous_id.add_const w)) (hBne.image _) hC hBC i
  let P' (k : Fin 3) : M.BoxProbeChains T F hunimod eW b₀ (E' k) β t scale (probe' k) :=
    BoxProbeChains.inSamplingBox T M F hunimod eW b₀ (E' k) C γ β
      ((M.supportIn T hunimod eW).weightSupport B') hβ hdom hw hδ scale
      (fun n => le_trans zero_le_one (hscale1 n)) (probe' k)
      (BoxProbeChains.dilate T M F hunimod eW hbij dynkinN b₀ (E k) B
        (hE k) (hne k) hB hBne w γ scale (probe k) (P k))
  have hscaled : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (fun q => bracketWordExponent t q) β.val := by
    refine ⟨hβ.1, ?_⟩
    intro β' hβ'
    simp only [t, columnBasisWeight, bracketWordExponent_const_mul, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hβ.2 β' hβ') (by linarith)
  have hbefore : ∀ n y,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => bracketWordExponent t (β.val j)) (scale n)).equivFun (origin n y)‖ ≤
          Real.exp (scale n * ε n) := by
    simpa only [t, bracketWordExponent_const_mul, boxCost] using horigin
  have hafter : ∀ n y,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => bracketWordExponent t (β.val j)) (scale n)).equivFun (base n y)‖ ≤
          Real.exp (scale n * ε n) := by
    simpa only [t, bracketWordExponent_const_mul, boxCost] using hbase
  obtain ⟨η, hη0, hη, hD⟩ := M.exists_linked_probe_chains T F hunimod eW
    haarN dynkinN b₀ E' β t hscaled scale hscale hscale1 probe' P'
    origin base horiginMeas hbaseMeas ε hε0 hε hbefore hafter
  exact ⟨P', η, hη0, hη, hD⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
