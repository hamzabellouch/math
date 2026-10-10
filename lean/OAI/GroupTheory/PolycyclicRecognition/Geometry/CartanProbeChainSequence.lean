import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanMeasurableBoxChains

namespace OAI

/-! # Uniform measurable chains for varying probe spaces -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric
open scoped Manifold

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

/-- Varying compact probe spaces at every scale use one common chain
length and amplitude bound. The canonical coordinate-ball selector is
chosen once and then composed with each actual Borel probe sampler. -/
theorem exists_measurable_probe_chain_sequence
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (hE : IsCompact E) (hne : E.Nonempty) (R : ℝ) (hR : 0 ≤ R)
    (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (t : Fin M.letterCount → ℝ)
    (hst : ∀ i, (M.supportIn T hunimod eW).weightSupport E i ≤ t i)
    (hγ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (fun w => bracketWordExponent t w) γ.val)
    (scale : ℕ → ℝ) (hr : ∀ n, 0 ≤ scale n)
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
    (y : ∀ n, Y n → closedBall (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) R)
    (hy : ∀ n, Measurable (y n)) :
    ∃ (N : ℕ) (C D : ℝ), 1 ≤ C ∧ 0 ≤ D ∧
      ∃ (mode : ℕ → Fin N → Fin M.letterCount)
        (coeff : ∀ n, Y n → Fin N → ℝ)
        (vertex : ∀ n, Y n → Fin (N + 1) → cartanRootIdeal H),
        (∀ n j, Measurable (fun q => coeff n q j)) ∧
        (∀ n j, Measurable (fun q => b₀.equivFun (vertex n q j))) ∧
        (∀ n q j, |coeff n q j| ≤ C * Real.exp (scale n *
          (M.supportIn T hunimod eW).weightSupport E (mode n j))) ∧
        (∀ n q, vertex n q 0 = 0) ∧
        (∀ n q, vertex n q (Fin.last N) =
          (M.boxBasis T hunimod eW E β (scale n)).equivFun.symm (y n q).val) ∧
        (∀ n q j, ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γ)
          (fun k => bracketWordExponent t (γ.val k)) (scale n)).equivFun (vertex n q j)‖ ≤ D) ∧
        ∀ n q j, F.ExpN (F.N.equiv (vertex n q j.succ)) =
          F.ExpN (F.N.equiv (vertex n q j.castSucc)) *
            F.ExpN (F.N.equiv (coeff n q j • M.letter (mode n j))) := by
  let Z := closedBall (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) R
  obtain ⟨N, C, D, hC, hD, hchain⟩ :=
    M.exists_measurable_box_generator_chain (A := Z) T F hunimod eW
      hExp realize haarN dynkinN b₀ E hE hne R hR
  have hn (n : ℕ) := hchain (scale n) (hr n) β γ hβ t hst hγ (fun z : Z => z) measurable_id
  choose mode coeff vertex hc hv ha hz he hb hs using hn
  refine ⟨N, C, D, hC, hD, mode, (fun n q => coeff n (y n q)),
    (fun n q => vertex n (y n q)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n j
    exact (hc n j).comp (hy n)
  · intro n j
    exact (hv n j).comp (hy n)
  · intro n q j
    exact ha n (y n q) j
  · intro n q
    exact hz n (y n q)
  · intro n q
    exact he n (y n q)
  · intro n q j
    exact hb n (y n q) j
  · intro n q j
    exact hs n (y n q) j

end PolycyclicRecognition.CartanWordModel

end

end OAI
