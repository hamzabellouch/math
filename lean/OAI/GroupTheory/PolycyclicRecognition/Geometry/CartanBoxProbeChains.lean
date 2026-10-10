import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanProbeChainSequence

namespace OAI

/-! # Measurable chains for actual group-valued probes -/

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

/-- The data retained for each of the three probe templates. The common
length and constants are independent of the scale and the probe point. -/
structure BoxProbeChains
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (γ : M.Bases) (t : Fin M.letterCount → ℝ) (scale : ℕ → ℝ)
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
    (probe : ∀ n, Y n → F.N.carrier) where
  length : ℕ
  amplitude : ℝ
  prefixRadius : ℝ
  amplitude_ge_one : 1 ≤ amplitude
  prefixRadius_nonneg : 0 ≤ prefixRadius
  mode : ℕ → Fin length → Fin M.letterCount
  coefficient : ∀ n, Y n → Fin length → ℝ
  vertex : ∀ n, Y n → Fin (length + 1) → cartanRootIdeal H
  coefficient_measurable : ∀ n j, Measurable (fun q => coefficient n q j)
  vertex_measurable : ∀ n j, Measurable (fun q => b₀.equivFun (vertex n q j))
  coefficient_bound : ∀ n q j, |coefficient n q j| ≤ amplitude * Real.exp (scale n *
    (M.supportIn T hunimod eW).weightSupport E (mode n j))
  vertex_zero : ∀ n q, vertex n q 0 = 0
  vertex_last : ∀ n q, F.ExpN (F.N.equiv (vertex n q (Fin.last length))) = probe n q
  vertex_bound : ∀ n q j,
    ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γ)
      (fun k => bracketWordExponent t (γ.val k)) (scale n)).equivFun (vertex n q j)‖ ≤
      prefixRadius
  vertex_step : ∀ n q j, F.ExpN (F.N.equiv (vertex n q j.succ)) =
    F.ExpN (F.N.equiv (vertex n q j.castSucc)) *
      F.ExpN (F.N.equiv (coefficient n q j • M.letter (mode n j)))

/-- Actual Borel probe endpoints in the group box admit simultaneous
measurable generator chains. Coordinates are recovered through the
published exponential homeomorphism, so no logarithmic sampler is assumed. -/
theorem exists_actual_box_probe_chains
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
    (probe : ∀ n, Y n → F.N.carrier) (hp : ∀ n, Measurable (probe n))
    (hprobe : ∀ n q, probe n q ∈ M.groupBox T hunimod eW
      (F.ExpN ∘ F.N.equiv) E β (scale n) R) :
    ∃ (N : ℕ) (C D : ℝ), 1 ≤ C ∧ 0 ≤ D ∧
      ∃ (mode : ℕ → Fin N → Fin M.letterCount)
        (coeff : ∀ n, Y n → Fin N → ℝ)
        (vertex : ∀ n, Y n → Fin (N + 1) → cartanRootIdeal H),
        (∀ n j, Measurable (fun q => coeff n q j)) ∧
        (∀ n j, Measurable (fun q => b₀.equivFun (vertex n q j))) ∧
        (∀ n q j, |coeff n q j| ≤ C * Real.exp (scale n *
          (M.supportIn T hunimod eW).weightSupport E (mode n j))) ∧
        (∀ n q, vertex n q 0 = 0) ∧
        (∀ n q, F.ExpN (F.N.equiv (vertex n q (Fin.last N))) = probe n q) ∧
        (∀ n q j, ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γ)
          (fun k => bracketWordExponent t (γ.val k)) (scale n)).equivFun (vertex n q j)‖ ≤ D) ∧
        ∀ n q j, F.ExpN (F.N.equiv (vertex n q j.succ)) =
          F.ExpN (F.N.equiv (vertex n q j.castSucc)) *
            F.ExpN (F.N.equiv (coeff n q j • M.letter (mode n j))) := by
  obtain ⟨⟨chart, hchart⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  let coordinates (n : ℕ) : (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ≃ₜ F.N.carrier :=
    (((M.boxBasis T hunimod eW E β (scale n)).map F.N.equiv.toLinearEquiv).equivFun.symm.toContinuousLinearEquiv.toHomeomorph).trans chart
  have he (n : ℕ) (z : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) :
      coordinates n z = F.ExpN (F.N.equiv
        ((M.boxBasis T hunimod eW E β (scale n)).equivFun.symm z)) := by
    change chart _ = _
    rw [hchart]
    rfl
  have hbound (n : ℕ) (q : Y n) : ‖(coordinates n).symm (probe n q)‖ ≤ R := by
    obtain ⟨v, hv, hb⟩ := hprobe n q
    have hc : coordinates n ((M.boxBasis T hunimod eW E β (scale n)).equivFun v) =
        probe n q := by
      rw [he, LinearEquiv.symm_apply_apply]
      exact hv
    rw [← hc, Homeomorph.symm_apply_apply]
    exact hb
  let y (n : ℕ) (q : Y n) : closedBall
      (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) R :=
    ⟨(coordinates n).symm (probe n q), by simpa only [mem_closedBall_zero_iff] using hbound n q⟩
  have hy (n : ℕ) : Measurable (y n) :=
    ((coordinates n).symm.continuous.measurable.comp (hp n)).subtype_mk
  obtain ⟨N, C, D, hC, hD, mode, coeff, vertex, hc, hv, ha, hz, hend, hb, hs⟩ :=
    M.exists_measurable_probe_chain_sequence T F hunimod eW hExp realize haarN dynkinN
      b₀ E hE hne R hR β γ hβ t hst hγ scale hr y hy
  refine ⟨N, C, D, hC, hD, mode, coeff, vertex, hc, hv, ha, hz, ?_, hb, hs⟩
  intro n q
  rw [hend]
  exact (he n ((coordinates n).symm (probe n q))).symm.trans
    ((coordinates n).apply_symm_apply (probe n q))

omit [SimplyConnectedSpace G] [FiniteDimensional ℝ W] [Nonempty (Fin M.letterCount)] in
/-- Use the original quotient/kernel probability cell as the probe space.
Measurable reparametrization keeps every prefix, coefficient and endpoint,
so the independent probe law can be chosen directly on that cell. -/
def BoxProbeChains.reparametrize
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (γ : M.Bases) (t : Fin M.letterCount → ℝ) (scale : ℕ → ℝ)
    {Y Z : ℕ → Type*} [∀ n, MeasurableSpace (Y n)] [∀ n, MeasurableSpace (Z n)]
    (probe : ∀ n, Y n → F.N.carrier)
    (P : M.BoxProbeChains T F hunimod eW b₀ E γ t scale probe)
    (ψ : ∀ n, Z n → Y n) (hψ : ∀ n, Measurable (ψ n)) :
    M.BoxProbeChains T F hunimod eW b₀ E γ t scale (fun n z => probe n (ψ n z)) where
  length := P.length
  amplitude := P.amplitude
  prefixRadius := P.prefixRadius
  amplitude_ge_one := P.amplitude_ge_one
  prefixRadius_nonneg := P.prefixRadius_nonneg
  mode := P.mode
  coefficient := fun n z => P.coefficient n (ψ n z)
  vertex := fun n z => P.vertex n (ψ n z)
  coefficient_measurable := fun n j => (P.coefficient_measurable n j).comp (hψ n)
  vertex_measurable := fun n j => (P.vertex_measurable n j).comp (hψ n)
  coefficient_bound := fun n z => P.coefficient_bound n (ψ n z)
  vertex_zero := fun n z => P.vertex_zero n (ψ n z)
  vertex_last := fun n z => P.vertex_last n (ψ n z)
  vertex_bound := fun n z => P.vertex_bound n (ψ n z)
  vertex_step := fun n z => P.vertex_step n (ψ n z)

/-- Package the actual chains so the three templates can share their
samplers while retaining their individual fixed lengths. -/
theorem nonempty_boxProbeChains
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
    (probe : ∀ n, Y n → F.N.carrier) (hp : ∀ n, Measurable (probe n))
    (hprobe : ∀ n q, probe n q ∈ M.groupBox T hunimod eW
      (F.ExpN ∘ F.N.equiv) E β (scale n) R) :
    Nonempty (M.BoxProbeChains T F hunimod eW b₀ E γ t scale probe) := by
  obtain ⟨N, C, D, hC, hD, mode, coeff, vertex, hc, hv, ha, hz, hend, hb, hs⟩ :=
    M.exists_actual_box_probe_chains T F hunimod eW hExp realize haarN dynkinN
      b₀ E hE hne R hR β γ hβ t hst hγ scale hr probe hp hprobe
  exact ⟨⟨N, C, D, hC, hD, mode, coeff, vertex, hc, hv, ha, hz, hend, hb, hs⟩⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
