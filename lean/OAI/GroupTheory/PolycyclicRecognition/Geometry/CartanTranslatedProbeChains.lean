import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxProbeChains
import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledProbeChains
import OAI.GroupTheory.PolycyclicRecognition.Algebra.BoundedPrefixEnvelope

namespace OAI

/-! # Measurable translated probe chains with vanishing error -/

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

omit [SimplyConnectedSpace G] [FiniteDimensional ℝ W] [Nonempty (Fin M.letterCount)] in
/-- Translate an actual probe chain by its possibly probe-dependent base.
The exponential chart supplies measurable logarithms of all products, and
the polynomial product estimate supplies one vanishing error for every prefix. -/
theorem BoxProbeChains.exists_translated
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (γ : M.Bases) (t : Fin M.letterCount → ℝ)
    (hγ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (fun w => bracketWordExponent t w) γ.val)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale1 : ∀ n, 1 ≤ scale n)
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
    (probe : ∀ n, Y n → F.N.carrier)
    (P : M.BoxProbeChains T F hunimod eW b₀ E γ t scale probe)
    (base : ∀ n, Y n → cartanRootIdeal H)
    (hmeas : ∀ n, Measurable (fun q => b₀.equivFun (base n q)))
    (ε : ℕ → ℝ) (hε0 : ∀ n, 0 ≤ ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hbase : ∀ n q,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γ)
        (fun j => bracketWordExponent t (γ.val j)) (scale n)).equivFun (base n q)‖ ≤
          Real.exp (scale n * ε n)) :
    ∃ (η : ℕ → ℝ) (vertex : ∀ n, Y n → Fin (P.length + 1) → cartanRootIdeal H),
      (∀ n, 0 ≤ η n) ∧ Tendsto η atTop (𝓝 0) ∧
      (∀ n j, Measurable (fun q => b₀.equivFun (vertex n q j))) ∧
      (∀ n q, vertex n q 0 = base n q) ∧
      (∀ n q, F.ExpN (F.N.equiv (vertex n q (Fin.last P.length))) =
        F.ExpN (F.N.equiv (base n q)) * probe n q) ∧
      (∀ n q j,
        F.ExpN (F.N.equiv (vertex n q j)) =
          F.ExpN (F.N.equiv (base n q)) * F.ExpN (F.N.equiv (P.vertex n q j))) ∧
      (∀ n q j,
        ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γ)
          (fun j => bracketWordExponent t (γ.val j)) (scale n)).equivFun (vertex n q j)‖ ≤
            Real.exp (scale n * η n)) ∧
      ∀ n q j, F.ExpN (F.N.equiv (vertex n q j.succ)) =
        F.ExpN (F.N.equiv (vertex n q j.castSucc)) *
          F.ExpN (F.N.equiv (P.coefficient n q j • M.letter (P.mode n j))) := by
  obtain ⟨⟨chart, hchart⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  let coordinates : (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ≃ₜ F.N.carrier :=
    ((b₀.map F.N.equiv.toLinearEquiv).equivFun.symm.toContinuousLinearEquiv.toHomeomorph).trans chart
  have he (v : cartanRootIdeal H) :
      coordinates (b₀.equivFun v) = F.ExpN (F.N.equiv v) := by
    change chart (F.N.equiv (b₀.equivFun.symm (b₀.equivFun v))) = _
    rw [LinearEquiv.symm_apply_apply, hchart]
  let : SecondCountableTopology F.N.carrier := coordinates.symm.secondCountableTopology
  let : IsTopologicalGroup F.N.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  have hinj : Function.Injective (F.ExpN ∘ F.N.equiv) :=
    (funext hchart ▸ chart.injective).comp F.N.equiv.injective
  obtain ⟨ε₂, hε₂0, hε₂, hD⟩ := exists_vanishing_exponential_envelope
    scale hscale hscale1 P.prefixRadius
  obtain ⟨η, vertex, hη0, hη, hz, hprod, hb, hs⟩ :=
    exists_probe_translated_rescaled_chain dynkinN F.N.equiv F.ExpN F.isExpN M.letter
      M.bound_zero b₀ t γ hγ scale hscale hscale1 ε ε₂ hε0 hε₂0 hε hε₂ hinj
      base P.vertex hbase (fun n q j => (P.vertex_bound n q j).trans (hD n))
      P.vertex_zero (fun n q j => F.ExpN (F.N.equiv
        (P.coefficient n q j • M.letter (P.mode n j)))) P.vertex_step
  refine ⟨η, vertex, hη0, hη, ?_, hz, ?_, hprod, hb, hs⟩
  · intro n j
    have hf : Measurable (fun q => F.ExpN (F.N.equiv (base n q)) *
        F.ExpN (F.N.equiv (P.vertex n q j))) := by
      simp_rw [← he]
      exact (coordinates.continuous.measurable.comp (hmeas n)).mul
        (coordinates.continuous.measurable.comp (P.vertex_measurable n j))
    have heq : (fun q => b₀.equivFun (vertex n q j)) =
        fun q => coordinates.symm (F.ExpN (F.N.equiv (base n q)) *
          F.ExpN (F.N.equiv (P.vertex n q j))) := by
      funext q
      apply coordinates.injective
      exact (he (vertex n q j)).trans ((hprod n q j).trans
        (coordinates.apply_symm_apply _).symm)
    rw [heq]
    exact coordinates.symm.continuous.measurable.comp hf
  · intro n q
    exact (hprod n q (Fin.last P.length)).trans
      (congrArg (fun z => F.ExpN (F.N.equiv (base n q)) * z) (P.vertex_last n q))

end PolycyclicRecognition.CartanWordModel

end

end OAI
