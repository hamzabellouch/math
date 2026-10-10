import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanDominatedGeneratorChain
import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledTranslatedChains
import OAI.GroupTheory.PolycyclicRecognition.Algebra.BoundedPrefixEnvelope

namespace OAI

/-! # Actual generator chains attached to an arbitrary allowed sheet suffix -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule Filter
open scoped Manifold Topology

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

include T in
/-- A box increment is generated inside an arbitrary allowed suffix, with
one error envelope for all resulting sheet prefixes. The generation and
ambient box templates may differ, as in the three probe paths in the
neighboring-offset argument. -/
theorem exists_cartan_suffix_generator_sequence
    [Nonempty (Fin M.letterCount)]
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (R : ℝ) :
    ∃ (N : ℕ) (C : ℝ), 1 ≤ C ∧
      ∀ (s t : Fin M.letterCount → ℝ), (∀ i, s i ≤ t i) → ∀ (β γ : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent s w) β.val →
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent t w) γ.val →
      ∀ (scale : ℕ → ℝ), Tendsto scale atTop atTop → (∀ n, 1 ≤ scale n) →
      ∀ (ε₀ : ℕ → ℝ), (∀ n, 0 ≤ ε₀ n) → Tendsto ε₀ atTop (𝓝 0) →
      ∀ (base : ℕ → cartanRootIdeal H),
      (∀ n, ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γ)
        (fun j => bracketWordExponent t (γ.val j)) (scale n)).equivFun (base n)‖ ≤
          Real.exp (scale n * ε₀ n)) →
      ∀ (K : Type*) (v : ℕ → K → cartanRootIdeal H),
      (∀ n q, ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => bracketWordExponent s (β.val j)) (scale n)).equivFun (v n q)‖ ≤ R) →
      ∃ (ε : ℕ → ℝ) (vertex : ℕ → K → Fin (N + 1) → cartanRootIdeal H)
        (mode : ℕ → K → Fin N → Fin M.letterCount) (coeff : ℕ → K → Fin N → ℝ),
        (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
        (∀ n q, vertex n q 0 = base n) ∧
        (∀ n q, F.ExpN (F.N.equiv (vertex n q (Fin.last N))) =
          F.ExpN (F.N.equiv (base n)) * F.ExpN (F.N.equiv (v n q))) ∧
        (∀ n q j, ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γ)
          (fun j => bracketWordExponent t (γ.val j)) (scale n)).equivFun (vertex n q j)‖ ≤
            Real.exp (scale n * ε n)) ∧
        (∀ n q j, |coeff n q j| ≤ C * Real.exp (scale n * (s (mode n q j) + ε n))) ∧
        (∀ n q j, F.ExpN (F.N.equiv (vertex n q j.succ)) =
          F.ExpN (F.N.equiv (vertex n q j.castSucc)) *
            F.ExpN (F.N.equiv (coeff n q j • M.letter (mode n q j)))) := by
  classical
  obtain ⟨N, C, D, hC, _, hchain⟩ := M.exists_uniform_dominated_cartan_chain T F
    hExpG realize haarN dynkinN b₀ R
  refine ⟨N, C, hC, ?_⟩
  intro s t hst β γ hβ hγ scale hscale hscale1 ε₀ hε₀0 hε₀ base hbase K v hv
  have hchains (n : ℕ) (q : K) := hchain s t hst β γ hβ hγ (scale n)
    (le_trans (by norm_num) (hscale1 n)) (v n q) (hv n q)
  choose u vertex hlen hamp hzero hend hbound hstep using hchains
  obtain ⟨ε₂, hε₂0, hε₂, hD⟩ := exists_vanishing_exponential_envelope scale hscale hscale1 D
  let step := fun n q (j : Fin N) => (u n q)[j.val]'(by rw [hlen]; exact j.isLt)
  let mode := fun n q (j : Fin N) => (step n q j).1
  let coeff := fun n q (j : Fin N) =>
    (step n q j).2 * Real.exp (scale n * s (mode n q j))
  have hsteps (n : ℕ) (q : K) (j : Fin N) :
      F.ExpN (F.N.equiv (vertex n q (j.val + 1))) =
      F.ExpN (F.N.equiv (vertex n q j.val)) *
        F.ExpN (F.N.equiv (coeff n q j • M.letter (mode n q j))) := by
    have hs := hstep n q j.val (by rw [hlen]; exact j.isLt)
    simpa only [step, mode, coeff, smul_smul] using hs
  obtain ⟨⟨chart, hchart⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  have hinj : Function.Injective (F.ExpN ∘ F.N.equiv) :=
    (funext hchart ▸ chart.injective).comp F.N.equiv.injective
  obtain ⟨ε, translated, hε0, hε, hstart, hmul, htransBound, htransStep⟩ :=
    exists_translated_rescaled_chain dynkinN F.N.equiv F.ExpN F.isExpN M.letter
      M.bound_zero b₀ t γ hγ scale hscale hscale1 ε₀ ε₂ hε₀0 hε₂0 hε₀ hε₂ hinj
      base (fun n q (j : Fin (N + 1)) => vertex n q j.val) hbase
      (fun n q j => (hbound n q j.val).trans (hD n)) hzero
      (fun n q j => F.ExpN (F.N.equiv (coeff n q j • M.letter (mode n q j)))) hsteps
  refine ⟨ε, translated, mode, coeff, hε0, hε, hstart, ?_, htransBound, ?_, htransStep⟩
  · intro n q
    simpa only [Fin.val_last, hend] using hmul n q (Fin.last N)
  · intro n q j
    have ha : |(step n q j).2| ≤ C := hamp n q _ (List.getElem_mem _)
    have hr : 0 ≤ scale n := le_trans (by norm_num) (hscale1 n)
    dsimp only [coeff]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul ha (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (hε0 n)) hr)) (Real.exp_pos _).le
    exact (by norm_num : (0 : ℝ) ≤ 1).trans hC

end PolycyclicRecognition.CartanWordModel

end

end OAI
