import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGeneratorChain
import OAI.GroupTheory.PolycyclicRecognition.Analysis.GeneratorPrefixChain
import OAI.GroupTheory.PolycyclicRecognition.Algebra.BoundedPrefixEnvelope

namespace OAI

/-! # Uniform finite generator chains along the geometric scale sequence -/

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
/-- All endpoints in one rescaled box admit chains of the same finite
length. One vanishing error envelope bounds every prefix, uniformly over
all endpoint choices. No measurable choice of the chains is asserted or
needed for deterministic subsequence arguments. -/
theorem exists_cartan_generator_sequence
    [Nonempty (Fin M.letterCount)]
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (R : ℝ) :
    ∃ (N : ℕ) (C : ℝ), 1 ≤ C ∧
      ∀ (s : Fin M.letterCount → ℝ) (β : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent s w) β.val →
      (∀ j, 0 ≤ bracketWordExponent s (β.val j)) →
      ∀ (scale : ℕ → ℝ), Tendsto scale atTop atTop → (∀ n, 1 ≤ scale n) →
      ∀ (δ : ℝ), 0 ≤ δ → ∀ (K : Type*) (v : ℕ → K → cartanRootIdeal H),
      (∀ n q, ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => bracketWordExponent s (β.val j)) (scale n)).equivFun (v n q)‖ ≤ R) →
      ∃ (ε : ℕ → ℝ) (vertex : ℕ → K → ℕ → cartanRootIdeal H)
        (mode : ℕ → K → Fin N → Fin M.letterCount) (coeff : ℕ → K → Fin N → ℝ),
        (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
        (∀ n q, vertex n q 0 = 0 ∧ vertex n q N = v n q) ∧
        (∀ n q j, ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
          (fun j => (1 + δ) * bracketWordExponent s (β.val j)) (scale n)).equivFun
            (vertex n q j)‖ ≤ Real.exp (scale n * ε n)) ∧
        (∀ n q j, |coeff n q j| ≤ C * Real.exp (scale n * s (mode n q j))) ∧
        (∀ n q j, F.ExpN (F.N.equiv (vertex n q (j.val + 1))) =
          F.ExpN (F.N.equiv (vertex n q j.val)) *
            F.ExpN (F.N.equiv (coeff n q j • M.letter (mode n q j)))) := by
  classical
  obtain ⟨N, C, D, hC, _, hchain⟩ := M.exists_uniform_cartan_generator_chain T F
    hExpG realize haarN dynkinN b₀ R
  refine ⟨N, C, hC, ?_⟩
  intro s β hβ hcost scale hscale hscale1 δ hδ K v hv
  have hchains (n : ℕ) (q : K) := hchain s β hβ (scale n)
    (le_trans (by norm_num) (hscale1 n)) (v n q) (hv n q)
  choose u vertex hlen hamp hzero hend hbound hstep using hchains
  obtain ⟨ε, hε0, hε, henv⟩ := enlarged_prefix_vanishing_envelope
    (fun _ => WordBasisSelections.basis M.letter M.wordList β)
    (fun _ j => bracketWordExponent s (β.val j)) (fun _ => hcost)
    scale hscale hscale1 (fun n (qj : K × ℕ) => vertex n qj.1 qj.2) D
    (fun n qj => hbound n qj.1 qj.2) hδ
  let step := fun n q (j : Fin N) => (u n q)[j.val]'(by rw [hlen]; exact j.isLt)
  let mode := fun n q (j : Fin N) => (step n q j).1
  let coeff := fun n q (j : Fin N) =>
    (step n q j).2 * Real.exp (scale n * s (mode n q j))
  refine ⟨ε, vertex, mode, coeff, hε0, hε, fun n q => ⟨hzero n q, hend n q⟩,
    fun n q j => henv n (q, j), ?_, ?_⟩
  · intro n q j
    have ha : |(step n q j).2| ≤ C := hamp n q _ (List.getElem_mem _)
    dsimp only [coeff]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right ha (Real.exp_pos _).le
  · intro n q j
    have hs := hstep n q j.val (by rw [hlen]; exact j.isLt)
    simpa only [step, mode, coeff, smul_smul] using hs

end PolycyclicRecognition.CartanWordModel

end

end OAI
