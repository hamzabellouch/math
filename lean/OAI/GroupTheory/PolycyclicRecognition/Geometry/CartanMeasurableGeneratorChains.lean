import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanMeasurableTemplateCoding
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MeasurableGeneratorChain
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DominatedWordPrefixes
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

namespace OAI

/-! # Measurable actual Cartan chains with uniform prefix control -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule Metric
open scoped Manifold

variable {EG G A : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [MeasurableSpace A]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

include T in
/-- A sampled template endpoint admits a measurable chain of fixed length.
Every actual logarithmic prefix lies in a uniformly bounded larger box. -/
theorem exists_measurable_template_generator_chain
    [Nonempty (Fin M.letterCount)]
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (v : Fin M.letterCount → H) (R : ℝ) (hR : 0 ≤ R) :
    ∃ (N : ℕ) (C D : ℝ), 1 ≤ C ∧ 0 ≤ D ∧
      ∀ r : ℝ, 0 ≤ r → ∀ (β γ : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent (M.templateSupportExponent v) w) β.val →
      ∀ t : Fin M.letterCount → ℝ, (∀ i, M.templateSupportExponent v i ≤ t i) →
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent t w) γ.val →
      let b := exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => bracketWordExponent (M.templateSupportExponent v) (β.val j)) r
      ∀ y : A → closedBall (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) R,
        Measurable y →
      ∃ (mode : Fin N → Fin M.letterCount) (coeff : A → Fin N → ℝ)
        (vertex : A → Fin (N + 1) → cartanRootIdeal H),
        (∀ j, Measurable (fun q => coeff q j)) ∧
        (∀ j, Measurable (fun q => b₀.equivFun (vertex q j))) ∧
        (∀ q j, |coeff q j| ≤ C * Real.exp (r * M.templateSupportExponent v (mode j))) ∧
        (∀ q, vertex q 0 = 0) ∧
        (∀ q, vertex q (Fin.last N) = b.equivFun.symm (y q).val) ∧
        (∀ q j, ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γ)
          (fun k => bracketWordExponent t (γ.val k)) r).equivFun (vertex q j)‖ ≤ D) ∧
        ∀ q j, F.ExpN (F.N.equiv (vertex q j.succ)) =
          F.ExpN (F.N.equiv (vertex q j.castSucc)) *
            F.ExpN (F.N.equiv (coeff q j • M.letter (mode j))) := by
  classical
  obtain ⟨N, C, hC, hcode⟩ := M.exists_measurable_bounded_template_coding (A := A) T F
    hExp realize haarN dynkinN b₀ v R hR
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  obtain ⟨D, hD, hbound⟩ := exists_uniform_dominated_word_prefix_bound dynkinN
    F.N.equiv F.ExpN F.isExpN M.letter M.bound_zero M.letter_mem_wordList b₀ N hC0
  obtain ⟨⟨chart, hchart⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  let e : (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ≃ₜ F.N.carrier :=
    (b₀.map F.N.equiv.toLinearEquiv).equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans chart
  have he (z) : e z = F.ExpN (F.N.equiv (b₀.equivFun.symm z)) := by
    change chart _ = _
    rw [hchart]
    rfl
  let : SecondCountableTopology F.N.carrier := e.symm.secondCountableTopology
  let : IsTopologicalGroup F.N.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  let E := F.ExpN ∘ F.N.equiv
  have hzero : E 0 = 1 := by simp [E, F.isExpN.map_zero]
  have hinj : Function.Injective E := (funext hchart ▸ chart.injective).comp F.N.equiv.injective
  refine ⟨N, C, D, hC, hD, ?_⟩
  intro r hr β γ hβ t hst hγ b y hy
  obtain ⟨word, hlen, hmeas, hamp, hend⟩ := hcode r hr β hβ y hy
  let X := fun i => Real.exp (r * M.templateSupportExponent v i) • M.letter i
  have hflow (i) : Measurable (fun s : ℝ => E (s • X i)) := by
    have hc : Continuous (fun s : ℝ => e (s • b₀.equivFun (X i))) := e.continuous.comp
      (continuous_id.smul (continuous_const : Continuous (fun _ : ℝ => b₀.equivFun (X i))))
    have heq : (fun s : ℝ => e (s • b₀.equivFun (X i))) = (fun s => E (s • X i)) := by
      funext s
      rw [he, map_smul, LinearEquiv.symm_apply_apply]
      rfl
    rw [heq] at hc
    exact hc.measurable
  obtain ⟨mode, c, g, hc, hg, hampc, hg0, hgN, hstep, hprefix⟩ :=
    exists_measurable_generator_chain X E hzero hflow (Classical.choice inferInstance)
      word hmeas hlen hC0 hamp (fun _ => 1) measurable_const
  let vertex := fun q j => b₀.equivFun.symm (e.symm (g q j))
  have hEval (q j) : E (vertex q j) = g q j := by
    change F.ExpN (F.N.equiv (b₀.equivFun.symm (e.symm (g q j)))) = _
    rw [← he]
    exact e.apply_symm_apply _
  have hv0 (q) : vertex q 0 = 0 := by
    apply hinj
    rw [hEval, hg0, hzero]
  have hvN (q) : vertex q (Fin.last N) = b.equivFun.symm (y q).val := by
    apply hinj
    rw [hEval, hgN, one_mul]
    exact hend q
  refine ⟨mode, fun q j => c q j * Real.exp (r * M.templateSupportExponent v (mode j)),
    vertex, ?_, ?_, ?_, hv0, hvN, ?_, ?_⟩
  · intro j
    exact (hc j).mul_const _
  · intro j
    simpa only [vertex, LinearEquiv.apply_symm_apply, Function.comp_def] using
      e.symm.continuous.measurable.comp (hg j)
  · intro q j
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hampc q j) (Real.exp_pos _).le
  · intro q j
    have hb := hbound (M.templateSupportExponent v) t hst γ hγ r hr
      (word.map (fun z => (z.1, z.2 q)))
      (by simpa only [List.length_map] using hlen) (by
        intro z hz
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
        exact hamp q w hw) j.val
    obtain ⟨w, hw, hnorm⟩ := hb
    have heq : vertex q j = w := hinj (by
      rw [hEval, hprefix, one_mul]
      exact hw.symm)
    simpa only [heq] using hnorm
  · intro q j
    change E (vertex q j.succ) = E (vertex q j.castSucc) * _
    rw [hEval, hEval, hstep]
    congr 1
    simp only [E, X, smul_smul, Function.comp_apply]

end PolycyclicRecognition.CartanWordModel

end

end OAI
