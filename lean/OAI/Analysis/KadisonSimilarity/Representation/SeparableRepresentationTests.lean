import OAI.Analysis.KadisonSimilarity.Representation.SeparableContractionTests
import OAI.Analysis.KadisonSimilarity.Representation.KaplanskyDischarge

namespace OAI

/-! # Common contraction tests for representations

A norm-dense sequence in the unit ball of a separable C-star algebra works in
every representation. The proved finite-vector Kaplansky theorem extends its
weak-operator closure to the unit ball of the represented bicommutant. This
does not require normality of a representation or of a pointwise fiber map.
-/

noncomputable section

namespace KadisonSimilarity

open ContinuousLinearMapWOT Filter
open scoped Topology CStarAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Finite-vector strong approximation implies membership in the weak
operator closure. -/
theorem mem_weak_closure_of_finite_strong_approximation
    (S : Set (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (happrox : ∀ (s : Finset H) (ε : ℝ), 0 < ε →
      ∃ R ∈ S, ∀ x ∈ s, ‖R x - T x‖ < ε) :
    ofCLM T ∈ closure (ofCLM '' S) := by
  classical
  have hex (j : Finset H × ℕ) :
      ∃ R ∈ S, ∀ x ∈ j.1, ‖R x - T x‖ < 1 / (j.2 + 1 : ℝ) :=
    happrox j.1 _ (by positivity)
  choose R hR hclose using hex
  have hstrong (x : H) : Tendsto (fun j => R j x) atTop (𝓝 (T x)) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨({x}, N), ?_⟩
    intro j hj
    have hx : x ∈ j.1 := hj.1 (by simp)
    rw [dist_eq_norm]
    apply (hclose j x hx).trans_le
    exact (one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hj.2 1)).trans hN.le
  have hweak : Tendsto (fun j => ofCLM (R j)) atTop (𝓝 (ofCLM T)) := by
    apply ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr
    intro x y
    exact tendsto_const_nhds.inner (hstrong x)
  exact mem_closure_of_tendsto hweak (Eventually.of_forall fun j => ⟨R j, hR j, rfl⟩)

variable {A : Type*} [CStarAlgebra A] [TopologicalSpace.SeparableSpace A]

/-- Choose one sequence in the source unit ball, dense for its norm topology. -/
theorem exists_norm_dense_contraction_tests :
    ∃ test : ℕ → A, (∀ n, ‖test n‖ ≤ 1) ∧
      ∀ a : A, ‖a‖ ≤ 1 → a ∈ closure (Set.range test) := by
  let B := {a : A // ‖a‖ ≤ 1}
  let : Nonempty B := ⟨⟨0, by simp⟩⟩
  let : SecondCountableTopology B :=
    (show Topology.IsEmbedding (Subtype.val : B → A) from
      Topology.IsEmbedding.subtypeVal).secondCountableTopology
  let : TopologicalSpace.SeparableSpace B := inferInstance
  let d : ℕ → B := TopologicalSpace.denseSeq B
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq B
  refine ⟨fun n => (d n).val, fun n => (d n).property, ?_⟩
  intro a ha
  exact map_mem_closure (f := (Subtype.val : B → A)) continuous_subtype_val
    (hd ⟨a, ha⟩) (by rintro _ ⟨n, rfl⟩; exact ⟨n, rfl⟩)

omit [TopologicalSpace.SeparableSpace A] in
/-- The image of a norm-dense source unit-ball sequence is weakly dense in
every represented bicommutant's unit ball. -/
theorem represented_contraction_mem_test_closure
    (test : ℕ → A)
    (hdense : ∀ a : A, ‖a‖ ≤ 1 → a ∈ closure (Set.range test))
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ representationVonNeumannAlgebra σ) (hn : ‖T‖ ≤ 1) :
    ofCLM T ∈ closure (Set.range fun n => ofCLM (σ (test n))) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hsource := mem_weak_closure_of_finite_strong_approximation
    {R | ∃ a : A, ‖a‖ ≤ 1 ∧ σ a = R} T (by
      intro s ε hε
      obtain ⟨a, ha, happrox⟩ := kaplansky_contraction_approximation σ T hT hn s ε hε
      exact ⟨σ a, ⟨a, ha, rfl⟩, happrox⟩)
  apply closure_minimal _ isClosed_closure hsource
  rintro _ ⟨R, ⟨a, ha, rfl⟩, rfl⟩
  exact map_mem_closure (f := fun a => ofCLM (σ a))
    (continuous_ofCLM.comp (map_continuous σ)) (hdense a ha)
    (by rintro _ ⟨n, rfl⟩; exact ⟨n, rfl⟩)

/-- One source sequence works simultaneously for all representations on a
fixed Hilbert space. Its construction is independent of that space. -/
theorem exists_common_representation_contraction_tests :
    ∃ test : ℕ → A, (∀ n, ‖test n‖ ≤ 1) ∧
      ∀ (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H),
        T ∈ representationVonNeumannAlgebra σ → ‖T‖ ≤ 1 →
        ofCLM T ∈ closure (Set.range fun n => ofCLM (σ (test n))) := by
  obtain ⟨test, hnorm, hdense⟩ := exists_norm_dense_contraction_tests (A := A)
  exact ⟨test, hnorm, fun σ T hT hn =>
    represented_contraction_mem_test_closure test hdense σ T hT hn⟩

/-- In particular the same source tests work on every Hilbert space of a
family, as required for a field of representations. -/
theorem exists_common_fiber_contraction_tests
    {Ω : Type*} (K : Ω → Type*) [∀ a, NormedAddCommGroup (K a)]
    [∀ a, InnerProductSpace ℂ (K a)] [∀ a, CompleteSpace (K a)]
    (σ : ∀ a, A →⋆ₐ[ℂ] (K a →L[ℂ] K a)) :
    ∃ test : ℕ → A, (∀ n, ‖test n‖ ≤ 1) ∧
      ∀ a (T : K a →L[ℂ] K a), T ∈ representationVonNeumannAlgebra (σ a) → ‖T‖ ≤ 1 →
        ofCLM T ∈ closure (Set.range fun n => ofCLM (σ a (test n))) := by
  obtain ⟨test, hnorm, hdense⟩ := exists_norm_dense_contraction_tests (A := A)
  exact ⟨test, hnorm, fun a T hT hn =>
    represented_contraction_mem_test_closure test hdense (σ a) T hT hn⟩

/-- Countably many almost-everywhere tests in the common source algebra
control the full scalar commutator seminorm almost everywhere. -/
theorem exists_common_fiber_scalar_tests
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (K : Ω → Type*) [∀ a, NormedAddCommGroup (K a)]
    [∀ a, InnerProductSpace ℂ (K a)] [∀ a, CompleteSpace (K a)]
    (σ : ∀ a, A →⋆ₐ[ℂ] (K a →L[ℂ] K a)) :
    ∃ test : ℕ → A, (∀ n, ‖test n‖ ≤ 1) ∧
      ∀ (Y : ∀ a, K a →L[ℂ] K a) (c : ℝ), 0 ≤ c →
        (∀ n, ∀ᵐ a ∂μ, ‖commutator (Y a) (σ a (test n))‖ ≤ c) →
        ∀ᵐ a ∂μ, scalarCommutatorNorm (representationVonNeumannAlgebra (σ a)) (Y a) ≤ c := by
  obtain ⟨test, hnorm, hdense⟩ := exists_common_fiber_contraction_tests K σ
  refine ⟨test, hnorm, ?_⟩
  intro Y c hc hbound
  exact ae_scalarCommutatorNorm_le_of_countable_tests μ K
    (fun a => representationVonNeumannAlgebra (σ a)) Y (fun a n => σ a (test n))
    (Eventually.of_forall hdense) hc hbound

end KadisonSimilarity

end

end OAI
