import OAI.Analysis.KadisonKastler.ConcreteFiniteTrace
import OAI.Analysis.KadisonKastler.TraceSeparability
import OAI.Analysis.FactorGeneration.TraceHilbert

namespace OAI

/-! # The canonical separable trace Hilbert realization

The trace completion provides the Hilbert-space norm estimates used
by boundary comparison.
-/

namespace KadisonKastler

open TopologicalSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem traceHilbert_factor (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (x : Algebra M) (hx : ∀ y : Algebra M, y * x = x * y) :
    ∃ c : ℂ, x = c • (1 : Algebra M) := by
  obtain ⟨c, hc⟩ := hM.factor x hx
  exact ⟨c, by simpa only [Algebra.algebraMap_eq_smul_one] using hc⟩

theorem traceHilbert_nonzero (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    (1 : Algebra M) ≠ 0 := by
  intro h
  exact hM.nonzero (congrArg Subtype.val h).symm

/-- The completion of the algebra in its canonical trace inner product. -/
abbrev ConcreteTraceHilbert (hM : Generator.IsII1Factor M.toStarSubalgebra) :=
  Generator.Tracial.TraceFreeHilbert (traceHilbert_factor hM)
    hM.diffuse hM.finite (traceHilbert_nonzero hM)

/-- The algebraic inclusion into its actual trace Hilbert completion. -/
def concreteTraceEmbedding (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    Algebra M →ₗ[ℂ] ConcreteTraceHilbert hM :=
  (Generator.Tracial.traceFreeInclusion (traceHilbert_factor hM)
    hM.diffuse hM.finite (traceHilbert_nonzero hM)).toLinearMap.comp
      (Generator.Tracial.traceFreeCopy (traceHilbert_factor hM)
        hM.diffuse hM.finite (traceHilbert_nonzero hM)).toAlgEquiv.toLinearMap

theorem concreteTraceEmbedding_norm (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (x : Algebra M) :
    ‖concreteTraceEmbedding hM x‖ = traceTwoNorm (concreteFactorTrace hM) x := by
  have hs := Generator.Tracial.traceFreeCopy_norm_sq (traceHilbert_factor hM)
    hM.diffuse hM.finite (traceHilbert_nonzero hM) x
  have hn : ‖concreteTraceEmbedding hM x‖ ^ 2 =
      ((concreteFactorTrace hM).toLinearMap (star x * x)).re := by
    change ‖Generator.Tracial.traceFreeInclusion (traceHilbert_factor hM)
      hM.diffuse hM.finite (traceHilbert_nonzero hM)
      (Generator.Tracial.traceFreeCopy (traceHilbert_factor hM)
        hM.diffuse hM.finite (traceHilbert_nonzero hM) x)‖ ^ 2 = _
    rw [LinearIsometry.norm_map]
    exact hs
  have ht := traceTwoNorm_sq (concreteFactorTrace hM) x
  nlinarith [norm_nonneg (concreteTraceEmbedding hM x),
    traceTwoNorm_nonneg (concreteFactorTrace hM) x]

theorem concreteTraceEmbedding_denseRange (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    DenseRange (concreteTraceEmbedding hM) := by
  let e := Generator.Tracial.traceFreeCopy (traceHilbert_factor hM)
    hM.diffuse hM.finite (traceHilbert_nonzero hM)
  let i := Generator.Tracial.traceFreeInclusion (traceHilbert_factor hM)
    hM.diffuse hM.finite (traceHilbert_nonzero hM)
  have hi : DenseRange i := Generator.Tracial.traceFreeInclusion_denseRange
    (traceHilbert_factor hM) hM.diffuse hM.finite (traceHilbert_nonzero hM)
  have he : DenseRange e := e.surjective.denseRange
  change DenseRange (fun x => i (e x))
  exact hi.comp he i.continuous

/-- Trace separability of the algebra makes any dense faithful trace
Hilbert realization separable. -/
theorem separableSpace_of_traceHilbert {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {τ : FaithfulTracialState (Algebra M)}
    (J : Algebra M →ₗ[ℂ] E) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (hsep : TraceSeparable τ Set.univ) (hdense : DenseRange J) : SeparableSpace E := by
  obtain ⟨D, hDc, _, hD⟩ := hsep
  refine ⟨J '' D, hDc.image J, ?_⟩
  have hsub : Set.range J ⊆ closure (J '' D) := by
    rintro _ ⟨x, rfl⟩
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨y, hy, hxy⟩ := hD x (Set.mem_univ x) ε hε
    refine ⟨J y, ⟨y, hy, rfl⟩, ?_⟩
    rw [dist_eq_norm, ← map_sub, hJ]
    exact hxy
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_univ_subset
  rw [← hdense.closure_range]
  exact closure_minimal hsub isClosed_closure

/-- The trace Hilbert space of a separably acting II₁ factor is separable. -/
instance concreteTraceHilbert_separable [SeparableSpace H]
    (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    SeparableSpace (ConcreteTraceHilbert hM) :=
  separableSpace_of_traceHilbert (concreteTraceEmbedding hM) (concreteTraceEmbedding_norm hM)
    ((concreteFactorTrace_finiteVector hM).traceSeparable Set.univ)
    (concreteTraceEmbedding_denseRange hM)

end

end KadisonKastler

end OAI
