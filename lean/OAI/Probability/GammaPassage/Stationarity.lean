import OAI.Probability.GammaPassage.Environment
import OAI.Probability.GammaPassage.PathIntegrability
import OAI.Probability.FirstPassage.Translation

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {ν : Measure ℝ}

/-- Deterministic lattice translation preserves an iid environment. -/
theorem IidEnvironment.translate (h : IidEnvironment ν P τ) (a : Vertex) :
    IidEnvironment ν P (fun e => τ (shiftEdge a e)) where
  probability := h.probability
  measurable := fun e => h.measurable (shiftEdge a e)
  independent := h.independent.precomp (shiftEdge_injective a)
  marginal := fun e => h.marginal (shiftEdge a e)

/-- The complete configuration has the product law. -/
theorem IidEnvironment.jointLaw (h : IidEnvironment ν P τ) :
    Measure.map (fun ω e => τ e ω) P = iidProductLaw ν := by
  rw [h.independent.map_fun_eq_infinitePi_map h.measurable]
  simp only [h.marginal, iidProductLaw]

/-- Every measurable configuration observable has translation-invariant law. -/
theorem IidEnvironment.translated_event_probability
    (h : IidEnvironment ν P τ) (a : Vertex)
    (A : Set (Edge → ℝ)) (hA : MeasurableSet A) :
    P {ω | (fun e => τ (shiftEdge a e) ω) ∈ A} =
      P {ω | (fun e => τ e ω) ∈ A} := by
  have he := congrArg (fun Q : Measure (Edge → ℝ) => Q A)
    ((h.translate a).jointLaw.trans h.jointLaw.symm)
  rw [Measure.map_apply (Measurable.of_eval (fun e => h.measurable _)) hA,
    Measure.map_apply (Measurable.of_eval h.measurable) hA] at he
  exact he

/-- Integral transport to the common product law. -/
theorem IidEnvironment.integral_configuration (h : IidEnvironment ν P τ)
    (f : (Edge → ℝ) → ℝ) (hf : Measurable f) :
    (∫ ω, f (fun e => τ e ω) ∂P) = ∫ w, f w ∂iidProductLaw ν := by
  rw [← h.jointLaw]
  exact (integral_map (Measurable.of_eval h.measurable).aemeasurable
    hf.aestronglyMeasurable).symm

/-- Translated passage times have equal expectations. -/
theorem IidEnvironment.integral_passageTime_translate
    (h : IidEnvironment ν P τ) (a p q : Vertex) :
    (∫ ω, passageTime (fun e => τ e ω) (a + p) (a + q) ∂P) =
      ∫ ω, passageTime (fun e => τ e ω) p q ∂P := by
  have hm : Measurable (fun w : Edge → ℝ => passageTime w p q) :=
    PlanarFPP.measurable_passageTime (fun e => measurable_pi_apply e) p q
  have ht := (h.translate a).integral_configuration
    (fun w : Edge → ℝ => passageTime w p q) hm
  have ho := h.integral_configuration (fun w : Edge → ℝ => passageTime w p q) hm
  have he : (∫ ω, passageTime (fun e => τ e ω) (a + p) (a + q) ∂P) =
      ∫ ω, passageTime (fun e => τ (shiftEdge a e) ω) p q ∂P :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      (passageTime_translate (fun e => τ e ω) a p q).symm)
  exact he.trans (ht.trans ho.symm)

variable {shape rate : ℝ}

/-- The expected passage time is nonnegative. -/
theorem GammaEnvironment.integral_passageTime_nonneg
    (h : GammaEnvironment shape rate P τ) (p q : Vertex) :
    0 ≤ ∫ ω, passageTime (fun e => τ e ω) p q ∂P := by
  apply integral_nonneg_of_ae
  filter_upwards [h.ae_positive] with ω hω
  exact passageTime_nonneg _ (fun e => (hω e).le) p q

/-- A deterministic path bounds the expected passage time, counting every traversal. -/
theorem GammaEnvironment.integral_passageTime_le_path_length
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (ds : List Step) (hend : p + displacement ds = q) :
    (∫ ω, passageTime (fun e => τ e ω) p q ∂P) ≤
      (ds.length : ℝ) * (shape / rate) := by
  have hb := integral_mono_ae (h.integrable_passageTime hs hr p q)
    (h.integrable_pathCost hs hr p ds) (by
      filter_upwards [h.ae_positive] with ω hω
      exact passageTime_le_cost _ (fun e => (hω e).le) p q ds hend)
  rw [h.integral_pathCost hs hr p ds] at hb
  exact hb

/-- There is a finite upper bound for the expected passage time. -/
theorem GammaEnvironment.finite_expected_passage
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) :
    Integrable (fun ω => passageTime (fun e => τ e ω) p q) P ∧
      ∃ L : ℕ, 0 ≤ (∫ ω, passageTime (fun e => τ e ω) p q ∂P) ∧
        (∫ ω, passageTime (fun e => τ e ω) p q ∂P) ≤ (L : ℝ) * (shape / rate) := by
  obtain ⟨ds, hend⟩ := exists_path p q
  exact ⟨h.integrable_passageTime hs hr p q, ds.length,
    h.integral_passageTime_nonneg p q,
    h.integral_passageTime_le_path_length hs hr p q ds hend⟩

/-- Stationarity and the passage-time triangle inequality give subadditivity in expectation. -/
theorem GammaEnvironment.mean_passageTime_subadditive
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (x y : Vertex) :
    (∫ ω, passageTime (fun e => τ e ω) 0 (x + y) ∂P) ≤
      (∫ ω, passageTime (fun e => τ e ω) 0 x ∂P) +
      (∫ ω, passageTime (fun e => τ e ω) 0 y ∂P) := by
  have hb := integral_mono_ae (h.integrable_passageTime hs hr 0 (x + y))
    ((h.integrable_passageTime hs hr 0 x).add
      (h.integrable_passageTime hs hr x (x + y))) (by
        filter_upwards [h.ae_positive] with ω hω
        exact passageTime_triangle _ (fun e => (hω e).le) 0 x (x + y))
  simp only [Pi.add_apply] at hb
  rw [integral_add (h.integrable_passageTime hs hr 0 x)
    (h.integrable_passageTime hs hr x (x + y))] at hb
  have ht := h.integral_passageTime_translate x 0 y
  simp only [add_zero] at ht
  rw [ht] at hb
  exact hb

/-- Mean passage time along an integer lattice direction, indexed by natural steps. -/
noncomputable def meanPassageSequence (P : Measure Ω) (τ : Edge → Ω → ℝ)
    (z : Vertex) (n : ℕ) : ℝ :=
  ∫ ω, passageTime (fun e => τ e ω) 0 (n • z) ∂P

theorem GammaEnvironment.meanPassageSequence_nonneg
    (h : GammaEnvironment shape rate P τ) (z : Vertex) (n : ℕ) :
    0 ≤ meanPassageSequence P τ z n :=
  h.integral_passageTime_nonneg 0 (n • z)

/-- Subadditivity includes the zero direction and zero indices. -/
theorem GammaEnvironment.meanPassageSequence_subadditive
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) (m n : ℕ) :
    meanPassageSequence P τ z (m + n) ≤
      meanPassageSequence P τ z m + meanPassageSequence P τ z n := by
  unfold meanPassageSequence
  rw [add_nsmul]
  exact h.mean_passageTime_subadditive hs hr (m • z) (n • z)

end GammaFPP

end OAI
