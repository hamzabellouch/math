import OAI.Probability.SLE.Mass.RadonTestLimitProperties
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.DenseEmbedding

namespace OAI

/-! Shrinking trace intervals have vanishing nonatomic mass. This gives
local oscillation control and continuous extension from rational times. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SLEExactGauge

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
/-- Continuity and null singleton mass control every sufficiently short
trace interval around any fixed time. It applies to a finite compact
restriction of the terminal measure. -/
theorem trace_interval_mass_small (ν : Measure X) [ν.OuterRegular]
    [NullSingletonClass ν] (γ : ℝ → X) (hγ : Continuous γ)
    (t : ℝ) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, dist a t < δ → dist b t < δ →
      ν (γ '' Icc a b) < ε := by
  obtain ⟨U,hUsub,hU,hνU⟩ := ({γ t} : Set X).exists_isOpen_lt_of_lt (μ := ν) ε (by simpa using hε)
  have htU : γ t ∈ U := hUsub (mem_singleton _)
  have hpre : γ ⁻¹' U ∈ 𝓝 t := hγ.continuousAt.preimage_mem_nhds (hU.mem_nhds htU)
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨δ,hδ,fun a b ha hb => (measure_mono ?_).trans_lt hνU⟩
  rintro _ ⟨x,hx,rfl⟩
  apply hδsub
  rw [Metric.mem_ball,Real.dist_eq]
  rw [Real.dist_eq,abs_lt] at ha hb
  exact abs_lt.mpr ⟨lt_of_lt_of_le ha.1 (sub_le_sub_right hx.1 t),
    lt_of_le_of_lt (sub_le_sub_right hx.2 t) hb.2⟩

/-- A rational-time real observable with arbitrarily small local
oscillation has a unique continuous extension to all real times. -/
theorem exists_continuous_rational_extension
    (f : ℚ → ℝ)
    (hosc : ∀ t : ℝ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ p q : ℚ, dist (p:ℝ) t < δ → dist (q:ℝ) t < δ → dist (f p) (f q) < ε) :
    ∃ F : ℝ → ℝ, Continuous F ∧ (∀ q : ℚ, F q=f q) ∧
      ∀ G : ℝ → ℝ, Continuous G → (∀ q : ℚ, G q=f q) → G=F := by
  let D := Rat.isDenseEmbedding_coe_real.isDenseInducing
  have hlim (t : ℝ) : ∃ c : ℝ, Tendsto f (comap ((↑) : ℚ → ℝ) (𝓝 t)) (𝓝 c) := by
    let : NeBot (comap ((↑) : ℚ → ℝ) (𝓝 t))  := D.comap_nhds_neBot t
    apply cauchy_map_iff_exists_tendsto.mp
    apply Metric.cauchy_iff.mpr
    refine ⟨inferInstance,fun ε hε => ?_⟩
    obtain ⟨δ,hδ,hcontrol⟩ := hosc t ε hε
    let A : Set ℚ := ((↑) : ℚ → ℝ) ⁻¹' Metric.ball t δ
    have hA : A ∈ comap ((↑) : ℚ → ℝ) (𝓝 t) :=
      preimage_mem_comap (Metric.ball_mem_nhds t hδ)
    refine ⟨f '' A,image_mem_map hA,?_⟩
    rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩
    exact hcontrol p q hp hq
  refine ⟨D.extend f,D.continuous_extend hlim,D.extend_eq' hlim,?_⟩
  intro G hG heq
  exact (D.extend_unique heq hG).symm

omit [BorelSpace X] in
/-- The trace-support estimate for increments supplies the local
oscillation hypothesis of the rational extension theorem. -/
theorem continuous_rational_extension_of_trace_control
    (ν : Measure X) [ν.OuterRegular] [IsFiniteMeasure ν] [NullSingletonClass ν]
    (γ : ℝ → X) (hγ : Continuous γ) (f : ℚ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hcontrol : ∀ p q : ℚ, dist (f p) (f q) ≤
      C*(ν (γ '' Icc (min (p:ℝ) q) (max (p:ℝ) q))).toReal) :
    ∃ F : ℝ → ℝ, Continuous F ∧ (∀ q : ℚ, F q=f q) ∧
      ∀ G : ℝ → ℝ, Continuous G → (∀ q : ℚ, G q=f q) → G=F := by
  apply exists_continuous_rational_extension f
  intro t ε hε
  have he : 0 < ε/(C+1) := div_pos hε (by linarith)
  obtain ⟨δ,hδ,hsmall⟩ := trace_interval_mass_small ν γ hγ t
    (ENNReal.ofReal (ε/(C+1))) (ENNReal.ofReal_pos.mpr he)
  refine ⟨δ,hδ,fun p q hp hq => ?_⟩
  have hm : dist (min (p:ℝ) q) t < δ := by
    rcases le_total (p:ℝ) q with h | h
    · simpa only [min_eq_left h] using hp
    · simpa only [min_eq_right h] using hq
  have hM : dist (max (p:ℝ) q) t < δ := by
    rcases le_total (p:ℝ) q with h | h
    · simpa only [max_eq_right h] using hq
    · simpa only [max_eq_left h] using hp
  have hv : (ν (γ '' Icc (min (p:ℝ) q) (max (p:ℝ) q))).toReal < ε/(C+1) := by
    have hh := (ENNReal.toReal_lt_toReal (measure_ne_top ν _) ENNReal.ofReal_ne_top).mpr (hsmall _ _ hm hM)
    simpa only [ENNReal.toReal_ofReal he.le] using hh
  have hbound := hcontrol p q
  have hratio : C*(ε/(C+1)) < ε := by
    rw [← mul_div_assoc,div_lt_iff₀ (by linarith : 0<C+1)]
    nlinarith
  exact hbound.trans_lt ((mul_le_mul_of_nonneg_left hv.le hC).trans_lt hratio)

end SLEExactGauge

end

end OAI
