import Mathlib.Probability.Moments.ComplexMGF

namespace OAI

/-! # Uniqueness from Laplace values on an interval about zero

This specialization is used for the finite positive measures formed from the
positive and negative parts of a modular averaging coefficient.
-/

namespace KadisonKastler

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

noncomputable section

theorem finiteMeasure_eq_of_local_laplace {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {a : ℝ} (ha : 0 < a)
    (hμ : ∀ t ∈ Ioo (-a) a, Integrable (fun x : ℝ => Real.exp (t * x)) μ)
    (hν : ∀ t ∈ Ioo (-a) a, Integrable (fun x : ℝ => Real.exp (t * x)) ν)
    (heq : ∀ t ∈ Ioo (-a) a, mgf id μ t = mgf id ν t) : μ = ν := by
  let S : Set ℂ := {z | z.re ∈ Ioo (-a) a}
  have hμ' : Ioo (-a) a ⊆ interior (integrableExpSet id μ) := by
    apply interior_maximal hμ isOpen_Ioo
  have hν' : Ioo (-a) a ⊆ interior (integrableExpSet id ν) := by
    apply interior_maximal hν isOpen_Ioo
  have hf : AnalyticOnNhd ℂ (complexMGF id μ) S :=
    analyticOnNhd_complexMGF.mono (fun z hz => hμ' hz)
  have hg : AnalyticOnNhd ℂ (complexMGF id ν) S :=
    analyticOnNhd_complexMGF.mono (fun z hz => hν' hz)
  have hS : IsPreconnected S := (convex_Ioo (-a) a).linear_preimage Complex.reLm |>.isPreconnected
  have h0 : (0 : ℂ) ∈ S := by change -a < 0 ∧ 0 < a; constructor <;> linarith
  have hreal : ∃ᶠ t : ℝ in 𝓝[≠] 0, complexMGF id μ t = complexMGF id ν t := by
    have hi : Ioo (-a) a ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) ha
    have he : ∀ᶠ t : ℝ in 𝓝[≠] 0, t ∈ Ioo (-a) a :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hi
    exact (he.mono fun t ht => by rw [complexMGF_ofReal, complexMGF_ofReal, heq t ht]).frequently
  have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] 0, complexMGF id μ z = complexMGF id ν z := by
    rw [frequently_iff_seq_forall] at hreal ⊢
    obtain ⟨xs, hx, he⟩ := hreal
    refine ⟨fun n => (xs n : ℂ), ?_, fun n => he n⟩
    rw [tendsto_nhdsWithin_iff] at hx ⊢
    constructor
    · simpa only [Function.comp_def, Complex.ofReal_zero] using
        (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hx.1
    · simpa using hx.2
  have he := hf.eqOn_of_preconnected_of_frequently_eq hg hS h0 hfreq
  apply Measure.ext_of_charFun
  ext t
  rw [← complexMGF_id_mul_I, ← complexMGF_id_mul_I]
  exact he (by simpa [S] using h0)

end

end KadisonKastler

end OAI
