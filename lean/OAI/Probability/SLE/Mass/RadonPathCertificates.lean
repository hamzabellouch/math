import OAI.Probability.SLE.Mass.RadonTestDetermines
import OAI.Probability.SLE.Mass.RadonTestLimitProperties
import OAI.Probability.SLE.Mass.RationalTraceMassProgressiveVersion

namespace OAI

/-! Countable compact-test certificates for order and continuous Radon paths.
The cutoff coordinates in the determining family supply local mass bounds. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology CompactlySupported NNReal

namespace SLEExactGauge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

private lemma positive_part_error {a b e : ℝ} (ha : 0 ≤ a) (h : |a-b| ≤ e) :
    |a-max b 0| ≤ e := by
  rcases le_total 0 b with hb | hb
  · simpa only [max_eq_left hb] using h
  · rw [max_eq_right hb,sub_zero,abs_of_nonneg ha]
    rw [abs_of_nonneg (sub_nonneg.mpr (hb.trans ha))] at h
    linarith

theorem LocalTestFamily.measure_le_of_positive_tests (D : LocalTestFamily X)
    (μ ν : Measure X) [μ.Regular] [ν.Regular]
    (h : ∀ j, (∫ x, (D.test j ⊔ 0) x ∂μ) ≤ ∫ x, (D.test j ⊔ 0) x ∂ν) : μ ≤ ν := by
  apply radon_measure_le_of_nonneg_tests
  intro f hf
  obtain ⟨k,_,happrox⟩ := D.weighted_approximation f
  let A := ∫ x, f x ∂μ
  let B := ∫ x, f x ∂ν
  let M := (∫ x, D.test k x ∂μ)+(∫ x, D.test k x ∂ν)
  have hb (n : ℕ) : A ≤ B+(1/(n+1:ℝ))*M := by
    obtain ⟨j,hj⟩ := happrox (1/(n+1:ℝ)) (by positivity)
    have hp (x : X) : |f x-(D.test j ⊔ 0) x| ≤ (1/(n+1:ℝ))*D.test k x :=
      positive_part_error (hf x) (hj x)
    have hμ := integral_sub_le_cutoff μ f (D.test j ⊔ 0) (D.test k) _ hp
    have hν := integral_sub_le_cutoff ν f (D.test j ⊔ 0) (D.test k) _ hp
    have hh := h j
    dsimp only [A,B,M]
    have hμ' := le_abs_self ((∫ x, f x ∂μ)-(∫ x, (D.test j ⊔ 0) x ∂μ))
    have hν' := neg_le_abs ((∫ x, f x ∂ν)-(∫ x, (D.test j ⊔ 0) x ∂ν))
    nlinarith
  have hl : Tendsto (fun n : ℕ => B+(1/(n+1:ℝ))*M) atTop (𝓝 B) := by
    simpa only [zero_mul,add_zero] using tendsto_const_nhds.add
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const M)
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hl hb

theorem LocalTestFamily.continuous_integrals_of_tests (D : LocalTestFamily X)
    {T : Type*} [TopologicalSpace T] [SequentialSpace T]
    (N : T → Measure X) (hr : ∀ t, (N t).Regular)
    (hc : ∀ j, Continuous (fun t => ∫ x, D.test j x ∂N t)) :
    ∀ f : C_c(X,ℝ), Continuous (fun t => ∫ x, f x ∂N t) := by
  intro f
  apply SeqContinuous.continuous
  intro t a hta
  let (n : ℕ) : IsFiniteMeasureOnCompacts (N (t n)) := by
    let := hr (t n)
    infer_instance
  obtain ⟨ν,hν,_,hl⟩ := D.exists_radon_limit (fun n => N (t n))
    (fun j => ⟨∫ x, D.test j x ∂N a,(hc j).continuousAt.tendsto.comp hta⟩)
  have he : ν=N a := by
    let := hν
    let := hr a
    apply D.measure_eq_of_test_integrals
    intro j
    exact tendsto_nhds_unique (hl (D.test j)) ((hc j).continuousAt.tendsto.comp hta)
  simpa only [he,Function.comp_def] using hl f

end SLEExactGauge

end

end OAI
