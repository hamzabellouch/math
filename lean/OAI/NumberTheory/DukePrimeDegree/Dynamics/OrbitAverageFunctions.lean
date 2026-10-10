import OAI.NumberTheory.DukePrimeDegree.Dynamics.L2ToL1Averages

namespace OAI

/-!
# Pointwise representatives of the orbit averages

The Hilbert-space Cesaro average agrees almost everywhere with the
literal finite sum along the orbit. A bounded density transfers that
agreement to a varying sampling law, so the dominated-average theorem
applies to actual orbit samples.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree

variable {X : Type*} [MeasurableSpace X]

lemma orbit_average_congr_ae (μ : Measure X) (T : X → X)
    (hT : MeasurePreserving T μ μ) {f g : X → ℝ}
    (hfg : f =ᵐ[μ] g) (N : ℕ) :
    birkhoffAverage ℝ T f N =ᵐ[μ] birkhoffAverage ℝ T g N := by
  have hsum := eventuallyEq_sum (s := Finset.range N)
    (fun k _ => (hT.iterate k).quasiMeasurePreserving.ae_eq_comp hfg)
  filter_upwards [hsum] with x hx
  simpa only [birkhoffAverage, birkhoffSum, Function.comp_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
    congrArg (fun z : ℝ => (N : ℝ)⁻¹ * z) hx

lemma Lp_orbit_average_ae (μ : Measure X) (T : X → X)
    (hT : MeasurePreserving T μ μ) (f : Lp ℝ 2 μ) (N : ℕ) :
    ((birkhoffAverage ℝ (Lp.compMeasurePreserving T hT) id N f : Lp ℝ 2 μ) : X → ℝ)
      =ᵐ[μ] birkhoffAverage ℝ T f N := by
  have hit (k : ℕ) :
      ((Lp.compMeasurePreserving T hT)^[k] f : X → ℝ)
        =ᵐ[μ] fun x => f (T^[k] x) := by
    rw [Lp.compMeasurePreserving_iterate]
    exact Lp.coeFn_compMeasurePreserving f (hT.iterate k)
  have hsum :
      ((∑ k ∈ Finset.range N, (Lp.compMeasurePreserving T hT)^[k] f : Lp ℝ 2 μ) : X → ℝ)
        =ᵐ[μ] fun x => ∑ k ∈ Finset.range N, f (T^[k] x) :=
    by
      have hh := eventuallyEq_sum (s := Finset.range N) (fun k _ => hit k)
      filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range N)
        (fun k => (Lp.compMeasurePreserving T hT)^[k] f), hh] with x hx hx'
      exact hx.trans (by simpa only [Finset.sum_apply] using hx')
  have hscale := Lp.coeFn_smul ((N : ℝ)⁻¹)
    (∑ k ∈ Finset.range N, (Lp.compMeasurePreserving T hT)^[k] f)
  filter_upwards [hscale, hsum] with x hx hs
  simpa only [birkhoffAverage, birkhoffSum, id_eq, Pi.smul_apply,
    smul_eq_mul, hs] using hx

lemma Lp_orbit_average_ae_of_domination
    (μ ν : Measure X) (T : X → X) (hT : MeasurePreserving T μ μ)
    (f : Lp ℝ 2 μ) (N : ℕ) (C : ℝ≥0∞) (hdom : ν ≤ C • μ) :
    ((birkhoffAverage ℝ (Lp.compMeasurePreserving T hT) id N f : Lp ℝ 2 μ) : X → ℝ)
      =ᵐ[ν] birkhoffAverage ℝ T f N :=
  ae_mono hdom (Measure.ae_smul_measure (Lp_orbit_average_ae μ T hT f N) C)

/-- A statement about the actual finite orbit sums, without any choice
of representative for their Hilbert-space average. -/
theorem actual_orbit_average_tendsto_integral
    (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : Ergodic T μ) (f : Lp ℝ 2 μ)
    (ν : ℕ → Measure X) [∀ n, IsProbabilityMeasure (ν n)]
    (C : ℝ) (hC : 0 ≤ C) (hdom : ∀ n, ν n ≤ ENNReal.ofReal C • μ) :
    Tendsto (fun N => ∫ x, birkhoffAverage ℝ T f N x ∂ν N)
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  have he (N : ℕ) :
      (∫ x, birkhoffAverage ℝ T f N x ∂ν N) =
        ∫ x, (birkhoffAverage ℝ (Lp.compMeasurePreserving T hT.toMeasurePreserving)
          id N f) x ∂ν N :=
    integral_congr_ae (Lp_orbit_average_ae_of_domination μ (ν N) T
      hT.toMeasurePreserving f N _ (hdom N)).symm
  simp_rw [he]
  exact dominated_orbit_average_tendsto_integral μ T hT f ν C hC hdom

/-- The window length may grow at any rate. Only divergence of the
length and a uniform bound for the sampling densities are needed. -/
theorem variable_orbit_average_tendsto_integral
    (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : Ergodic T μ) (f : X → ℝ) (hf : MemLp f 2 μ)
    (ν : ℕ → Measure X) [∀ n, IsProbabilityMeasure (ν n)]
    (C : ℝ) (hC : 0 ≤ C) (hdom : ∀ n, ν n ≤ ENNReal.ofReal C • μ)
    (length : ℕ → ℕ) (hlength : Tendsto length atTop atTop) :
    Tendsto (fun n => ∫ x, birkhoffAverage ℝ T f (length n) x ∂ν n)
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  let F (n : ℕ) : Lp ℝ 2 μ := birkhoffAverage ℝ
    (Lp.compMeasurePreserving T hT.toMeasurePreserving) id (length n) (hf.toLp f)
  have hF : Tendsto (fun n => ∫ x, |F n x - ∫ y, f y ∂μ| ∂μ) atTop (𝓝 0) := by
    have hmean := (L1_orbit_average_tendsto_integral μ T hT (hf.toLp f)).comp hlength
    have he : (∫ y, hf.toLp f y ∂μ) = ∫ y, f y ∂μ := integral_congr_ae hf.coeFn_toLp
    simpa only [he, F, Function.comp_def] using hmean
  have hav : Tendsto (fun n => ∫ x, F n x ∂ν n) atTop (𝓝 (∫ y, f y ∂μ)) := by
    apply integral_tendsto_of_dominated_sampling μ ν C _ hC hdom
    · intro n
      exact memLp_one_iff_integrable.mp ((Lp.memLp (F n)).mono_exponent (by norm_num))
    · exact hF
  have he (n : ℕ) :
      (∫ x, F n x ∂ν n) = ∫ x, birkhoffAverage ℝ T f (length n) x ∂ν n := by
    apply integral_congr_ae
    apply ae_mono (hdom n)
    apply Measure.ae_smul_measure
    exact (Lp_orbit_average_ae μ T hT.toMeasurePreserving (hf.toLp f) (length n)).trans
      (orbit_average_congr_ae μ T hT.toMeasurePreserving hf.coeFn_toLp (length n))
  simpa only [he] using hav

end DukePrimeDegree

end

end OAI
