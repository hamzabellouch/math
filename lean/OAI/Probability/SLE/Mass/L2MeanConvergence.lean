import OAI.Probability.SLE.Mass.L2ConvexTails

namespace OAI

/-! Passing expectations through the common L² convex extraction. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SLEExactGauge

lemma continuous_L2_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] :
    Continuous (fun x : Lp ℝ 2 P => ∫ ω, x ω ∂P) := by
  let h1 : MemLp (fun _ : Ω => (1 : ℝ)) 2 P := memLp_const 1
  let one : Lp ℝ 2 P := h1.toLp (fun _ => 1)
  have he (x : Lp ℝ 2 P) : inner ℝ one x = ∫ ω, x ω ∂P := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [h1.coeFn_toLp] with ω hω
    simp only [Real.inner_apply,one,hω,one_mul]
  simpa only [he] using (continuous_const.inner continuous_id :
    Continuous (fun x : Lp ℝ 2 P => inner ℝ one x))

lemma weighted_randomVariable_integral_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (f : ℕ → Ω → ℝ) (hf : ∀ n, MemLp (f n) 2 P)
    (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) (x : Lp ℝ 2 P)
    (h : Tendsto (fun n => ∑ i ∈ s n, w n i • (hf (n+i)).toLp (f (n+i))) atTop (𝓝 x)) :
    Tendsto (fun n => ∫ ω, ∑ i ∈ s n, w n i * f (n+i) ω ∂P)
      atTop (𝓝 (∫ ω, x ω ∂P)) := by
  have he (n : ℕ) : (∫ ω, ∑ i ∈ s n, w n i * f (n+i) ω ∂P) =
      ∫ ω, (∑ i ∈ s n, w n i • (hf (n+i)).toLp (f (n+i))) ω ∂P := by
    apply integral_congr_ae
    have hc := ae_coeFn_weighted_sum (s n) (w n) (fun i => (hf (n+i)).toLp (f (n+i)))
    have hr : ∀ᵐ ω ∂P, ∀ i, (hf (n+i)).toLp (f (n+i)) ω = f (n+i) ω :=
      ae_all_iff.mpr (fun i => (hf (n+i)).coeFn_toLp)
    filter_upwards [hc,hr] with ω hc hr
    simpa only [hr] using hc.symm
  simpa only [he,Function.comp_def] using (continuous_L2_integral P).continuousAt.tendsto.comp h

lemma continuous_L2_pairing
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (a : Ω → ℝ) (ha : MemLp a 2 P) :
    Continuous (fun x : Lp ℝ 2 P => ∫ ω, a ω * x ω ∂P) := by
  let y : Lp ℝ 2 P := ha.toLp a
  have he (x : Lp ℝ 2 P) : inner ℝ y x = ∫ ω, a ω * x ω ∂P := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp] with ω hω
    simp only [Real.inner_apply,y,hω]
  simpa only [he] using (continuous_const.inner continuous_id :
    Continuous (fun x : Lp ℝ 2 P => inner ℝ y x))

lemma weighted_randomVariable_pairing_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ) (hf : ∀ n, MemLp (f n) 2 P)
    (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) (x : Lp ℝ 2 P)
    (h : Tendsto (fun n => ∑ i ∈ s n, w n i • (hf (n+i)).toLp (f (n+i))) atTop (𝓝 x))
    (a : Ω → ℝ) (ha : MemLp a 2 P) :
    Tendsto (fun n => ∫ ω, a ω * (∑ i ∈ s n, w n i * f (n+i) ω) ∂P)
      atTop (𝓝 (∫ ω, a ω * x ω ∂P)) := by
  have he (n : ℕ) : (∫ ω, a ω * (∑ i ∈ s n, w n i * f (n+i) ω) ∂P) =
      ∫ ω, a ω * (∑ i ∈ s n, w n i • (hf (n+i)).toLp (f (n+i))) ω ∂P := by
    apply integral_congr_ae
    have hc := ae_coeFn_weighted_sum (s n) (w n) (fun i => (hf (n+i)).toLp (f (n+i)))
    have hr : ∀ᵐ ω ∂P, ∀ i, (hf (n+i)).toLp (f (n+i)) ω = f (n+i) ω :=
      ae_all_iff.mpr (fun i => (hf (n+i)).coeFn_toLp)
    filter_upwards [hc,hr] with ω hc hr
    apply congrArg (fun v : ℝ => a ω * v)
    simpa only [hr] using hc.symm
  simpa only [he,Function.comp_def] using (continuous_L2_pairing P a ha).continuousAt.tendsto.comp h

end SLEExactGauge

end

end OAI
