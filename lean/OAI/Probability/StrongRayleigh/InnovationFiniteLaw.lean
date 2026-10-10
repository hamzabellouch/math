import OAI.Probability.StrongRayleigh.InnovationCharacteristic
import OAI.Probability.StrongRayleigh.FiniteGaussianCharacteristic

namespace OAI

universe u_1 u_2

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace Problem336AdditiveD139.InnovationCharacteristic

variable {Ω : Type u_1} {F : Type u_2} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] [Fintype F]

theorem gaussian_increment_law_of_local_characteristic
    (H : ℝ → MeasurableSpace Ω) (hH : Monotone H) (hle : ∀ u, H u ≤ mΩ)
    (W : ℝ → Ω → F → ℝ)
    (hW : ∀ u, 0 ≤ u → ∀ i, StronglyMeasurable[H u] (fun ω => W u ω i))
    (hlocal : ∀ θ : F → ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u v : ℝ, 0 ≤ u → u ≤ v → v - u ≤ 1 → ∀ᵐ ω ∂μ,
        ‖μ[fun ω => phase (∑ i : F, (W v ω i - W u ω i) * θ i) | H u] ω -
          (Real.exp (-(v - u) * (∑ i : F, (θ i) ^ 2) / 2) : ℂ)‖ ≤
            C * (v - u) * Real.sqrt (v - u))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Measure.map (fun ω i => W t ω i - W s ω i) μ =
        Measure.pi (fun _ : F => gaussianReal 0 ⟨t - s, sub_nonneg.mpr hst⟩) ∧
      Indep (H s) (MeasurableSpace.comap (fun ω i => W t ω i - W s ω i)
        inferInstance) μ := by
  classical
  have ht : 0 ≤ t := hs.trans hst
  have hZ : Measurable (fun ω i => W t ω i - W s ω i) :=
    Measurable.of_eval (fun i =>
      (((hW t ht i).mono (hle t)).measurable.sub ((hW s hs i).mono (hle s)).measurable))
  apply CharacteristicLaw.gaussian_pi_law_and_independent_of_event_characteristic
    hZ (hle s) ⟨t - s, sub_nonneg.mpr hst⟩
  intro A hA θ
  obtain ⟨C, hC, herr⟩ := hlocal θ
  let V : ℝ → Ω → ℝ := fun u ω => ∑ i : F, W u ω i * θ i
  have hV (u : ℝ) (hu : 0 ≤ u) : StronglyMeasurable[H u] (V u) := by
    exact Finset.stronglyMeasurable_fun_sum _ (fun i _ => (hW u hu i).mul_const (θ i))
  have hdiff (u v : ℝ) (ω : Ω) :
      V v ω - V u ω = ∑ i : F, (W v ω i - W u ω i) * θ i := by
    simp only [V, sub_mul, Finset.sum_sub_distrib]
  have herr' : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v - u ≤ 1 → ∀ᵐ ω ∂μ,
      ‖μ[fun ω => phase (V v ω - V u ω) | H u] ω -
        (Real.exp (-(v - u) * (∑ i : F, (θ i) ^ 2) / 2) : ℂ)‖ ≤
          C * (v - u) * Real.sqrt (v - u) := by
    simpa only [hdiff] using herr
  have h := event_characteristic_eq H hH hle V hV C (∑ i : F, (θ i) ^ 2) hC
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) herr' hs hst A hA
  change (∫ ω in A, Complex.exp (((∑ i : F, (W t ω i - W s ω i) * θ i : ℝ) : ℂ) *
      Complex.I) ∂μ) = ((μ A).toReal : ℂ) *
        Complex.exp (((-(t - s) * ∑ i : F, (θ i) ^ 2) / 2 : ℝ) : ℂ)
  simpa only [hdiff, phase, Complex.ofReal_exp, mul_comm] using h

theorem gaussian_increment_law_of_local_characteristic_nnreal
    (H : ℝ≥0 → MeasurableSpace Ω) (hH : Monotone H) (hle : ∀ u, H u ≤ mΩ)
    (W : ℝ≥0 → Ω → F → ℝ)
    (hW : ∀ u i, StronglyMeasurable[H u] (fun ω => W u ω i))
    (hlocal : ∀ θ : F → ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u v : ℝ≥0, u ≤ v → (v : ℝ) - u ≤ 1 → ∀ᵐ ω ∂μ,
        ‖μ[fun ω => phase (∑ i : F, (W v ω i - W u ω i) * θ i) | H u] ω -
          (Real.exp (-((v : ℝ) - u) * (∑ i : F, (θ i) ^ 2) / 2) : ℂ)‖ ≤
            C * ((v : ℝ) - u) * Real.sqrt ((v : ℝ) - u))
    {s t : ℝ≥0} (hst : s ≤ t) :
    Measure.map (fun ω i => W t ω i - W s ω i) μ =
        Measure.pi (fun _ : F => gaussianReal 0 (t - s)) ∧
      Indep (H s) (MeasurableSpace.comap (fun ω i => W t ω i - W s ω i)
        inferInstance) μ := by
  have hlocal' : ∀ θ : F → ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u v : ℝ, 0 ≤ u → u ≤ v → v - u ≤ 1 → ∀ᵐ ω ∂μ,
        ‖μ[fun ω => phase (∑ i : F,
          (W v.toNNReal ω i - W u.toNNReal ω i) * θ i) | H u.toNNReal] ω -
          (Real.exp (-(v - u) * (∑ i : F, (θ i) ^ 2) / 2) : ℂ)‖ ≤
            C * (v - u) * Real.sqrt (v - u) := by
    intro θ
    obtain ⟨C, hC, hθ⟩ := hlocal θ
    refine ⟨C, hC, ?_⟩
    intro u v hu huv hvu
    have hv : 0 ≤ v := hu.trans huv
    have h := hθ u.toNNReal v.toNNReal (Real.toNNReal_monotone huv)
      (by simpa only [Real.coe_toNNReal _ hu, Real.coe_toNNReal _ hv] using hvu)
    simpa only [Real.coe_toNNReal _ hu, Real.coe_toNNReal _ hv] using h
  have h := gaussian_increment_law_of_local_characteristic
    (fun u => H u.toNNReal) (hH.comp Real.toNNReal_monotone)
    (fun u => hle u.toNNReal) (fun u => W u.toNNReal)
    (fun u _ => hW u.toNNReal) hlocal' (s := (s : ℝ)) (t := (t : ℝ))
    s.property (show (s : ℝ) ≤ t from hst)
  have hv : (⟨(t : ℝ) - s, sub_nonneg.mpr (show (s : ℝ) ≤ t from hst)⟩ : ℝ≥0) =
      t - s := by
    apply Subtype.ext
    exact (NNReal.coe_sub hst).symm
  have hscoe : ((s : ℝ).toNNReal) = s := Real.toNNReal_coe
  have htcoe : ((t : ℝ).toNNReal) = t := Real.toNNReal_coe
  rw [hscoe, htcoe] at h
  change (Measure.map (fun ω i => W t ω i - W s ω i) μ =
      Measure.pi (fun _ : F => gaussianReal 0
        ⟨(t : ℝ) - s, sub_nonneg.mpr (show (s : ℝ) ≤ t from hst)⟩)) ∧ _ at h
  rwa [hv] at h

end Problem336AdditiveD139.InnovationCharacteristic

end

end OAI
