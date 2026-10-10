import OAI.Probability.FreeIsing.Estimates.FiniteIsingZeroField
import OAI.Probability.FreeIsing.Posterior.ProgressiveIsingPosterior

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

namespace Problem367

@[simp] theorem spinSign_flip (s : IsingSpin) : spinSign s.flip = -spinSign s := by
  cases s <;> norm_num [spinSign, IsingSpin.flip]

namespace FinitePosterior

theorem fieldMean_reindex {S V : Type*} [Fintype S] [Fintype V]
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (x : V → ℝ) (e : S ≃ S) :
    fieldMean (energy ∘ e) (spin ∘ e) (observable ∘ e) x =
      fieldMean energy spin observable x := by
  unfold fieldMean fieldEnergy
  simp only [Function.comp_apply]
  rw [e.sum_comp (fun s => observable s * Real.exp (energy s + ∑ v, x v * spin s v)),
    e.sum_comp (fun s => Real.exp (energy s + ∑ v, x v * spin s v))]

theorem fieldMean_neg_of_equiv {S V : Type*} [Fintype S] [Fintype V]
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (e : S ≃ S) (he : ∀ s, energy (e s) = energy s)
    (hs : ∀ s v, spin (e s) v = -spin s v)
    (ho : ∀ s, observable (e s) = -observable s) (x : V → ℝ) :
    fieldMean energy spin observable (fun v => -x v) =
      -fieldMean energy spin observable x := by
  rw [← fieldMean_reindex energy spin observable (fun v => -x v) e]
  simp only [fieldMean, fieldEnergy, Function.comp_apply, he, hs, ho,
    neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib, neg_div]

end FinitePosterior

theorem finiteIsingPosteriorMean_neg {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (v : D) (x : D → ℝ) :
    FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) w => spinSign (eta w))
      (fun eta => spinSign (eta v)) (fun w => -x w) =
    -FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) w => spinSign (eta w))
      (fun eta => spinSign (eta v)) x := by
  apply FinitePosterior.fieldMean_neg_of_equiv _ _ _
    (flipConfigMeasurableEquiv D).toEquiv
  · exact finiteIsingEnergy_flipConfig beta D
  · intro eta w
    exact spinSign_flip (eta w)
  · intro eta
    exact spinSign_flip (eta v)

theorem finiteIsingPosteriorMean_zero {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (v : D) :
    FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) w => spinSign (eta w))
      (fun eta => spinSign (eta v)) (fun _ => 0) = 0 := by
  have h := finiteIsingPosteriorMean_neg beta D v (fun _ => 0)
  simp only [neg_zero] at h
  linarith

@[simp] theorem finiteGibbsSpinMean_zero {d : ℕ} (beta : ℝ)
    (v : TreeVertex d) (n : ℕ) : finiteGibbsSpinMean beta v n (fun _ => 0) = 0 := by
  exact finiteIsingPosteriorMean_zero beta (connectedExhaustion v n)
    ⟨v, mem_connectedExhaustion v n⟩

theorem finiteGibbsSpinMean_neg {d : ℕ} (beta : ℝ)
    (v : TreeVertex d) (n : ℕ) (x : TreeVertex d → ℝ) :
    finiteGibbsSpinMean beta v n (fun w => -x w) =
      -finiteGibbsSpinMean beta v n x := by
  exact finiteIsingPosteriorMean_neg beta (connectedExhaustion v n)
    ⟨v, mem_connectedExhaustion v n⟩ ((connectedExhaustion v n).restrict x)

@[simp] theorem infiniteGibbsSpinMean_zero {d : ℕ} (beta : ℝ)
    (v : TreeVertex d) : infiniteGibbsSpinMean beta v (fun _ => 0) = 0 := by
  have hlim : Tendsto (fun n => finiteGibbsSpinMean beta v n (fun _ => 0))
      atTop (𝓝 0) := by simp
  rw [infiniteGibbsSpinMean, hlim.limUnder_eq]
  norm_num

theorem infiniteGibbsSpinMean_neg_of_tendsto {d : ℕ} (beta : ℝ)
    (v : TreeVertex d) (x : TreeVertex d → ℝ) {z : ℝ}
    (hz : Tendsto (fun n => finiteGibbsSpinMean beta v n x) atTop (𝓝 z)) :
    infiniteGibbsSpinMean beta v (fun w => -x w) =
      -infiniteGibbsSpinMean beta v x := by
  have hn : Tendsto (fun n => finiteGibbsSpinMean beta v n (fun w => -x w))
      atTop (𝓝 (-z)) := by
    simpa only [finiteGibbsSpinMean_neg] using hz.neg
  rw [infiniteGibbsSpinMean, infiniteGibbsSpinMean, hn.limUnder_eq, hz.limUnder_eq]
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem brownian_ising_array_zero_ae {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i)) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν), ∀ i, B i 0 (p.2 i) = 0 := by
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  apply ae_all_iff.mpr
  intro i
  exact ((measurePreserving_eval_infinitePi ν i).comp
    (measurePreserving_snd (μ := μ) (ν := Measure.infinitePi ν))).quasiMeasurePreserving.ae
      (hB i).eval_zero_ae_eq_zero

theorem infiniteGibbsSpinMean_brownian_zero {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (beta : ℝ)
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i)) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν), ∀ v,
      infiniteGibbsSpinMean beta v
        (fun i => (0 : ℝ) * spinSign (p.1 i) + B i 0 (p.2 i)) = 0 := by
  filter_upwards [brownian_ising_array_zero_ae μ ν hB] with p hp
  intro v
  simpa only [zero_mul, zero_add, hp] using infiniteGibbsSpinMean_zero beta v

theorem HasFreeIsingLaw.brownian_past_posterior_zero
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (v : TreeVertex d) :
    (μ.prod (Measure.infinitePi ν))[fun p => spinSign (p.1 v) |
      MeasurableSpace.comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
          fun i (s : Set.Iic (0 : ℝ≥0)) =>
            (s.1 : ℝ) * spinSign (p.1 i) + B i s.1 (p.2 i)) inferInstance]
      =ᵐ[μ.prod (Measure.infinitePi ν)] (fun _ => 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  filter_upwards [hμ.infiniteGibbsSpinMean_eq_brownian_past ν hB hmB 0 v,
    infiniteGibbsSpinMean_brownian_zero beta μ ν hB] with p hpost hz
  exact hpost.symm.trans (hz v)

end Problem367

end

end OAI
