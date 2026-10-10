import OAI.Probability.FreeIsing.Posterior.PlantedSymmetry
import OAI.Probability.FreeIsing.Spins.Moments

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem cond_prod_first_event {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (μ : Measure Ω) (ν : Measure A) [SFinite μ] [IsProbabilityMeasure ν]
    (E : Set Ω) :
    (μ.prod ν)[|E ×ˢ Set.univ] = (μ[|E]).prod ν := by
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, Measure.prod_prod, measure_univ, mul_one,
    ← Measure.restrict_prod_eq_prod_univ, Measure.prod_smul_left]

theorem HasFreeIsingLaw.measurePreserving_noise_cond_spin
    {d : ℕ} {θ : ℝ} {A : Type*} [MeasurableSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw θ μ)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (r w : TreeVertex d) (s : IsingSpin) :
    MeasurePreserving (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) => p.2 w)
      (μ.prod (Measure.infinitePi ν))[|{p | p.1 r = s}] (ν w) := by
  let := hμ.isProbabilityMeasure
  have hmass : μ {σ | σ r = s} ≠ 0 := by rw [hμ.marginal]; norm_num
  let : IsProbabilityMeasure μ[|{σ | σ r = s}] := cond_isProbabilityMeasure hmass
  have hset : {p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) | p.1 r = s} =
      {σ : TreeVertex d → IsingSpin | σ r = s} ×ˢ Set.univ := by ext p; simp
  rw [hset, cond_prod_first_event]
  refine ⟨(measurable_pi_apply w).comp measurable_snd, ?_⟩
  change Measure.map ((fun z : TreeVertex d → A => z w) ∘ Prod.snd) _ = _
  rw [← Measure.map_map (measurable_pi_apply w) measurable_snd,
    Measure.map_snd_prod, measure_univ, one_smul, Measure.infinitePi_map_eval]

theorem HasFreeIsingLaw.gaussian_noise_hasLaw_cond_spin
    {d : ℕ} {θ : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw θ μ) (t : ℝ≥0) (r w : TreeVertex d) (s : IsingSpin) :
    HasLaw (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) => p.2 w)
      (gaussianReal 0 t)
      (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))[|{p | p.1 r = s}] := by
  exact (hμ.measurePreserving_noise_cond_spin (fun _ => gaussianReal 0 t) r w s).hasLaw

theorem HasFreeIsingLaw.standard_gaussian_hasLaw_cond_spin
    {d : ℕ} {θ : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw θ μ) (t : ℝ≥0) (ht : 0 < t)
    (r w : TreeVertex d) (s : IsingSpin) :
    HasLaw (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
      p.2 w / Real.sqrt t) (gaussianReal 0 1)
      (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))[|{p | p.1 r = s}] := by
  have h := gaussianReal_div_const (hμ.gaussian_noise_hasLaw_cond_spin t r w s) (Real.sqrt t)
  have hs : t / NNReal.mk ((Real.sqrt t) ^ 2) (sq_nonneg _) = 1 := by
    apply NNReal.eq
    change (t : ℝ) / (Real.sqrt (t : ℝ)) ^ 2 = 1
    rw [Real.sq_sqrt (show (0 : ℝ) ≤ t from t.2),
      div_self (ne_of_gt (show (0 : ℝ) < t from ht))]
  simpa only [zero_div, hs] using h

theorem HasFreeIsingLaw.own_gaussian_observation_cond_pos
    {d : ℕ} {θ : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (_hμ : HasFreeIsingLaw θ μ) (t : ℝ≥0) (ht : 0 < t) (r : TreeVertex d) :
    ∀ᵐ p ∂(μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))[|{p | p.1 r = .pos}],
      PlantedSymmetry.observation t p r =
        (t : ℝ) + Real.sqrt t * (p.2 r / Real.sqrt t) := by
  have hs : MeasurableSet {p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) |
      p.1 r = .pos} :=
    (show MeasurableSet ({IsingSpin.pos} : Set IsingSpin) from trivial).preimage
      ((measurable_pi_apply r).comp measurable_fst)
  filter_upwards [ae_cond_mem hs] with p hp
  have hroot : p.1 r = .pos := hp
  have hsqrt : Real.sqrt (t : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (show (0 : ℝ) < t from ht)).ne'
  simp only [PlantedSymmetry.observation, hroot, spinSign, mul_one]
  rw [mul_div_cancel₀ _ hsqrt]

end Problem367

end

end OAI
