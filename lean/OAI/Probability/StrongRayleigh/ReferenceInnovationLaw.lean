import OAI.Probability.StrongRayleigh.WeightedLocalInnovation
import OAI.Probability.StrongRayleigh.ObservationNoiseReal
import OAI.Probability.StrongRayleigh.LocalCharacteristicBrownian
import OAI.Probability.StrongRayleigh.InnovationContinuity

namespace OAI

universe u_1 u_2

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal BigOperators

namespace Problem336AdditiveD139.ReferenceInnovationLaw

variable {I : Type u_1} {Ω : Type u_2} [MeasurableSpace Ω]

def process (B : ℝ≥0 → Ω → ℝ)
    (b : I → ReferenceObservation.Space I Ω → ℝ≥0 → ℝ)
    (i : I) (t : ℝ≥0) (ω : ReferenceObservation.Space I Ω) : ℝ :=
  ReferenceObservation.observation B i t ω -
    ∫ s in (0 : ℝ)..(t : ℝ), b i ω s.toNNReal

def realDrift (b : I → ReferenceObservation.Space I Ω → ℝ≥0 → ℝ)
    (i : I) (ω : ReferenceObservation.Space I Ω) (t : ℝ) : ℝ :=
  b i ω t.toNNReal

lemma measurable_realDrift
    {b : I → ReferenceObservation.Space I Ω → ℝ≥0 → ℝ}
    (hbm : ∀ i, Measurable (Function.uncurry (b i))) (i : I) :
    Measurable (Function.uncurry (realDrift b i)) := by
  exact (hbm i).comp (measurable_fst.prodMk
    (continuous_real_toNNReal.measurable.comp measurable_snd))

omit [MeasurableSpace Ω] in
lemma process_eq_innovation
    (B : ℝ≥0 → Ω → ℝ)
    (b : I → ReferenceObservation.Space I Ω → ℝ≥0 → ℝ)
    (i : I) (t : ℝ≥0) (ω : ReferenceObservation.Space I Ω) :
    process B b i t ω = InnovationCorrection.innovation
      (boolReal (ω.1 i)) (fun s => ReferenceObservation.noise B i s.toNNReal ω)
      (realDrift b i ω) t := by
  simp [process, InnovationCorrection.innovation, ReferenceObservation.observation,
    realDrift]

theorem local_characteristic_error
    (μ : ProbabilityMeasure (I → Bool)) (ν : ProbabilityMeasure Ω)
    (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B (ν : Measure Ω))
    (hBm : ∀ t, Measurable (B t))
    (b : I → ReferenceObservation.Space I Ω → ℝ≥0 → ℝ)
    (hbm : ∀ i, Measurable (Function.uncurry (b i)))
    (hb : ∀ i ω t, b i ω t ∈ Set.Icc (0 : ℝ) 1)
    (hpost : ∀ t i, (fun ω => b i ω t) =ᵐ[ReferenceObservation.law μ ν]
      (ReferenceObservation.law μ ν)[(fun ω => boolReal (ω.1 i)) |
        ObservationNoise.historySigma B t])
    (S : Finset I) (θ : I → ℝ) (u v : ℝ≥0) (huv : u ≤ v)
    (hsmall : (v : ℝ) - (u : ℝ) ≤ 1) :
    ∀ᵐ ω ∂ ReferenceObservation.law μ ν,
      ‖(ReferenceObservation.law μ ν)[(fun a => Complex.exp
          (((∑ i ∈ S, θ i * (process B b i v a - process B b i u a) : ℝ) : ℂ) *
            Complex.I)) | ObservationNoise.historySigma B u] ω -
          (Real.exp (-(((v : ℝ) - (u : ℝ)) * ∑ i ∈ S, θ i ^ 2) / 2) : ℂ)‖ ≤
        WeightedLocalInnovation.errorConstant S θ * ((v : ℝ) - (u : ℝ)) *
          Real.sqrt ((v : ℝ) - (u : ℝ)) := by
  classical
  let P := ReferenceObservation.law μ ν
  let X : I → ReferenceObservation.Space I Ω → ℝ := fun i ω => boolReal (ω.1 i)
  let N : I → ReferenceObservation.Space I Ω → ℝ → ℝ :=
    fun i ω s => ReferenceObservation.noise B i s.toNNReal ω
  let h : ℝ≥0 := v - u
  have hh : (h : ℝ) = (v : ℝ) - (u : ℝ) := NNReal.coe_sub huv
  have huv' : (u : ℝ) + (h : ℝ) = (v : ℝ) := by rw [hh]; ring
  let Q := WeightedLocalInnovation.noiseIncrement S θ N u v
  have hQm : Measurable Q := by
    unfold Q WeightedLocalInnovation.noiseIncrement N
    exact S.measurable_sum (fun i _ => measurable_const.mul
      ((ReferenceObservation.measurable_noise B hBm i _).sub
        (ReferenceObservation.measurable_noise B hBm i _)))
  have hQlaw : HasLaw Q (gaussianReal 0 (h * WeightedLocalInnovation.variance S θ)) P := by
    have hq := ObservationNoise.real_increment_hasLaw μ ν hB hBm
      u.coe_nonneg (show (u : ℝ) ≤ (v : ℝ) from huv) S θ
    have hv : ObservationNoise.incrementVariance ((v : ℝ) - (u : ℝ)).toNNReal S θ =
        h * WeightedLocalInnovation.variance S θ := by
      apply NNReal.coe_injective
      rw [ObservationNoise.incrementVariance_real (show (u : ℝ) ≤ (v : ℝ) from huv)]
      change ((v : ℝ) - (u : ℝ)) * (∑ i ∈ S, θ i ^ 2) =
        (h : ℝ) * (∑ i ∈ S, θ i ^ 2)
      rw [hh]
    rw [hv] at hq
    exact hq
  have hQi : Indep (MeasurableSpace.comap Q inferInstance)
      (ObservationNoise.realFiltration (I := I) hBm (u : ℝ)) P := by
    rw [ObservationNoise.realFiltration_apply, Real.toNNReal_coe]
    change IndepFun Q (ObservationNoise.history B u) P
    have hi := ObservationNoise.real_increment_indep_history μ ν hB hBm
      u.coe_nonneg (show (u : ℝ) ≤ (v : ℝ) from huv) S θ
    change IndepFun Q (ObservationNoise.history B (u : ℝ).toNNReal) P at hi
    rw [Real.toNNReal_coe] at hi
    exact hi
  have hlocal := WeightedLocalInnovation.innovation_characteristic_error
    (μ := P) S θ (ObservationNoise.realFiltration (I := I) hBm) (u : ℝ) h
    (by simpa only [hh] using hsmall)
    (X := X) (B := N) (b := realDrift b)
    (fun i _ => (measurable_of_finite boolReal).comp
      ((measurable_pi_apply i).comp measurable_fst))
    (fun i _ ω => ReferenceObservation.signal_real_mem_unitInterval i ω)
    (fun i _ => measurable_realDrift hbm i)
    (fun i _ ω t => hb i ω t.toNNReal)
    hQm.comap_le (by simpa only [huv'] using (comap_measurable Q).stronglyMeasurable)
    (by simpa only [huv'] using hQlaw)
    hQi
    (fun t _ i _ => hpost t.toNNReal i)
  rw [huv'] at hlocal
  have hvar : (WeightedLocalInnovation.variance S θ : ℝ) = ∑ i ∈ S, θ i ^ 2 := rfl
  simpa only [WeightedLocalInnovation.innovationIncrement, X, N,
    ← process_eq_innovation, ObservationNoise.realFiltration_apply,
    Real.toNNReal_coe, hvar, hh, P, mul_comm Complex.I] using hlocal

theorem local_characteristic_subtype
    (μ : ProbabilityMeasure (I → Bool)) (ν : ProbabilityMeasure Ω)
    (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B (ν : Measure Ω))
    (hBm : ∀ t, Measurable (B t))
    (b : I → ReferenceObservation.Space I Ω → ℝ≥0 → ℝ)
    (hbm : ∀ i, Measurable (Function.uncurry (b i)))
    (hb : ∀ i ω t, b i ω t ∈ Set.Icc (0 : ℝ) 1)
    (hpost : ∀ t i, (fun ω => b i ω t) =ᵐ[ReferenceObservation.law μ ν]
      (ReferenceObservation.law μ ν)[(fun ω => boolReal (ω.1 i)) |
        ObservationNoise.historySigma B t])
    (S : Finset I) (θ : S → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : ℝ≥0, u ≤ v → (v : ℝ) - u ≤ 1 →
      ∀ᵐ ω ∂ ReferenceObservation.law μ ν,
        ‖(ReferenceObservation.law μ ν)[(fun a => Complex.exp (Complex.I *
            ((∑ i : S, θ i * (process B b i v a - process B b i u a) : ℝ) : ℂ))) |
              ObservationNoise.historySigma B u] ω -
            (Real.exp (-((v : ℝ) - u) * (∑ i : S, θ i ^ 2) / 2) : ℂ)‖ ≤
          C * ((v : ℝ) - u) * Real.sqrt ((v : ℝ) - u) := by
  classical
  let θ' : I → ℝ := fun i => if hi : i ∈ S then θ ⟨i, hi⟩ else 0
  have hs (f : I → ℝ) : (∑ i ∈ S, θ' i * f i) = ∑ i : S, θ i * f i := by
    rw [← Finset.sum_coe_sort]
    simp [θ']
  have hv : (∑ i ∈ S, θ' i ^ 2) = ∑ i : S, θ i ^ 2 := by
    rw [← Finset.sum_coe_sort]
    simp [θ']
  refine ⟨WeightedLocalInnovation.errorConstant S θ',
    WeightedLocalInnovation.errorConstant_nonneg S θ', ?_⟩
  intro u v huv hsmall
  have h := local_characteristic_error μ ν B hB hBm b hbm hb hpost S θ' u v huv hsmall
  simpa only [hs, hv, neg_mul, mul_comm Complex.I] using h

variable [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)]

theorem exists_iid_path_version [Countable I]
    (μ : ProbabilityMeasure (I → Bool)) (ν : ProbabilityMeasure Ω)
    (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B (ν : Measure Ω))
    (hBm : ∀ t, Measurable (B t))
    (ρ : Measure C(ℝ≥0, ℝ))
    (hρ : IsBrownianReal (fun t (w : C(ℝ≥0, ℝ)) => w t) ρ)
    (b : I → ReferenceObservation.Space I Ω → ℝ≥0 → ℝ)
    (hbm : ∀ i, Measurable (Function.uncurry (b i)))
    (hb : ∀ i ω t, b i ω t ∈ Set.Icc (0 : ℝ) 1)
    (hpost : ∀ t i, (fun ω => b i ω t) =ᵐ[ReferenceObservation.law μ ν]
      (ReferenceObservation.law μ ν)[(fun ω => boolReal (ω.1 i)) |
        ObservationNoise.historySigma B t])
    (hadapt : ∀ i, Adapted (ObservationNoise.filtration (I := I) hBm) (process B b i))
    (hcont : ∀ i, ∀ᵐ ω ∂ ReferenceObservation.law μ ν,
      Continuous (fun t => process B b i t ω)) :
    ∃ W : ReferenceObservation.Space I Ω → I → C(ℝ≥0, ℝ), Measurable W ∧
      Measure.map W (ReferenceObservation.law μ ν) = Measure.infinitePi (fun _ : I => ρ) ∧
      ∀ᵐ ω ∂ ReferenceObservation.law μ ν, ∀ i t, W ω i t = process B b i t ω := by
  refine exists_iid_path_version_of_local_characteristic ρ hρ
    (ObservationNoise.filtration (I := I) hBm) hadapt ?_ hcont ?_
  · intro i
    filter_upwards [(ReferenceObservation.noise_isPreBrownian μ ν B hB i).eval_zero_ae_eq_zero]
      with ω hω
    simpa only [process, ReferenceObservation.observation, NNReal.coe_zero,
      zero_mul, zero_add, intervalIntegral.integral_same, sub_zero] using hω
  · exact local_characteristic_subtype μ ν B hB hBm b hbm hb hpost

def fieldDrift (B : ℝ≥0 → Ω → ℝ) (b : ℝ → (I → ℝ) → I → ℝ)
    (i : I) (ω : ReferenceObservation.Space I Ω) (t : ℝ≥0) : ℝ :=
  b t (fun j => ReferenceObservation.observation B j t ω) i

def fieldProcess (B : ℝ≥0 → Ω → ℝ) (b : ℝ → (I → ℝ) → I → ℝ)
    (i : I) (t : ℝ≥0) (ω : ReferenceObservation.Space I Ω) : ℝ :=
  ReferenceObservation.observation B i t ω - ∫ s in (0 : ℝ)..(t : ℝ),
    b s (fun j => ReferenceObservation.observation B j s.toNNReal ω) i

omit [MeasurableSpace Ω] [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)] in
lemma process_fieldDrift_eq (B : ℝ≥0 → Ω → ℝ) (b : ℝ → (I → ℝ) → I → ℝ)
    (i : I) (t : ℝ≥0) (ω : ReferenceObservation.Space I Ω) :
    process B (fieldDrift B b) i t ω = fieldProcess B b i t ω := by
  unfold process fieldDrift fieldProcess
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le t.coe_nonneg] at hs
  dsimp only
  rw [Real.coe_toNNReal _ hs.1]

omit [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)] in
lemma measurable_fieldDrift
    {B : ℝ≥0 → Ω → ℝ} (hBj : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    {b : ℝ → (I → ℝ) → I → ℝ}
    (hbm : Measurable (Function.uncurry b)) (i : I) :
    Measurable (Function.uncurry (fieldDrift B b i)) := by
  have hg : Measurable (fun p : ReferenceObservation.Space I Ω × ℝ≥0 =>
      ((p.2 : ℝ), fun j => ReferenceObservation.observation B j p.2 p.1)) :=
    (NNReal.continuous_coe.measurable.comp measurable_snd).prodMk
      (Measurable.of_eval fun j =>
        (ReferenceObservation.measurable_observation_joint B hBj j).comp measurable_swap)
  exact ((measurable_pi_apply i).comp hbm).comp hg

theorem exists_iid_field_innovation [Countable I]
    (μ : ProbabilityMeasure (I → Bool)) (ν : ProbabilityMeasure Ω)
    (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B (ν : Measure Ω))
    (hBm : ∀ t, Measurable (B t))
    (hBj : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ w, Continuous (fun t => B t w))
    (ρ : Measure C(ℝ≥0, ℝ))
    (hρ : IsBrownianReal (fun t (w : C(ℝ≥0, ℝ)) => w t) ρ)
    (b : ℝ → (I → ℝ) → I → ℝ)
    (hbm : Measurable (Function.uncurry b))
    (hb : ∀ t y i, b t y i ∈ Set.Icc (0 : ℝ) 1)
    (hpost : ∀ (t : ℝ≥0) i, (fun ω : ReferenceObservation.Space I Ω =>
      b t (fun j => ReferenceObservation.observation B j t ω) i)
        =ᵐ[ReferenceObservation.law μ ν]
      (ReferenceObservation.law μ ν)[(fun ω => boolReal (ω.1 i)) |
        ObservationNoise.historySigma B t]) :
    ∃ W : ReferenceObservation.Space I Ω → I → C(ℝ≥0, ℝ), Measurable W ∧
      Measure.map W (ReferenceObservation.law μ ν) = Measure.infinitePi (fun _ : I => ρ) ∧
      ∀ᵐ ω ∂ ReferenceObservation.law μ ν, ∀ i t, W ω i t = fieldProcess B b i t ω := by
  have hcoord (i : I) : Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i) :=
    (measurable_pi_apply i).comp hbm
  have hadapt : ∀ i, Adapted (ObservationNoise.filtration (I := I) hBm)
      (process B (fieldDrift B b) i) := by
    intro i t
    have ha := InnovationAdapted.measurable_innovation_nnreal
      (ObservationNoise.filtration (I := I) hBm)
      (fun t ω j => ReferenceObservation.observation B j t ω)
      (fun j t => ObservationNoise.measurable_current_observation B t j)
      (fun ω j => ReferenceObservation.continuous_observation_path B hBc j ω)
      b hcoord i t
    change Measurable[ObservationNoise.historySigma B t]
      (fun ω => process B (fieldDrift B b) i t ω)
    simp_rw [process_fieldDrift_eq]
    exact ha
  have hcont : ∀ i, ∀ᵐ ω ∂ ReferenceObservation.law μ ν,
      Continuous (fun t => process B (fieldDrift B b) i t ω) := by
    intro i
    apply ae_of_all
    intro ω
    have hcoords (j : I) : Measurable (fun p : ℝ≥0 × (I → ℝ) =>
        b (p.1 : ℝ) p.2 j) :=
      (hcoord j).comp (NNReal.continuous_coe.measurable.comp measurable_fst |>.prodMk measurable_snd)
    have hc := InnovationAdapted.continuous_innovation_nnreal
      (fun t j => ReferenceObservation.observation B j t ω)
      (fun j => ReferenceObservation.continuous_observation_path B hBc j ω)
      (fun t => b (t : ℝ)) hcoords 1
      (fun t y j => by rw [abs_of_nonneg (hb t y j).1]; exact (hb t y j).2) i
    exact hc
  obtain ⟨W, hWm, hWlaw, hWeq⟩ := exists_iid_path_version μ ν B hB hBm ρ hρ
    (fieldDrift B b) (measurable_fieldDrift hBj hbm)
    (fun i ω t => hb t _ i) hpost hadapt hcont
  exact ⟨W, hWm, hWlaw, hWeq.mono (fun ω hω i t =>
    (hω i t).trans (process_fieldDrift_eq B b i t ω))⟩

theorem map_field_innovation_eq [Countable I]
    (μ : ProbabilityMeasure (I → Bool)) (ν : ProbabilityMeasure Ω)
    (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B (ν : Measure Ω))
    (hBm : ∀ t, Measurable (B t))
    (hBj : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ w, Continuous (fun t => B t w))
    (ρ : Measure C(ℝ≥0, ℝ))
    (hρ : IsBrownianReal (fun t (w : C(ℝ≥0, ℝ)) => w t) ρ)
    (b : ℝ → (I → ℝ) → I → ℝ)
    (hbm : Measurable (Function.uncurry b))
    (hb : ∀ t y i, b t y i ∈ Set.Icc (0 : ℝ) 1)
    (hpost : ∀ (t : ℝ≥0) i, (fun ω : ReferenceObservation.Space I Ω =>
      b t (fun j => ReferenceObservation.observation B j t ω) i)
        =ᵐ[ReferenceObservation.law μ ν]
      (ReferenceObservation.law μ ν)[(fun ω => boolReal (ω.1 i)) |
        ObservationNoise.historySigma B t])
    (Z : ReferenceObservation.Space I Ω → I → C(ℝ≥0, ℝ))
    (hZ : ∀ ω i t, Z ω i t = fieldProcess B b i t ω) :
    Measure.map Z (ReferenceObservation.law μ ν) = Measure.infinitePi (fun _ : I => ρ) := by
  obtain ⟨W, _, hWlaw, hWeq⟩ :=
    exists_iid_field_innovation μ ν B hB hBm hBj hBc ρ hρ b hbm hb hpost
  have heq : Z =ᵐ[ReferenceObservation.law μ ν] W := by
    filter_upwards [hWeq] with ω hω
    funext i
    apply ContinuousMap.coe_injective
    funext t
    exact (hZ ω i t).trans (hω i t).symm
  exact (Measure.map_congr heq).trans hWlaw

end Problem336AdditiveD139.ReferenceInnovationLaw

end

end OAI
