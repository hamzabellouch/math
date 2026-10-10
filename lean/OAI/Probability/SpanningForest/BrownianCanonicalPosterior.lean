import OAI.Probability.SpanningForest.CanonicalPosteriorIdentification
import OAI.Probability.SpanningForest.BrownianPosteriorReduction
import OAI.Probability.SpanningForest.BinaryGaussianPosterior

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal BigOperators ProbabilityTheory Topology

namespace Problem336.Observation

theorem gaussianFiniteTilt_finset_eq {I : Type*}
    (μ : ProbabilityMeasure (I → Bool)) (S : Finset I) (e : I)
    (t : ℝ) (y : I → ℝ) :
    FinitePosterior.gaussianFiniteTilt (μ : Measure (I → Bool))
      (fun i : S => (i : I)) e t (fun i => y i) =
      TiltLimit.finiteTiltMean μ S (fun i => y i - t / 2) e := by
  unfold FinitePosterior.gaussianFiniteTilt TiltLimit.finiteTiltMean
    TiltLimit.tiltedMean TiltLimit.finiteEnergy
  have hsum (x : I → Bool) :
      (∑ i : S, (y i - t / 2) * FinitePosterior.binaryValue (x i)) =
        ∑ i ∈ S, (y i - t / 2) * FinitePosterior.binaryValue (x i) :=
    Finset.sum_coe_sort S (fun i : I => (y i - t / 2) * FinitePosterior.binaryValue (x i))
  simp_rw [hsum]
  simp only [FinitePosterior.binaryValue, TiltLimit.bit]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => mul_comm _ _)

theorem finiteTiltMean_eq_condExp_brownian_history
    {Ω I : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : ProbabilityMeasure (I → Bool)) (X : Ω → I → Bool) (hX : Measurable X)
    (hprior : P.map X = (μ : Measure (I → Bool)))
    (B : I → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω s => B i s ω) P)
    (hBm : ∀ i s, Measurable (B i s))
    (hXB : IndepFun X (fun ω (p : I × ℝ≥0) => B p.1 p.2 ω) P)
    (S : Finset I) (e : I) (t : ℝ≥0) (ht : t ≠ 0) :
    (fun ω => TiltLimit.finiteTiltMean μ S
      (fun i => (t : ℝ) * TiltLimit.bit (X ω i) + B i t ω - (t : ℝ) / 2) e) =ᵐ[P]
      P[fun ω => TiltLimit.bit (X ω e) |
        historySigma (fun (i : S) (s : Set.Iic t) ω =>
          (s : ℝ) * TiltLimit.bit (X ω i) + B i s ω)] := by
  classical
  let noise : Ω → S → ℝ := fun ω i => B i t ω
  have hnoise : Measurable noise := Measurable.of_eval (fun i => hBm i t)
  have hbind : iIndepFun (fun (i : S) ω s => B i s ω) P :=
    hind.precomp Subtype.val_injective
  have heind : iIndepFun (fun (i : S) ω => B i t ω) P :=
    hbind.comp (fun _ f => f t) (fun _ => measurable_pi_apply t)
  have hnoiseLaw : P.map noise = Measure.pi (fun _ : S => gaussianReal 0 t) := by
    rw [iIndepFun.map_fun_eq_pi_map (fun (i : S) => (hBm i t).aemeasurable) heind]
    congr 1
    funext i
    exact (hB i).hasLaw_eval t |>.map_eq
  have hXnoise : IndepFun X noise P := hXB.comp measurable_id
    (show Measurable (fun f : I × ℝ≥0 → ℝ => fun i : S => f (i, t)) by fun_prop)
  have hXsub : IndepFun X (fun ω (p : S × ℝ≥0) => B p.1 p.2 ω) P :=
    hXB.comp measurable_id
      (show Measurable (fun f : I × ℝ≥0 → ℝ => fun p : S × ℝ≥0 => f (p.1, p.2)) by
        fun_prop)
  let D : (I → Bool) → S → ℝ := fun x i => TiltLimit.bit (x i)
  have hD : Measurable D := Measurable.of_eval (fun i =>
    TiltLimit.continuous_bit.measurable.comp (measurable_pi_apply (i : I)))
  let f : (I → Bool) → ℝ := fun x => TiltLimit.bit (x e)
  have hf : Measurable f :=
    TiltLimit.continuous_bit.measurable.comp (measurable_pi_apply e)
  have hfi : Integrable (f ∘ X) P := by
    exact (show Integrable TiltLimit.bit (P.map (fun ω => X ω e)) from
      Integrable.of_finite).comp_measurable ((measurable_pi_apply e).comp hX)
  have hh := BrownianBridge.condExp_observation_history_eq_endpoint
    (fun (i : S) => hB i) hbind (fun i s => hBm i s) hX D hD hXsub t ht f hf hfi
  have he := FinitePosterior.binaryField_gaussian_condExp P
    (μ : Measure (I → Bool)) X noise hX hnoise (fun i : S => (i : I)) e t ht
    hprior hnoiseLaw hXnoise
  have he' : P[f ∘ X | MeasurableSpace.comap
      (fun ω (i : S) => (t : ℝ) * TiltLimit.bit (X ω i) + B i t ω) inferInstance] =ᵐ[P]
      fun ω => TiltLimit.finiteTiltMean μ S
        (fun i => (t : ℝ) * TiltLimit.bit (X ω i) + B i t ω - (t : ℝ) / 2) e := by
    filter_upwards [he] with ω hω
    exact hω.trans (gaussianFiniteTilt_finset_eq μ S e t
      (fun i => (t : ℝ) * TiltLimit.bit (X ω i) + B i t ω))
  exact (hh.trans he').symm

theorem drift_eq_condExp_brownian_history
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : ProbabilityMeasure (I → Bool)) (X : Ω → I → Bool) (hX : Measurable X)
    (hprior : P.map X = (μ : Measure (I → Bool)))
    (B : I → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω s => B i s ω) P)
    (hBm : ∀ i s, Measurable (B i s))
    (hXB : IndepFun X (fun ω (p : I × ℝ≥0) => B p.1 p.2 ω) P)
    (S : I → ℕ → Finset I) (e : I)
    (hS : Monotone (S e)) (hcover : ∀ i, ∃ n, i ∈ S e n)
    (t : ℝ≥0) (ht : t ≠ 0) :
    (fun ω => PosteriorDrift.drift μ S t
      (fun i => (t : ℝ) * TiltLimit.bit (X ω i) + B i t ω) e) =ᵐ[P]
      P[fun ω => TiltLimit.bit (X ω e) |
        historySigma (fun i (s : Set.Iic t) ω =>
          (s : ℝ) * TiltLimit.bit (X ω i) + B i s ω)] := by
  apply drift_eq_condExp_of_finite_history P μ S e hS hcover
    (fun i s ω => (s : ℝ) * TiltLimit.bit (X ω i) + B i s ω)
  · intro i s
    exact ((TiltLimit.continuous_bit.measurable.comp
      ((measurable_pi_apply i).comp hX)).const_mul _).add (hBm i s)
  · intro n
    exact finiteTiltMean_eq_condExp_brownian_history P μ X hX hprior B hB hind hBm hXB
      (S e n) e t ht

theorem drift_zero_zero {I : Type*} [Countable I]
    (μ : ProbabilityMeasure (I → Bool)) (S : I → ℕ → Finset I) (e : I) :
    PosteriorDrift.drift μ S 0 (fun _ => 0) e =
      ∫ x, TiltLimit.bit (x e) ∂(μ : Measure (I → Bool)) := by
  apply PosteriorDrift.drift_eq_of_tendsto
  simp [TiltLimit.finiteTiltMean, TiltLimit.tiltedMean, TiltLimit.finiteEnergy]

theorem drift_eq_condExp_brownian_history_zero
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : ProbabilityMeasure (I → Bool)) (X : Ω → I → Bool) (hX : Measurable X)
    (hprior : P.map X = (μ : Measure (I → Bool)))
    (B : I → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hBm : ∀ i s, Measurable (B i s))
    (S : I → ℕ → Finset I) (e : I) :
    (fun ω => PosteriorDrift.drift μ S 0
      (fun i => (0 : ℝ) * TiltLimit.bit (X ω i) + B i 0 ω) e) =ᵐ[P]
      P[fun ω => TiltLimit.bit (X ω e) |
        historySigma (fun i (s : Set.Iic (0 : ℝ≥0)) ω =>
          (s : ℝ) * TiltLimit.bit (X ω i) + B i s ω)] := by
  let H := fun ω (p : I × Set.Iic (0 : ℝ≥0)) =>
    (p.2 : ℝ) * TiltLimit.bit (X ω p.1) + B p.1 p.2 ω
  have hH : Measurable H := by
    apply Measurable.of_eval
    intro p
    exact ((TiltLimit.continuous_bit.measurable.comp
      ((measurable_pi_apply p.1).comp hX)).const_mul _).add (hBm p.1 p.2)
  have hzero : ∀ᵐ ω ∂P, ∀ i, B i 0 ω = 0 :=
    ae_all_iff.mpr (fun i => (hB i).eval_zero_ae_eq_zero)
  have hHzero : H =ᵐ[P] fun _ => (0 : I × Set.Iic (0 : ℝ≥0) → ℝ) := by
    filter_upwards [hzero] with ω hω
    funext p
    have hs : (p.2 : ℝ≥0) = 0 := le_antisymm p.2.2 (by positivity)
    simp [H, hs, hω p.1]
  have hind0 : IndepFun X H P :=
    (indepFun_const_right X (0 : I × Set.Iic (0 : ℝ≥0) → ℝ)).congr
      Filter.EventuallyEq.rfl hHzero.symm
  have hs : StronglyMeasurable[(inferInstance : MeasurableSpace (I → Bool)).comap X]
      (fun ω => TiltLimit.bit (X ω e)) :=
    (TiltLimit.continuous_bit.measurable.comp
      ((measurable_pi_apply e).comp (comap_measurable X))).stronglyMeasurable
  have hc := condExp_indep_eq hX.comap_le hH.comap_le hs hind0
  have hmean : (∫ ω, TiltLimit.bit (X ω e) ∂P) =
      ∫ x, TiltLimit.bit (x e) ∂(μ : Measure (I → Bool)) := by
    rw [← hprior]
    exact (integral_map_of_stronglyMeasurable hX
      (TiltLimit.continuous_bit.measurable.comp (measurable_pi_apply e)).stronglyMeasurable).symm
  filter_upwards [hzero, hc] with ω hω hcω
  have hy : (fun i => (0 : ℝ) * TiltLimit.bit (X ω i) + B i 0 ω) =
      (fun _ => 0) := by
    funext i
    simp [hω i]
  rw [hy, drift_zero_zero]
  exact hmean.symm.trans hcω.symm

theorem drift_eq_condExp_brownian_history_all_times
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : ProbabilityMeasure (I → Bool)) (X : Ω → I → Bool) (hX : Measurable X)
    (hprior : P.map X = (μ : Measure (I → Bool)))
    (B : I → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω s => B i s ω) P)
    (hBm : ∀ i s, Measurable (B i s))
    (hXB : IndepFun X (fun ω (p : I × ℝ≥0) => B p.1 p.2 ω) P)
    (S : I → ℕ → Finset I) (e : I)
    (hS : Monotone (S e)) (hcover : ∀ i, ∃ n, i ∈ S e n)
    (t : ℝ≥0) :
    (fun ω => PosteriorDrift.drift μ S t
      (fun i => (t : ℝ) * TiltLimit.bit (X ω i) + B i t ω) e) =ᵐ[P]
      P[fun ω => TiltLimit.bit (X ω e) |
        historySigma (fun i (s : Set.Iic t) ω =>
          (s : ℝ) * TiltLimit.bit (X ω i) + B i s ω)] := by
  by_cases ht : t = 0
  · subst t
    exact drift_eq_condExp_brownian_history_zero P μ X hX hprior B hB hBm S e
  · exact drift_eq_condExp_brownian_history P μ X hX hprior B hB hind hBm hXB
      S e hS hcover t ht

end Problem336.Observation

end

end OAI
