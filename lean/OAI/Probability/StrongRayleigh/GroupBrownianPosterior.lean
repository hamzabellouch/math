import OAI.Probability.StrongRayleigh.BrownianObservationSufficiency
import OAI.Probability.StrongRayleigh.GroupDriftPosterior
import OAI.Probability.StrongRayleigh.FiniteEndpointPosterior

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

namespace Problem336AdditiveD139.GroupBrownianPosterior

open PosteriorLimit BrownianObservationSufficiency

theorem measurable_binaryField {I : Type u_1} :
    Measurable (fun x : I → Bool => fun i => boolReal (x i)) :=
  Measurable.of_eval fun i =>
    (measurable_of_countable boolReal).comp (measurable_pi_apply i)

theorem integrable_binaryCoordinate {Ω : Type u_2} {I : Type u_3} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → I → Bool)
    (mX : Measurable X) (i : I) :
    Integrable (fun ω => boolReal (X ω i)) P := by
  apply (integrable_const (1 : ℝ)).mono'
    (((measurable_pi_apply i).comp (measurable_binaryField.comp mX)).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro ω
  cases hx : X ω i <;> simp [boolReal, hx]

theorem finiteFieldMean_congr_on {I : Type u_4}
    (μ : ProbabilityMeasure (I → Bool)) (S : Finset I) (i : I)
    (h h' : I → ℝ) (hh : ∀ j ∈ S, h j = h' j) :
    finiteFieldMean μ S h i = finiteFieldMean μ S h' i := by
  have hw (x : I → Bool) : finiteFieldWeight S h x = finiteFieldWeight S h' x := by
    unfold finiteFieldWeight
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [hh j hj]
  simp only [finiteFieldMean, hw]

theorem finiteFieldMean_zero {I : Type u_5}
    (μ : ProbabilityMeasure (I → Bool)) (S : Finset I) (i : I) :
    finiteFieldMean μ S (fun _ => 0) i =
      ∫ x, boolReal (x i) ∂(μ : Measure (I → Bool)) := by
  simp [finiteFieldMean, finiteFieldWeight]

theorem finiteFieldMean_zero_endpoint_posterior
    {I : Type u_6} {Ω : Type u_7} [MeasurableSpace Ω]
    (P : Measure Ω) (μ : ProbabilityMeasure (I → Bool))
    {B : I → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (mB : ∀ i, Measurable (B i 0))
    (X : Ω → I → Bool) (mX : Measurable X)
    (hLaw : HasLaw X (μ : Measure (I → Bool)) P)
    (S : Finset I) (i : I) :
    (fun ω => finiteFieldMean μ S (fun j => B j 0 ω) i) =ᵐ[P]
      P[(fun ω => boolReal (X ω i)) |
        MeasurableSpace.comap (fun ω (j : (S : Set I)) => B j 0 ω) inferInstance] := by
  have := hLaw.isProbabilityMeasure
  have hzero : ∀ᵐ ω ∂P, ∀ j : S, B j 0 ω = 0 :=
    ae_all_iff.mpr (fun j => (hB j).eval_zero_ae_eq_zero)
  have hmean : (fun ω => finiteFieldMean μ S (fun j => B j 0 ω) i) =ᵐ[P]
      fun _ => ∫ x, boolReal (x i) ∂(μ : Measure (I → Bool)) := by
    filter_upwards [hzero] with ω hω
    rw [finiteFieldMean_congr_on μ S i (fun j => B j 0 ω) (fun _ => 0)
      (fun j hj => hω ⟨j, hj⟩), finiteFieldMean_zero]
  have mg : Measurable (fun x : I → Bool => boolReal (x i)) :=
    (measurable_pi_apply i).comp measurable_binaryField
  have hCE := condExp_endpoint_zero_eq_integral hB mB
    (fun ω => boolReal (X ω i)) (mg.comp mX) (S : Set I)
  have hInt : (∫ ω, boolReal (X ω i) ∂P) =
      ∫ x, boolReal (x i) ∂(μ : Measure (I → Bool)) :=
    hLaw.integral_comp mg.aestronglyMeasurable
  rw [hInt] at hCE
  exact hmean.trans hCE.symm

theorem groupDrift_ae_eq_condExp_of_endpoint_posteriors
    {Γ : Type u_8} {Ω : Type u_9} [Group Γ] [Countable Γ] [DecidableEq Γ] [MeasurableSpace Ω]
    (P : Measure Ω) (μ : ProbabilityMeasure (Γ → Bool))
    {B : Γ → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hIndep : iIndepFun (fun i ω s => B i s ω) P)
    (mB : ∀ i s, Measurable (B i s))
    (X : Ω → Γ → Bool) (mX : Measurable X)
    (hX : IndepFun X (fun ω (p : Γ × ℝ≥0) => B p.1 p.2 ω) P)
    (t : ℝ≥0)
    (hEndpoint : ∀ (i : Γ) (S : Finset Γ),
      (fun ω => finiteFieldMean μ S
        (fun j => (t : ℝ) * boolReal (X ω j) + B j t ω - (t : ℝ) / 2) i) =ᵐ[P]
        P[(fun ω => boolReal (X ω i)) |
          endpointSpace
            (fun j (s : Set.Iic t) ω =>
              (s.1 : ℝ) * boolReal (X ω j) + B j s.1 ω)
            (S : Set Γ) ⟨t, by simp⟩])
    (i : Γ) :
    (fun ω => groupDrift μ (t : ℝ)
      (fun j => (t : ℝ) * boolReal (X ω j) + B j t ω) i) =ᵐ[P]
      P[(fun ω => boolReal (X ω i)) |
        observationSpace
          (fun j (s : Set.Iic t) ω =>
            (s.1 : ℝ) * boolReal (X ω j) + B j s.1 ω) Set.univ] := by
  have := hIndep.isProbabilityMeasure
  have mbit (j : Γ) : Measurable (fun ω => boolReal (X ω j)) :=
    (measurable_pi_apply j).comp (measurable_binaryField.comp mX)
  apply groupDrift_ae_eq_condExp_of_finite_posteriors P μ
    (fun j ω => boolReal (X ω j))
    (fun j (s : Set.Iic t) ω => (s.1 : ℝ) * boolReal (X ω j) + B j s.1 ω)
    (fun j s => (mbit j).const_mul _ |>.add (mB j s)) (t : ℝ) ⟨t, by simp⟩
    (fun j S => ?_) i
  have he := hEndpoint j S
  simp only [finiteObservationDrift_eq_finiteFieldMean]
  exact he.trans
    (condExp_history_eq_endpoint_all hB hIndep mB mX hX
      (fun x k => boolReal (x k)) measurable_binaryField
      (fun x => boolReal (x j))
      ((measurable_pi_apply j).comp measurable_binaryField)
      (integrable_binaryCoordinate P X mX j) (S : Set Γ) t).symm

theorem groupDrift_ae_eq_condExp_of_positive_endpoint_posteriors
    {Γ : Type u_10} {Ω : Type u_11} [Group Γ] [Countable Γ] [DecidableEq Γ] [MeasurableSpace Ω]
    (P : Measure Ω) (μ : ProbabilityMeasure (Γ → Bool))
    {B : Γ → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hIndep : iIndepFun (fun i ω s => B i s ω) P)
    (mB : ∀ i s, Measurable (B i s))
    (X : Ω → Γ → Bool) (mX : Measurable X)
    (hLaw : HasLaw X (μ : Measure (Γ → Bool)) P)
    (hX : IndepFun X (fun ω (p : Γ × ℝ≥0) => B p.1 p.2 ω) P)
    (t : ℝ≥0)
    (hEndpoint : 0 < t → ∀ (i : Γ) (S : Finset Γ),
      (fun ω => finiteFieldMean μ S
        (fun j => (t : ℝ) * boolReal (X ω j) + B j t ω - (t : ℝ) / 2) i) =ᵐ[P]
        P[(fun ω => boolReal (X ω i)) |
          endpointSpace
            (fun j (s : Set.Iic t) ω =>
              (s.1 : ℝ) * boolReal (X ω j) + B j s.1 ω)
            (S : Set Γ) ⟨t, by simp⟩])
    (i : Γ) :
    (fun ω => groupDrift μ (t : ℝ)
      (fun j => (t : ℝ) * boolReal (X ω j) + B j t ω) i) =ᵐ[P]
      P[(fun ω => boolReal (X ω i)) |
        observationSpace
          (fun j (s : Set.Iic t) ω =>
            (s.1 : ℝ) * boolReal (X ω j) + B j s.1 ω) Set.univ] := by
  apply groupDrift_ae_eq_condExp_of_endpoint_posteriors P μ hB hIndep mB X mX hX t
    (fun j S => ?_) i
  by_cases ht : t = 0
  · subst t
    simpa! only [NNReal.coe_zero, zero_mul, zero_div, zero_add, sub_zero,
      endpointSpace_eq_comap] using
      finiteFieldMean_zero_endpoint_posterior P μ hB (fun j => mB j 0) X mX hLaw S j
  · exact hEndpoint (pos_of_ne_zero ht) j S

theorem groupDrift_ae_eq_condExp
    {Γ : Type u_12} {Ω : Type u_13} [Group Γ] [Countable Γ] [DecidableEq Γ] [MeasurableSpace Ω]
    (P : Measure Ω) (μ : ProbabilityMeasure (Γ → Bool))
    {B : Γ → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hIndep : iIndepFun (fun i ω s => B i s ω) P)
    (mB : ∀ i s, Measurable (B i s))
    (X : Ω → Γ → Bool) (mX : Measurable X)
    (hLaw : HasLaw X (μ : Measure (Γ → Bool)) P)
    (hX : IndepFun X (fun ω (p : Γ × ℝ≥0) => B p.1 p.2 ω) P)
    (t : ℝ≥0) (i : Γ) :
    (fun ω => groupDrift μ (t : ℝ)
      (fun j => (t : ℝ) * boolReal (X ω j) + B j t ω) i) =ᵐ[P]
      P[(fun ω => boolReal (X ω i)) |
        observationSpace
          (fun j (s : Set.Iic t) ω =>
            (s.1 : ℝ) * boolReal (X ω j) + B j s.1 ω) Set.univ] := by
  have := hLaw.isProbabilityMeasure
  have mZ : Measurable (fun ω j => B j t ω) :=
    Measurable.of_eval (fun j => mB j t)
  have hXZ : IndepFun X (fun ω j => B j t ω) P := by
    simpa only [Function.comp_def, Function.id_def] using hX.comp measurable_id
      (show Measurable (fun f : (Γ × ℝ≥0) → ℝ => fun j => f (j, t)) by fun_prop)
  apply groupDrift_ae_eq_condExp_of_endpoint_posteriors P μ hB hIndep mB X mX hX t
    (fun j S => ?_) i
  have hSInd : iIndepFun (fun (j : S) ω => B j t ω) P :=
    (iIndepFun.precomp (g := fun j : S => (j : Γ))
      Subtype.val_injective hIndep).comp
        (fun _ f => f t) (fun _ => measurable_pi_apply t)
  have hSLaw : HasLaw (fun ω => fun j : S => B j t ω)
      (Measure.pi (fun _ : S => gaussianReal 0 t)) P :=
    iIndepFun.hasLaw_pi (fun j => (hB j).hasLaw_eval t) hSInd
  have hp := (finiteObservationDrift_condExp P μ X mX hLaw j S
    (fun ω k => B k t ω) mZ t hSLaw hXZ).symm
  simpa only [finiteObservationDrift_eq_finiteFieldMean, endpointSpace,
    MeasurableSpace.comap_process_pi, iSup_subtype, Finset.mem_coe] using hp

end Problem336AdditiveD139.GroupBrownianPosterior

end

end OAI
