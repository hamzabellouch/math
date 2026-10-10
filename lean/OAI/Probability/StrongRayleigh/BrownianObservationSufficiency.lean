import OAI.Probability.StrongRayleigh.BrownianBridgeSignal
import OAI.Probability.StrongRayleigh.IndependentConditioning
import OAI.Probability.StrongRayleigh.ObservationHistory

namespace OAI

universe u_1 u_2 u_3

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

namespace Problem336AdditiveD139.BrownianObservationSufficiency

open PosteriorLimit

variable {Ω : Type u_1} {I : Type u_2} {α : Type u_3} [MeasurableSpace Ω] [MeasurableSpace α]
  {P : Measure Ω}

theorem condExp_history_eq_endpoint
    {B : I → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hIndep : iIndepFun (fun i ω s => B i s ω) P)
    (mB : ∀ i s, Measurable (B i s))
    {X : Ω → α} (mX : Measurable X)
    (hX : IndepFun X (fun ω (p : I × ℝ≥0) => B p.1 p.2 ω) P)
    (a : α → I → ℝ) (ma : Measurable a)
    (f : α → ℝ) (mf : Measurable f) (hf : Integrable (fun ω => f (X ω)) P)
    (J : Set I) (t : ℝ≥0) (ht : t ≠ 0) :
    P[(fun ω => f (X ω)) |
      observationSpace
        (fun i (s : Set.Iic t) ω => (s.1 : ℝ) * a (X ω) i + B i s.1 ω) J]
      =ᵐ[P]
    P[(fun ω => f (X ω)) |
      endpointSpace
        (fun i (s : Set.Iic t) ω => (s.1 : ℝ) * a (X ω) i + B i s.1 ω)
        J ⟨t, by simp⟩] := by
  have := hIndep.isProbabilityMeasure
  have hIndepJ : iIndepFun (fun (i : J) ω s => B i s ω) P :=
    hIndep.precomp Subtype.val_injective
  have hXJ : IndepFun X (fun ω (p : J × ℝ≥0) => B p.1 p.2 ω) P := by
    simpa only [Function.comp_def, id_eq] using
      hX.comp measurable_id
        (show Measurable (fun z : I × ℝ≥0 → ℝ =>
          fun p : J × ℝ≥0 => z (p.1.1, p.2)) by fun_prop)
  have hbridge := brownianBridgeFamily_indep_signal_endpoints
    (fun i : J => hB i) hIndepJ (fun i : J => mB i) mX hXJ t ht
  have hpair : IndepFun
      (fun ω => (f (X ω), fun i : J => (t : ℝ) * a (X ω) i + B i t ω))
      (fun ω (i : J) (s : Set.Iic t) =>
        B i s ω - (s.1 : ℝ) / (t : ℝ) * B i t ω) P := by
    simpa only [Function.comp_def, id_eq] using hbridge.symm.comp
      (show Measurable (fun z : α × (J → ℝ) =>
        (f z.1, fun i : J => (t : ℝ) * a z.1 i + z.2 i)) by fun_prop)
      (show Measurable (fun z : (J × Set.Iic t) → ℝ =>
        fun (i : J) (s : Set.Iic t) => z (i, s)) by fun_prop)
  rw [signal_observationSpace_eq_endpoint_sup_noise_bridge
    (fun i ω => a (X ω) i) B J t ht,
    endpointSpace_eq_comap, observationSpace_eq_comap]
  exact IndependentConditioning.condExp_sup_comap_of_indepFun
    (mf.comp mX)
    (show Measurable (fun ω (i : J) => (t : ℝ) * a (X ω) i + B i t ω) by fun_prop)
    (show Measurable (fun ω (i : J) (s : Set.Iic t) =>
      B i s ω - (s.1 : ℝ) / (t : ℝ) * B i t ω) by fun_prop)
    hf hpair

theorem posterior_history_of_endpoint
    {B : I → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hIndep : iIndepFun (fun i ω s => B i s ω) P)
    (mB : ∀ i s, Measurable (B i s))
    {X : Ω → α} (mX : Measurable X)
    (hX : IndepFun X (fun ω (p : I × ℝ≥0) => B p.1 p.2 ω) P)
    (a : α → I → ℝ) (ma : Measurable a)
    (f : α → ℝ) (mf : Measurable f) (hf : Integrable (fun ω => f (X ω)) P)
    (J : Set I) (t : ℝ≥0) (ht : t ≠ 0)
    (posterior : Ω → ℝ)
    (hp : posterior =ᵐ[P] P[(fun ω => f (X ω)) |
      endpointSpace
        (fun i (s : Set.Iic t) ω => (s.1 : ℝ) * a (X ω) i + B i s.1 ω)
        J ⟨t, by simp⟩]) :
    posterior =ᵐ[P] P[(fun ω => f (X ω)) |
      observationSpace
        (fun i (s : Set.Iic t) ω => (s.1 : ℝ) * a (X ω) i + B i s.1 ω) J] :=
  hp.trans (condExp_history_eq_endpoint hB hIndep mB mX hX a ma f mf hf J t ht).symm

omit [MeasurableSpace Ω] in

theorem observationSpace_zero_eq_endpointSpace
    (Y : I → Set.Iic (0 : ℝ≥0) → Ω → ℝ) (J : Set I) :
    observationSpace Y J = endpointSpace Y J ⟨0, by simp⟩ := by
  apply le_antisymm
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun s => ?_
    have hs : s = ⟨0, by simp⟩ := by
      apply Subtype.ext
      exact le_antisymm s.2 zero_le
    rw [hs]
    exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)
  · exact endpointSpace_le_observationSpace Y J ⟨0, by simp⟩

theorem condExp_history_eq_endpoint_all
    {B : I → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hIndep : iIndepFun (fun i ω s => B i s ω) P)
    (mB : ∀ i s, Measurable (B i s))
    {X : Ω → α} (mX : Measurable X)
    (hX : IndepFun X (fun ω (p : I × ℝ≥0) => B p.1 p.2 ω) P)
    (a : α → I → ℝ) (ma : Measurable a)
    (f : α → ℝ) (mf : Measurable f) (hf : Integrable (fun ω => f (X ω)) P)
    (J : Set I) (t : ℝ≥0) :
    P[(fun ω => f (X ω)) |
      observationSpace
        (fun i (s : Set.Iic t) ω => (s.1 : ℝ) * a (X ω) i + B i s.1 ω) J]
      =ᵐ[P]
    P[(fun ω => f (X ω)) |
      endpointSpace
        (fun i (s : Set.Iic t) ω => (s.1 : ℝ) * a (X ω) i + B i s.1 ω)
        J ⟨t, by simp⟩] := by
  by_cases ht : t = 0
  · subst t
    rw [observationSpace_zero_eq_endpointSpace]
  · exact condExp_history_eq_endpoint hB hIndep mB mX hX a ma f mf hf J t ht

theorem limsup_endpoint_posteriors_eq_full_history
    {B : I → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hIndep : iIndepFun (fun i ω s => B i s ω) P)
    (mB : ∀ i s, Measurable (B i s))
    {X : Ω → α} (mX : Measurable X)
    (hX : IndepFun X (fun ω (p : I × ℝ≥0) => B p.1 p.2 ω) P)
    (a : α → I → ℝ) (ma : Measurable a)
    (f : α → ℝ) (mf : Measurable f) (hf : Integrable (fun ω => f (X ω)) P)
    (J : ℕ → Set I) (hmono : Monotone J) (hexhaust : ∀ i, ∃ n, i ∈ J n)
    (t : ℝ≥0) (b : ℕ → Ω → ℝ)
    (hb : ∀ n, b n =ᵐ[P] P[(fun ω => f (X ω)) |
      endpointSpace
        (fun i (s : Set.Iic t) ω => (s.1 : ℝ) * a (X ω) i + B i s.1 ω)
        (J n) ⟨t, by simp⟩]) :
    (fun ω => Filter.limsup (fun n => b n ω) Filter.atTop) =ᵐ[P]
      P[(fun ω => f (X ω)) |
        observationSpace
          (fun i (s : Set.Iic t) ω => (s.1 : ℝ) * a (X ω) i + B i s.1 ω) Set.univ] := by
  have := hIndep.isProbabilityMeasure
  apply limsup_ae_eq_full_observation_condExp
    (fun i (s : Set.Iic t) ω => (s.1 : ℝ) * a (X ω) i + B i s.1 ω)
    (by intro i s; fun_prop) J hmono hexhaust (fun ω => f (X ω)) b
  intro n
  exact (hb n).trans
    (condExp_history_eq_endpoint_all hB hIndep mB mX hX a ma f mf hf (J n) t).symm

theorem condExp_endpoint_zero_eq_integral [IsProbabilityMeasure P]
    {B : I → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (mB : ∀ i, Measurable (B i 0))
    (g : Ω → ℝ) (mg : Measurable g)
    (J : Set I) [Countable J] :
    P[g | MeasurableSpace.comap (fun ω (i : J) => B i 0 ω) inferInstance]
      =ᵐ[P] fun _ => ∫ ω, g ω ∂P := by
  have hzero : (fun ω (i : J) => B i 0 ω) =ᵐ[P] (fun _ _ => (0 : ℝ)) := by
    have hall : ∀ᵐ ω ∂P, ∀ i : J, B i 0 ω = 0 :=
      ae_all_iff.mpr (fun i => (hB i).eval_zero_ae_eq_zero)
    filter_upwards [hall] with ω hω
    exact funext hω
  have hind : IndepFun g (fun ω (i : J) => B i 0 ω) P :=
    (indepFun_const_right g (fun _ : J => (0 : ℝ))).congr
      Filter.EventuallyEq.rfl hzero.symm
  exact condExp_indep_eq mg.comap_le
    (Measurable.of_eval fun i : J => mB i).comap_le
    (comap_measurable g).stronglyMeasurable hind

end Problem336AdditiveD139.BrownianObservationSufficiency

end

end OAI
