import OAI.Probability.SpanningForest.BrownianBridge
import OAI.Probability.SpanningForest.PosteriorIndependentExtension

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

namespace Problem336.BrownianBridge

theorem condExp_observation_history_eq_endpoint
    {Ω I A : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace A] {P : Measure Ω}
    {C : I → ℝ≥0 → Ω → ℝ} (hC : ∀ i, IsPreBrownianReal (C i) P)
    (hind : iIndepFun (fun i ω s => C i s ω) P)
    (hCm : ∀ i s, Measurable (C i s)) {X : Ω → A} (hXm : Measurable X)
    (D : A → I → ℝ) (hD : Measurable D)
    (hXC : IndepFun X (fun ω (p : I × ℝ≥0) => C p.1 p.2 ω) P)
    (t : ℝ≥0) (ht : t ≠ 0) (f : A → ℝ) (hf : Measurable f)
    (hfi : Integrable (f ∘ X) P) :
    P[f ∘ X | MeasurableSpace.comap
      (fun ω (p : I × Set.Iic t) => (p.2 : ℝ) * D (X ω) p.1 + C p.1 p.2 ω) inferInstance]
      =ᵐ[P]
    P[f ∘ X | MeasurableSpace.comap
      (fun ω i => (t : ℝ) * D (X ω) i + C i t ω) inferInstance] := by
  have := hind.isProbabilityMeasure
  let E := fun ω i => (t : ℝ) * D (X ω) i + C i t ω
  let R := fun ω (p : I × Set.Iic t) => residual (C p.1) t p.2 ω
  let hidden := MeasurableSpace.comap (fun ω => (X ω, E ω)) inferInstance
  let : MeasurableSpace Ω := mΩ
  have hE : Measurable[mΩ] E := by
    apply Measurable.of_eval
    intro i
    exact (((measurable_pi_apply i).comp (hD.comp hXm)).const_mul _).add (hCm i t)
  have hR : Measurable[mΩ] R := by
    apply Measurable.of_eval
    intro p
    exact (hCm p.1 p.2).sub ((hCm p.1 t).const_mul _)
  have hhidden : hidden ≤ mΩ := (hXm.prodMk hE).comap_le
  have hobs : MeasurableSpace.comap E inferInstance ≤ hidden :=
    (comap_measurable (fun ω => (X ω, E ω))).snd.comap_le
  have hXhidden : @Measurable Ω A hidden _ X :=
    (comap_measurable (fun ω => (X ω, E ω))).fst
  have hfh : StronglyMeasurable[hidden] (f ∘ X) := (hf.comp hXhidden).stronglyMeasurable
  have hbridge : Indep hidden (MeasurableSpace.comap R inferInstance) P :=
    (indepFun_residual_family_hidden_endpoint hC hind hCm hXm D hD hXC t ht).symm
  rw [observation_family_history_comap C X D t ht]
  exact Observation.condExp_sup_independent P hhidden hR.comap_le hobs hfh hfi hbridge

theorem zero_history_comap {Ω I : Type*} (C : I → ℝ≥0 → Ω → ℝ) :
    MeasurableSpace.comap (fun ω (p : I × Set.Iic (0 : ℝ≥0)) => C p.1 p.2 ω) inferInstance =
      MeasurableSpace.comap (fun ω i => C i 0 ω) inferInstance := by
  let H := fun ω (p : I × Set.Iic (0 : ℝ≥0)) => C p.1 p.2 ω
  let E := fun ω i => C i 0 ω
  let extract : (I × Set.Iic (0 : ℝ≥0) → ℝ) → (I → ℝ) :=
    fun f i => f (i, ⟨0, by simp⟩)
  let extend : (I → ℝ) → (I × Set.Iic (0 : ℝ≥0) → ℝ) := fun f p => f p.1
  have he : Measurable extract := by fun_prop
  have hx : Measurable extend := by fun_prop
  have hE : E = extract ∘ H := rfl
  have hH : H = extend ∘ E := by
    funext ω ⟨i, s, hs⟩
    have hs0 : s = 0 := le_antisymm hs (by positivity)
    subst s
    rfl
  change MeasurableSpace.comap H _ = MeasurableSpace.comap E _
  apply le_antisymm
  · rw [hH, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hx.comap_le
  · rw [hE, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono he.comap_le

theorem condExp_observation_history_eq_endpoint_all
    {Ω I A : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace A] {P : Measure Ω}
    {C : I → ℝ≥0 → Ω → ℝ} (hC : ∀ i, IsPreBrownianReal (C i) P)
    (hind : iIndepFun (fun i ω s => C i s ω) P)
    (hCm : ∀ i s, Measurable (C i s)) {X : Ω → A} (hXm : Measurable X)
    (D : A → I → ℝ) (hD : Measurable D)
    (hXC : IndepFun X (fun ω (p : I × ℝ≥0) => C p.1 p.2 ω) P)
    (t : ℝ≥0) (f : A → ℝ) (hf : Measurable f)
    (hfi : Integrable (f ∘ X) P) :
    P[f ∘ X | MeasurableSpace.comap
      (fun ω (p : I × Set.Iic t) => (p.2 : ℝ) * D (X ω) p.1 + C p.1 p.2 ω) inferInstance]
      =ᵐ[P]
    P[f ∘ X | MeasurableSpace.comap
      (fun ω i => (t : ℝ) * D (X ω) i + C i t ω) inferInstance] := by
  by_cases ht : t = 0
  · subst t
    rw [zero_history_comap (fun i r ω => (r : ℝ) * D (X ω) i + C i r ω)]
  · exact condExp_observation_history_eq_endpoint hC hind hCm hXm D hD hXC t ht f hf hfi

end Problem336.BrownianBridge

end

end OAI
