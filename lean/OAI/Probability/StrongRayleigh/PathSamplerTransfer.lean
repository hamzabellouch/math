import OAI.Probability.StrongRayleigh.IIDAction
import OAI.Probability.StrongRayleigh.AsymptoticReadout
import OAI.Probability.StrongRayleigh.BrownianSublinear

namespace OAI

universe u_1 u_2 u_3

noncomputable section

open MeasureTheory Filter
open scoped NNReal Topology

namespace Problem336AdditiveD139.PathSamplerTransfer

variable {Γ : Type u_1} [Group Γ] [Countable Γ] [MeasurableSpace Γ]
variable [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)]

def decoderSlopes (Z : (Γ → C(ℝ≥0, ℝ)) → Γ → C(ℝ≥0, ℝ))
    (n : ℕ) (w : Γ → C(ℝ≥0, ℝ)) (i : Γ) : ℝ :=
  Z w i (n + 1 : ℝ≥0) / ((n : ℝ) + 1)

omit [Group Γ] [Countable Γ] [MeasurableSpace Γ] in
lemma measurable_decoderSlopes
    {Z : (Γ → C(ℝ≥0, ℝ)) → Γ → C(ℝ≥0, ℝ)}
    (hZ : Measurable Z) (n : ℕ) : Measurable (decoderSlopes Z n) := by
  apply Measurable.of_eval
  intro i
  exact (((continuous_eval_const (n + 1 : ℝ≥0)).measurable.comp
    (measurable_pi_apply i)).comp hZ).div_const _

omit [Countable Γ] [MeasurableSpace Γ] [MeasurableSpace C(ℝ≥0, ℝ)]
    [BorelSpace C(ℝ≥0, ℝ)] in
lemma decoderSlopes_equivariant
    {Z : (Γ → C(ℝ≥0, ℝ)) → Γ → C(ℝ≥0, ℝ)}
    (heq : ∀ g w, Z (leftTranslate g w) = leftTranslate g (Z w))
    (n : ℕ) (g : Γ) (w : Γ → C(ℝ≥0, ℝ)) :
    decoderSlopes Z n (leftTranslate g w) = leftTranslate g (decoderSlopes Z n w) := by
  funext i
  simp only [decoderSlopes, heq, leftTranslate]

theorem factor_of_reference_decoder
    {Ω : Type u_2} [MeasurableSpace Ω]
    (P : Measure Ω) (ρ : Measure C(ℝ≥0, ℝ)) [IsProbabilityMeasure ρ]
    (μ : ProbabilityMeasure (Γ → Bool))
    (Z : (Γ → C(ℝ≥0, ℝ)) → Γ → C(ℝ≥0, ℝ))
    (hZ : Measurable Z)
    (heq : ∀ g w, Z (leftTranslate g w) = leftTranslate g (Z w))
    (W : Ω → Γ → C(ℝ≥0, ℝ)) (hW : Measurable W)
    (hWlaw : P.map W = Measure.infinitePi (fun _ : Γ => ρ))
    (X : Ω → Γ → Bool) (hXlaw : P.map X = (μ : Measure (Γ → Bool)))
    (B : Ω → Γ → ℝ≥0 → ℝ)
    (hdecode : ∀ i, ∀ᵐ ω ∂P, ∀ n : ℕ,
      Z (W ω) i (n + 1 : ℝ≥0) =
        ((n : ℝ) + 1) * boolReal (X ω i) + B ω i (n + 1 : ℝ≥0))
    (hnoise : ∀ i, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => B ω i (n + 1 : ℝ≥0) / ((n : ℝ) + 1))
        atTop (𝓝 0)) :
    HasEquivariantIIDFactor μ := by
  let Ψ : (Γ → C(ℝ≥0, ℝ)) → Γ → Bool :=
    fun w => asymptoticReadout (fun n => decoderSlopes Z n w)
  have hΨ : Measurable Ψ :=
    measurable_asymptoticReadout.comp
      (Measurable.of_eval (measurable_decoderSlopes hZ))
  have hΨeq : ∀ g w, Ψ (leftTranslate g w) = leftTranslate g (Ψ w) := by
    intro g w
    change asymptoticReadout (fun n => decoderSlopes Z n (leftTranslate g w)) = _
    simp_rw [decoderSlopes_equivariant heq]
    exact asymptoticReadout_leftTranslate g _
  apply IIDAction.factor_of_standardBorel_decoder ρ μ Ψ hΨ hΨeq
  apply map_asymptoticReadout_of_reference P _ _ (decoderSlopes Z)
    (measurable_decoderSlopes hZ) W hW hWlaw X hXlaw
  intro i
  filter_upwards [hdecode i, hnoise i] with ω hdec hlim
  have hformula : (fun n => decoderSlopes Z n (W ω) i) =
      (fun n : ℕ => boolReal (X ω i) + B ω i (n + 1 : ℝ≥0) / ((n : ℝ) + 1)) := by
    funext n
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    simp only [decoderSlopes, hdec n, add_div, mul_div_cancel_left₀ _ hn]
  rw [hformula]
  simpa only [add_zero] using tendsto_const_nhds.add hlim

theorem factor_of_brownian_reference_decoder
    {Ω : Type u_3} [MeasurableSpace Ω]
    (P : Measure Ω) (ρ : Measure C(ℝ≥0, ℝ)) [IsProbabilityMeasure ρ]
    (μ : ProbabilityMeasure (Γ → Bool))
    (Z : (Γ → C(ℝ≥0, ℝ)) → Γ → C(ℝ≥0, ℝ))
    (hZ : Measurable Z)
    (heq : ∀ g w, Z (leftTranslate g w) = leftTranslate g (Z w))
    (W : Ω → Γ → C(ℝ≥0, ℝ)) (hW : Measurable W)
    (hWlaw : P.map W = Measure.infinitePi (fun _ : Γ => ρ))
    (X : Ω → Γ → Bool) (hXlaw : P.map X = (μ : Measure (Γ → Bool)))
    (B : Ω → Γ → ℝ≥0 → ℝ)
    (hdecode : ∀ i, ∀ᵐ ω ∂P, ∀ n : ℕ,
      Z (W ω) i (n + 1 : ℝ≥0) =
        ((n : ℝ) + 1) * boolReal (X ω i) + B ω i (n + 1 : ℝ≥0))
    (hB : ∀ i, ProbabilityTheory.IsPreBrownianReal (fun t ω => B ω i t) P) :
    HasEquivariantIIDFactor μ := by
  apply factor_of_reference_decoder P ρ μ Z hZ heq W hW hWlaw X hXlaw B hdecode
  intro i
  filter_upwards [BrownianSublinear.tendsto_nat_div_ae (hB i)] with ω hω
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
    hω.comp (tendsto_add_atTop_nat 1)

end Problem336AdditiveD139.PathSamplerTransfer

end

end OAI
