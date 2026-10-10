import OAI.Probability.StrongRayleigh.AsymptoticReadout
import OAI.Probability.StrongRayleigh.UniformSource
import OAI.Probability.StrongRayleigh.BrownianReadout
import OAI.Probability.StrongRayleigh.DecoderUniqueness

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal

namespace Problem336AdditiveD139

theorem hasEquivariantIIDFactor_of_reference_readout
    {Γ : Type u_1} {α : Type u_2} {Ω : Type u_3} [Group Γ] [Countable Γ] [MeasurableSpace Γ]
    [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    [MeasurableSpace Ω]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (μ : ProbabilityMeasure (Γ → Bool)) (ρ : Measure Ω)
    (Z : ℕ → (Γ → α) → Γ → ℝ) (hZ : ∀ n, Measurable (Z n))
    (heq : ∀ n g w, Z n (leftTranslate g w) = leftTranslate g (Z n w))
    (W : Ω → Γ → α) (hW : Measurable W)
    (hWlaw : Measure.map W ρ = Measure.infinitePi (fun _ : Γ => ν))
    (X : Ω → Γ → Bool)
    (hXlaw : Measure.map X ρ = (μ : Measure (Γ → Bool)))
    (hlim : ∀ i, ∀ᵐ ω ∂ρ,
      Tendsto (fun n => Z n (W ω) i) atTop (𝓝 (boolReal (X ω i)))) :
    HasEquivariantIIDFactor μ := by
  apply hasEquivariantIIDFactor_of_standardBorel_sampler ν μ
    (fun w => asymptoticReadout (fun n => Z n w))
  · exact measurable_asymptoticReadout.comp (Measurable.of_eval hZ)
  · intro g w
    have hz : (fun n => Z n (leftTranslate g w)) =
        (fun n => leftTranslate g (Z n w)) := funext (fun n => heq n g w)
    rw [hz, asymptoticReadout_leftTranslate]
  · exact map_asymptoticReadout_of_reference ρ _ _ Z hZ W hW hWlaw X hXlaw hlim

theorem hasEquivariantIIDFactor_of_reference_reconstruction
    {Γ : Type u_4} {α : Type u_5} {Ω : Type u_6} [Group Γ] [Countable Γ] [MeasurableSpace Γ]
    [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    [MeasurableSpace Ω]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (μ : ProbabilityMeasure (Γ → Bool)) (ρ : Measure Ω)
    (Z : ℕ → (Γ → α) → Γ → ℝ) (hZ : ∀ n, Measurable (Z n))
    (heq : ∀ n g w, Z n (leftTranslate g w) = leftTranslate g (Z n w))
    (W : Ω → Γ → α) (hW : Measurable W)
    (hWlaw : Measure.map W ρ = Measure.infinitePi (fun _ : Γ => ν))
    (X : Ω → Γ → Bool)
    (hXlaw : Measure.map X ρ = (μ : Measure (Γ → Bool)))
    (Y : ℕ → Ω → Γ → ℝ)
    (hrec : ∀ n, (fun ω => Z n (W ω)) =ᵐ[ρ] Y n)
    (hlim : ∀ i, ∀ᵐ ω ∂ρ,
      Tendsto (fun n => Y n ω i) atTop (𝓝 (boolReal (X ω i)))) :
    HasEquivariantIIDFactor μ := by
  apply hasEquivariantIIDFactor_of_reference_readout ν μ ρ Z hZ heq
    W hW hWlaw X hXlaw
  intro i
  filter_upwards [ae_all_iff.mpr hrec, hlim i] with ω hrec hlim
  exact hlim.congr (fun n => (congrFun (hrec n) i).symm)

theorem hasEquivariantIIDFactor_of_brownian_decoder
    {Γ : Type u_7} {α : Type u_8} {Ω : Type u_9} [Group Γ] [Countable Γ] [MeasurableSpace Γ]
    [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    [MeasurableSpace Ω]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (μ : ProbabilityMeasure (Γ → Bool)) (P : Measure Ω)
    (b : ℝ → (Γ → ℝ) → Γ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hb : ∀ t, 0 ≤ t → ∀ x i, 0 ≤ b t x i ∧ b t x i ≤ 1)
    (hlip : ∀ t, 0 ≤ t → ∀ x y D, 0 ≤ D →
      (∀ i, |x i - y i| ≤ D) → ∀ i, |b t x i - b t y i| ≤ L * D)
    (w Z : (Γ → α) → ℝ → Γ → ℝ)
    (hZ : ∀ t, Measurable (fun q => Z q t))
    (heq : ∀ t, 0 ≤ t → ∀ g q,
      Z (leftTranslate g q) t = leftTranslate g (Z q t))
    (hZint : ∀ q i t, 0 ≤ t →
      IntervalIntegrable (fun s => b s (Z q s) i) volume 0 t)
    (hZsolve : ∀ q i t, 0 ≤ t →
      Z q t i = w q t i + ∫ s in (0 : ℝ)..t, b s (Z q s) i)
    (W : Ω → Γ → α) (hW : Measurable W)
    (hWlaw : Measure.map W P = Measure.infinitePi (fun _ : Γ => ν))
    (X : Ω → Γ → Bool)
    (hXlaw : Measure.map X P = (μ : Measure (Γ → Bool)))
    (B : Γ → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, ProbabilityTheory.IsPreBrownianReal (B i) P)
    (Y : Ω → ℝ → Γ → ℝ)
    (hYint : ∀ᵐ ω ∂P, ∀ i t, 0 ≤ t →
      IntervalIntegrable (fun s => b s (Y ω s) i) volume 0 t)
    (hYnat : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ i,
      Y ω n i = (n : ℝ) * boolReal (X ω i) + B i n ω)
    (hWrep : ∀ᵐ ω ∂P, ∀ i t, 0 ≤ t →
      w (W ω) t i = Y ω t i - ∫ s in (0 : ℝ)..t, b s (Y ω s) i) :
    HasEquivariantIIDFactor μ := by
  let Znat : ℕ → (Γ → α) → Γ → ℝ := fun n q => Z q n
  have hZnat : ∀ n, Measurable (Znat n) := fun n => hZ n
  apply hasEquivariantIIDFactor_of_standardBorel_sampler ν μ (brownianSlopeReadout Znat)
    (measurable_brownianSlopeReadout Znat hZnat)
  · exact brownianSlopeReadout_leftTranslate Znat
      (fun n g q => heq n (Nat.cast_nonneg n) g q)
  · apply map_brownianSlopeReadout_of_reference P _ _ Znat hZnat
      W hW hWlaw X hXlaw B hB
    intro n
    filter_upwards [hYint, hYnat n, hWrep] with ω hYint hYnat hWrep
    have hrec := Decoder.bounded_drift_decoder_unique b L hL hb hlip
      (fun i t => w (W ω) t i) (fun i t => Z (W ω) t i) (fun i t => Y ω t i)
      (fun i t ht => hZint (W ω) i t ht) hYint
      (fun i t ht => hZsolve (W ω) i t ht)
      (by
        intro i t ht
        rw [hWrep i t ht]
        ring)
    intro i
    exact (hrec i n (Nat.cast_nonneg n)).trans (hYnat i)

end Problem336AdditiveD139

end

end OAI
