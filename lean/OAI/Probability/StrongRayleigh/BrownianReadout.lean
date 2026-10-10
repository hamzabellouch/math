import OAI.Probability.StrongRayleigh.AsymptoticReadout
import OAI.Probability.StrongRayleigh.BrownianSublinear

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem336AdditiveD139

def brownianSlopeReadout {W : Type u_1} {I : Type u_2} (Z : ℕ → W → I → ℝ) (w : W) : I → Bool :=
  asymptoticReadout (fun n i => Z n w i / (n : ℝ))

theorem measurable_brownianSlopeReadout {W : Type u_3} {I : Type u_4} [MeasurableSpace W]
    (Z : ℕ → W → I → ℝ) (hZ : ∀ n, Measurable (Z n)) :
    Measurable (brownianSlopeReadout Z) := by
  apply measurable_asymptoticReadout.comp
  apply Measurable.of_eval
  intro n
  apply Measurable.of_eval
  intro i
  exact ((measurable_pi_apply i).comp (hZ n)).div_const (n : ℝ)

theorem brownianSlopeReadout_leftTranslate {Γ : Type u_5} {α : Type u_6} [Group Γ]
    (Z : ℕ → (Γ → α) → Γ → ℝ)
    (hZ : ∀ n g w, Z n (leftTranslate g w) = leftTranslate g (Z n w))
    (g : Γ) (w : Γ → α) :
    brownianSlopeReadout Z (leftTranslate g w) =
      leftTranslate g (brownianSlopeReadout Z w) := by
  unfold brownianSlopeReadout
  have hfield : (fun n i => Z n (leftTranslate g w) i / (n : ℝ)) =
      (fun n => leftTranslate g (fun i => Z n w i / (n : ℝ))) := by
    funext n i
    rw [hZ]
    rfl
  rw [hfield, asymptoticReadout_leftTranslate]

theorem map_brownianSlopeReadout_of_reference
    {Ω : Type u_7} {W : Type u_8} {I : Type u_9} [MeasurableSpace Ω] [MeasurableSpace W] [Countable I]
    (P : Measure Ω) (ν : Measure W) (μ : Measure (I → Bool))
    (Z : ℕ → W → I → ℝ) (hZ : ∀ n, Measurable (Z n))
    (W₀ : Ω → W) (hW₀ : Measurable W₀) (hWlaw : Measure.map W₀ P = ν)
    (X : Ω → I → Bool) (hXlaw : Measure.map X P = μ)
    (B : I → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hdecode : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ i,
      Z n (W₀ ω) i = (n : ℝ) * boolReal (X ω i) + B i n ω) :
    Measure.map (brownianSlopeReadout Z) ν = μ := by
  apply map_asymptoticReadout_of_reference P ν μ
    (fun n w i => Z n w i / (n : ℝ))
  · intro n
    exact Measurable.of_eval fun i =>
      ((measurable_pi_apply i).comp (hZ n)).div_const (n : ℝ)
  · exact hW₀
  · exact hWlaw
  · exact hXlaw
  · intro i
    filter_upwards [BrownianSublinear.tendsto_nat_observation_slope_all_ae B
      (fun i ω => boolReal (X ω i)) hB, ae_all_iff.mpr hdecode] with ω hlim heq
    simpa only [heq] using hlim i

end Problem336AdditiveD139

end

end OAI
