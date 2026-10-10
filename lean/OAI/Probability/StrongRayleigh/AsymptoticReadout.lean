import OAI.Probability.StrongRayleigh.Model

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem336AdditiveD139

def binaryReadout (z : ℕ → ℝ) : Bool := by
  classical
  exact if ∀ N : ℕ, ∃ n : ℕ, (1 : ℝ) / 2 < z (N + n) then true else false

def asymptoticReadout {I : Type u_1} (z : ℕ → I → ℝ) : I → Bool :=
  fun i => binaryReadout (fun n => z n i)

theorem measurable_binaryReadout : Measurable binaryReadout := by
  classical
  have hp : MeasurableSet {z : ℕ → ℝ | ∀ N : ℕ, ∃ n : ℕ,
      (1 : ℝ) / 2 < z (N + n)} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n =>
      measurableSet_lt measurable_const (measurable_pi_apply (N + n))
  exact Measurable.ite hp measurable_const measurable_const

theorem binaryReadout_eq_of_tendsto {z : ℕ → ℝ} {b : Bool}
    (h : Tendsto z atTop (𝓝 (boolReal b))) : binaryReadout z = b := by
  classical
  cases b with
  | false =>
    have hz : Tendsto z atTop (𝓝 (0 : ℝ)) := by simpa [boolReal] using h
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp hz).2 (1 / 2) (by norm_num))
    have hp : ¬ (∀ N : ℕ, ∃ n : ℕ, (1 : ℝ) / 2 < z (N + n)) := by
      intro hp
      obtain ⟨n, hn⟩ := hp N
      have hh := hN (N + n) (Nat.le_add_right N n)
      linarith
    simp only [binaryReadout, ite_eq_right hp]
  | true =>
    have hz : Tendsto z atTop (𝓝 (1 : ℝ)) := by simpa [boolReal] using h
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp hz).1 (1 / 2) (by norm_num))
    have hp : ∀ M : ℕ, ∃ n : ℕ, (1 : ℝ) / 2 < z (M + n) := by
      intro M
      exact ⟨N, hN (M + N) (Nat.le_add_left N M)⟩
    simp only [binaryReadout, ite_eq_left hp]

theorem measurable_asymptoticReadout {I : Type u_2} :
    Measurable (@asymptoticReadout I) := by
  apply Measurable.of_eval
  intro i
  exact measurable_binaryReadout.comp
    (Measurable.of_eval fun n => (measurable_pi_apply i).comp (measurable_pi_apply n))

theorem asymptoticReadout_eq_of_tendsto {I : Type u_3} {z : ℕ → I → ℝ}
    {x : I → Bool} (h : ∀ i, Tendsto (fun n => z n i) atTop (𝓝 (boolReal (x i)))) :
    asymptoticReadout z = x := by
  funext i
  exact binaryReadout_eq_of_tendsto (h i)

theorem asymptoticReadout_leftTranslate {Γ : Type u_4} [Group Γ]
    (g : Γ) (z : ℕ → Γ → ℝ) :
    asymptoticReadout (fun n => leftTranslate g (z n)) =
      leftTranslate g (asymptoticReadout z) := rfl

theorem asymptoticReadout_ae_eq {Ω : Type u_5} {I : Type u_6} [MeasurableSpace Ω] [Countable I]
    (ρ : Measure Ω) (Z : ℕ → Ω → I → ℝ) (X : Ω → I → Bool)
    (h : ∀ i, ∀ᵐ ω ∂ρ, Tendsto (fun n => Z n ω i) atTop (𝓝 (boolReal (X ω i)))) :
    (fun ω => asymptoticReadout (fun n => Z n ω)) =ᵐ[ρ] X := by
  filter_upwards [ae_all_iff.mpr h] with ω hω
  exact asymptoticReadout_eq_of_tendsto hω

theorem map_asymptoticReadout_of_reference
    {Ω : Type u_7} {W : Type u_8} {I : Type u_9} [MeasurableSpace Ω] [MeasurableSpace W] [Countable I]
    (ρ : Measure Ω) (ν : Measure W) (μ : Measure (I → Bool))
    (Z : ℕ → W → I → ℝ) (hZ : ∀ n, Measurable (Z n))
    (W₀ : Ω → W) (hW₀ : Measurable W₀) (hWlaw : Measure.map W₀ ρ = ν)
    (X : Ω → I → Bool) (hXlaw : Measure.map X ρ = μ)
    (hlim : ∀ i, ∀ᵐ ω ∂ρ,
      Tendsto (fun n => Z n (W₀ ω) i) atTop (𝓝 (boolReal (X ω i)))) :
    Measure.map (fun w => asymptoticReadout (fun n => Z n w)) ν = μ := by
  have hreadout : Measurable (fun w => asymptoticReadout (fun n => Z n w)) :=
    measurable_asymptoticReadout.comp (Measurable.of_eval hZ)
  rw [← hWlaw, Measure.map_map hreadout hW₀]
  exact (Measure.map_congr
    (asymptoticReadout_ae_eq ρ (fun n ω => Z n (W₀ ω)) X hlim)).trans hXlaw

theorem hasEquivariantIIDFactor_of_asymptotic_observations
    {Γ : Type u_10} [Group Γ] [Countable Γ] [MeasurableSpace Γ]
    (μ : ProbabilityMeasure (Γ → Bool))
    (Z : ℕ → (Γ → UnitLabel) → Γ → ℝ)
    (hZ : ∀ n, Measurable (Z n))
    (heq : ∀ n g u, Z n (leftTranslate g u) = leftTranslate g (Z n u))
    (X : (Γ → UnitLabel) → Γ → Bool)
    (hX : Measure.map X (iidUnitLabels Γ) = (μ : Measure (Γ → Bool)))
    (hlim : ∀ i, ∀ᵐ u ∂iidUnitLabels Γ,
      Tendsto (fun n => Z n u i) atTop (𝓝 (boolReal (X u i)))) :
    HasEquivariantIIDFactor μ := by
  refine ⟨fun u => asymptoticReadout (fun n => Z n u), ?_, ?_, ?_⟩
  · exact measurable_asymptoticReadout.comp (Measurable.of_eval hZ)
  · intro g u
    have hfields : (fun n => Z n (leftTranslate g u)) =
        (fun n => leftTranslate g (Z n u)) := funext (fun n => heq n g u)
    change asymptoticReadout (fun n => Z n (leftTranslate g u)) = _
    rw [hfields, asymptoticReadout_leftTranslate]
  · exact (Measure.map_congr (asymptoticReadout_ae_eq (iidUnitLabels Γ) Z X hlim)).trans hX

end Problem336AdditiveD139

end

end OAI
