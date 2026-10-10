import OAI.Probability.FreeIsing.Brownian.IntegralProperties

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped NNReal Topology

namespace Problem367.BrownianGrid

theorem integralSum_comp {Ω Ω' : Type*} (φ : Ω' → Ω)
    (B : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (H : ℕ → Ω → ℝ) (n : ℕ) :
    integralSum (fun s => B s ∘ φ) t (fun i => H i ∘ φ) n =
      integralSum B t H n ∘ φ := rfl

theorem uniformSum_comp {Ω Ω' : Type*} (φ : Ω' → Ω)
    (B H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) :
    uniformSum (fun s => B s ∘ φ) (fun s => H s ∘ φ) T n =
      uniformSum B H T n ∘ φ := rfl

theorem integral_sq_sub_comp
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {φ : Ω' → Ω}
    (hφ : MeasurePreserving φ Q P) {X I : Ω → ℝ}
    (hX : AEStronglyMeasurable X P) (hI : AEStronglyMeasurable I P) :
    (∫ ω, (X (φ ω) - I (φ ω)) ^ 2 ∂Q) =
      ∫ ω, (X ω - I ω) ^ 2 ∂P := by
  have hm : AEStronglyMeasurable (fun ω => (X ω - I ω) ^ 2) (Q.map φ) := by
    rw [hφ.map_eq]
    exact (hX.sub hI).pow 2
  simpa only [hφ.map_eq] using (integral_map hφ.aemeasurable hm).symm

theorem meanSquare_limit_comp
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {φ : Ω' → Ω}
    (hφ : MeasurePreserving φ Q P) {X : ℕ → Ω → ℝ} {I : Ω → ℝ}
    (hX : ∀ n, AEStronglyMeasurable (X n) P) (hI : AEStronglyMeasurable I P)
    (hlim : Tendsto (fun n => ∫ ω, (X n ω - I ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (X n (φ ω) - I (φ ω)) ^ 2 ∂Q) atTop (𝓝 0) := by
  have heq : (fun n => ∫ ω, (X n (φ ω) - I (φ ω)) ^ 2 ∂Q) =
      (fun n => ∫ ω, (X n ω - I ω) ^ 2 ∂P) :=
    funext (fun n => integral_sq_sub_comp hφ (hX n) hI)
  rw [heq]
  exact hlim

theorem ae_eq_of_meanSquare_limits_comp
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {φ : Ω' → Ω}
    (hφ : MeasurePreserving φ Q P) {X : ℕ → Ω → ℝ}
    {I : Ω → ℝ} {J : Ω' → ℝ}
    (hX : ∀ n, MemLp (X n) 2 P) (hI : MemLp I 2 P) (hJ : MemLp J 2 Q)
    (hlimI : Tendsto (fun n => ∫ ω, (X n ω - I ω) ^ 2 ∂P) atTop (𝓝 0))
    (hlimJ : Tendsto (fun n => ∫ ω, (X n (φ ω) - J ω) ^ 2 ∂Q) atTop (𝓝 0)) :
    I ∘ φ =ᵐ[Q] J := by
  apply ae_eq_of_mean_square_limits (fun n => (hX n).comp_measurePreserving hφ)
    (hI.comp_measurePreserving hφ) hJ
  · exact meanSquare_limit_comp hφ (fun n => (hX n).aestronglyMeasurable)
      hI.aestronglyMeasurable hlimI
  · exact hlimJ

theorem uniformIntegral_eq_comp
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {φ : Ω' → Ω}
    (hφ : MeasurePreserving φ Q P) (B H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    {I : Ω → ℝ} {J : Ω' → ℝ}
    (hX : ∀ n, MemLp (uniformSum B H T n) 2 P)
    (hI : MemLp I 2 P) (hJ : MemLp J 2 Q)
    (hlimI : Tendsto (fun n => ∫ ω, (uniformSum B H T n ω - I ω) ^ 2 ∂P)
      atTop (𝓝 0))
    (hlimJ : Tendsto (fun n => ∫ ω,
      (uniformSum (fun s => B s ∘ φ) (fun s => H s ∘ φ) T n ω - J ω) ^ 2 ∂Q)
      atTop (𝓝 0)) : I ∘ φ =ᵐ[Q] J :=
  ae_eq_of_meanSquare_limits_comp hφ hX hI hJ hlimI hlimJ

theorem ae_eq_process_of_meanSquare_limits_comp
    {Ω Ω' T : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [TopologicalSpace T] [SeparableSpace T] [Nonempty T]
    {P : Measure Ω} {Q : Measure Ω'} {φ : Ω' → Ω}
    (hφ : MeasurePreserving φ Q P) {X : T → ℕ → Ω → ℝ}
    {I : T → Ω → ℝ} {J : T → Ω' → ℝ}
    (hX : ∀ t n, MemLp (X t n) 2 P)
    (hI : ∀ t, MemLp (I t) 2 P) (hJ : ∀ t, MemLp (J t) 2 Q)
    (hcI : ∀ᵐ ω ∂P, Continuous (fun t => I t ω))
    (hcJ : ∀ᵐ ω ∂Q, Continuous (fun t => J t ω))
    (hlimI : ∀ t, Tendsto (fun n => ∫ ω, (X t n ω - I t ω) ^ 2 ∂P)
      atTop (𝓝 0))
    (hlimJ : ∀ t, Tendsto (fun n => ∫ ω, (X t n (φ ω) - J t ω) ^ 2 ∂Q)
      atTop (𝓝 0)) :
    (fun ω t => I t (φ ω)) =ᵐ[Q] (fun ω t => J t ω) := by
  have hcI' : ∀ᵐ ω ∂Q, Continuous (fun t => I t (φ ω)) := by
    apply ae_of_ae_map (p := fun ω => Continuous (fun t => I t ω)) hφ.aemeasurable
    simpa only [hφ.map_eq] using hcI
  apply ae_eq_of_continuous_of_evaluation_ae_eq hcI' hcJ
  intro t
  exact ae_eq_of_meanSquare_limits_comp hφ (hX t) (hI t) (hJ t) (hlimI t) (hlimJ t)

theorem ae_eq_array_of_meanSquare_limits_comp
    {Ω Ω' V T : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [Countable V]
    [TopologicalSpace T] [SeparableSpace T] [Nonempty T]
    {P : Measure Ω} {Q : Measure Ω'} {φ : Ω' → Ω}
    (hφ : MeasurePreserving φ Q P) {X : V → T → ℕ → Ω → ℝ}
    {I : V → T → Ω → ℝ} {J : V → T → Ω' → ℝ}
    (hX : ∀ v t n, MemLp (X v t n) 2 P)
    (hI : ∀ v t, MemLp (I v t) 2 P) (hJ : ∀ v t, MemLp (J v t) 2 Q)
    (hcI : ∀ v, ∀ᵐ ω ∂P, Continuous (fun t => I v t ω))
    (hcJ : ∀ v, ∀ᵐ ω ∂Q, Continuous (fun t => J v t ω))
    (hlimI : ∀ v t, Tendsto (fun n => ∫ ω, (X v t n ω - I v t ω) ^ 2 ∂P)
      atTop (𝓝 0))
    (hlimJ : ∀ v t, Tendsto (fun n => ∫ ω, (X v t n (φ ω) - J v t ω) ^ 2 ∂Q)
      atTop (𝓝 0)) :
    (fun ω v t => I v t (φ ω)) =ᵐ[Q] (fun ω v t => J v t ω) := by
  have hv : ∀ v, (fun ω t => I v t (φ ω)) =ᵐ[Q] (fun ω t => J v t ω) :=
    fun v => ae_eq_process_of_meanSquare_limits_comp hφ (hX v) (hI v) (hJ v)
      (hcI v) (hcJ v) (hlimI v) (hlimJ v)
  filter_upwards [ae_all_iff.mpr hv] with ω hω
  exact funext hω

end Problem367.BrownianGrid

end

end OAI
