import OAI.Probability.StrongRayleigh.InnovationInverse
import OAI.Probability.StrongRayleigh.PathSamplerTransfer
import OAI.Probability.StrongRayleigh.BrownianSublinear

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology

namespace Problem336AdditiveD139.PathRealization

local instance : MeasurableSpace Path := borel Path
local instance : BorelSpace Path := ⟨rfl⟩

theorem factor_of_reference_innovation
    {Γ : Type u_1} [Group Γ] [Countable Γ] [MeasurableSpace Γ]
    {Ω : Type u_2} [MeasurableSpace Ω]
    (P : Measure Ω) (ρ : Measure Path) [IsProbabilityMeasure ρ]
    (μ : ProbabilityMeasure (Γ → Bool))
    {b : (ℝ≥0 × (Γ → ℝ)) → Γ → ℝ} (hb : Measurable b)
    (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C)
    (hunit : ∀ p i, 0 ≤ b p i ∧ b p i ≤ 1)
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ t x y D, 0 ≤ D → (∀ i, |x i - y i| ≤ D) →
      ∀ i, |b (t, x) i - b (t, y) i| ≤ L * D)
    (hequiv : ∀ (g : Γ) t x i,
      b (t, leftTranslate g x) i = b (t, x) (g⁻¹ * i))
    (Y : Ω → Γ → Path) (hY : Measurable Y)
    (hinnovation : P.map (fun ω => innovation b hb C hbound (Y ω)) =
      Measure.infinitePi (fun _ : Γ => ρ))
    (X : Ω → Γ → Bool) (hXlaw : P.map X = (μ : Measure (Γ → Bool)))
    (B : Ω → Γ → ℝ≥0 → ℝ)
    (hobs : ∀ ω i t, Y ω i t = (t : ℝ) * boolReal (X ω i) + B ω i t)
    (hnoise : ∀ i, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => B ω i (n + 1 : ℝ≥0) / ((n : ℝ) + 1))
        atTop (𝓝 0)) :
    HasEquivariantIIDFactor μ := by
  obtain ⟨Z, hZ, hZeq, hleft⟩ := exists_equivariant_innovation_leftInverse
    hb C hbound hunit L hL hlip hequiv
  apply PathSamplerTransfer.factor_of_reference_decoder P ρ μ Z hZ hZeq
    (fun ω => innovation b hb C hbound (Y ω))
    ((measurable_innovation hb C hbound).comp hY) hinnovation X hXlaw B
  · intro i
    filter_upwards [] with ω
    intro n
    rw [hleft (Y ω)]
    simpa using hobs ω i (n + 1 : ℝ≥0)
  · exact hnoise

theorem factor_of_brownian_reference_innovation
    {Γ : Type u_3} [Group Γ] [Countable Γ] [MeasurableSpace Γ]
    {Ω : Type u_4} [MeasurableSpace Ω]
    (P : Measure Ω) (ρ : Measure Path) [IsProbabilityMeasure ρ]
    (μ : ProbabilityMeasure (Γ → Bool))
    {b : (ℝ≥0 × (Γ → ℝ)) → Γ → ℝ} (hb : Measurable b)
    (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C)
    (hunit : ∀ p i, 0 ≤ b p i ∧ b p i ≤ 1)
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ t x y D, 0 ≤ D → (∀ i, |x i - y i| ≤ D) →
      ∀ i, |b (t, x) i - b (t, y) i| ≤ L * D)
    (hequiv : ∀ (g : Γ) t x i,
      b (t, leftTranslate g x) i = b (t, x) (g⁻¹ * i))
    (Y : Ω → Γ → Path) (hY : Measurable Y)
    (hinnovation : P.map (fun ω => innovation b hb C hbound (Y ω)) =
      Measure.infinitePi (fun _ : Γ => ρ))
    (X : Ω → Γ → Bool) (hXlaw : P.map X = (μ : Measure (Γ → Bool)))
    (B : Ω → Γ → ℝ≥0 → ℝ)
    (hobs : ∀ ω i t, Y ω i t = (t : ℝ) * boolReal (X ω i) + B ω i t)
    (hBrownian : ∀ i, ProbabilityTheory.IsPreBrownianReal (fun t ω => B ω i t) P) :
    HasEquivariantIIDFactor μ := by
  apply factor_of_reference_innovation P ρ μ hb C hbound hunit L hL hlip
    hequiv Y hY hinnovation X hXlaw B hobs
  intro i
  filter_upwards [BrownianSublinear.tendsto_nat_div_ae (hBrownian i)] with ω hω
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
    hω.comp (Filter.tendsto_add_atTop_nat 1)

end Problem336AdditiveD139.PathRealization

end

end OAI
