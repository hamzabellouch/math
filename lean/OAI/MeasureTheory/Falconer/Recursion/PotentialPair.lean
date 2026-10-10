import OAI.MeasureTheory.Falconer.Recursion.PotentialFrostman

namespace OAI

/-! # Localized pair potentials at the original finite resolution -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

theorem regularized_pair_potential (μ : Measure X) [SFinite μ]
    {K s q : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hsq : s < q) (g N : ℕ) (hg : g ≤ N)
    (hmass : μ univ ≤ 1)
    (hball : ∀ x : X, ∀ n : ℕ, n ≤ N →
      μ (ball x (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q)) :
    (∫⁻ z in {z : X × X | dist z.1 z.2 < 1/(2:ℝ)^g},
      ENNReal.ofReal ((1/(dist z.1 z.2+1/(2:ℝ)^N))^s) ∂μ.prod μ) ≤
      ENNReal.ofReal (K*(((2:ℝ)^g)^(s-q))*(1+(2:ℝ)^s/(1-(2:ℝ)^(s-q)))) := by
  let D : Set (X × X) := {z | dist z.1 z.2 < 1/(2:ℝ)^g}
  let f : X × X → ℝ≥0∞ := fun z => ENNReal.ofReal ((1/(dist z.1 z.2+1/(2:ℝ)^N))^s)
  let B := ENNReal.ofReal (K*(((2:ℝ)^g)^(s-q))*(1+(2:ℝ)^s/(1-(2:ℝ)^(s-q))))
  have hD : MeasurableSet D := measurableSet_lt (by fun_prop) measurable_const
  have hp (x : X) : (∫⁻ y in ball x (1/(2:ℝ)^g), f (x,y) ∂μ) ≤ B := by
    have hh := regularized_potential_frostman μ x hK hs hsq g (N-g) (by
      intro n hn
      exact hball x n (by omega))
    simpa only [Nat.add_sub_of_le hg,f,B] using hh
  rw [← lintegral_indicator hD,
    lintegral_prod _ (((by fun_prop : Measurable f).indicator hD).aemeasurable)]
  calc
    _ = ∫⁻ x, ∫⁻ y in ball x (1/(2:ℝ)^g), f (x,y) ∂μ ∂μ := by
      apply lintegral_congr
      intro x
      rw [← lintegral_indicator measurableSet_ball]
      apply lintegral_congr
      intro y
      by_cases hy : dist x y < 1/(2:ℝ)^g
      · have hb : y ∈ ball x (1/(2:ℝ)^g) := by simpa only [mem_ball,dist_comm] using hy
        rw [indicator_of_mem (show (x,y) ∈ D from hy),indicator_of_mem hb]
      · have hb : y ∉ ball x (1/(2:ℝ)^g) := by simpa only [mem_ball,dist_comm] using hy
        rw [indicator_of_notMem (show (x,y) ∉ D from hy),indicator_of_notMem hb]
    _ ≤ ∫⁻ _ : X, B ∂μ := lintegral_mono hp
    _ = B*μ univ := lintegral_const _
    _ ≤ B*1 := mul_le_mul_right hmass B
    _ = _ := mul_one _

end Falconer

end OAI
