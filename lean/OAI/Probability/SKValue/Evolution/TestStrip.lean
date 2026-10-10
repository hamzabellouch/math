import Mathlib
import OAI.Probability.SKValue.Evolution.EvolveStrips
import OAI.Probability.SKValue.Equations.TestGenerator
import OAI.Probability.SKValue.Evolution.TestEvolution

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue
lemma LinearEvolution.jet_joint {T:ℝ} {γ:ℝ → ℝ} {A V:ℝ → ℝ → ℝ}
    (h:LinearEvolution T γ A V) (n:ℕ) : ∃ L:ℝ,0≤L ∧
    ∀ s∈Icc (0:ℝ) T,∀ t∈Icc (0:ℝ) T,∀ x y,
      |iteratedDeriv n (V s) y-iteratedDeriv n (V t) x|≤L*(|s-t|+|y-x|) := by
  obtain ⟨C,hC,hc⟩ := h.temporal n
  obtain ⟨D,hD,hd⟩ := h.bound (n+1)
  refine ⟨C+D,add_nonneg hC hD,?_⟩
  intro s hs t ht x y
  have hdiff := (h.slices t ht).smooth.differentiable_iteratedDeriv n
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)
  have hl:LipschitzWith ⟨D,hD⟩ (iteratedDeriv n (V t)) := by
    apply lipschitzWith_of_nnnorm_deriv_le hdiff
    intro z
    have hz := hd t ht z
    rw [iteratedDeriv_succ] at hz
    exact_mod_cast hz
  have hx := hl.dist_le_mul y x
  change |iteratedDeriv n (V t) y-iteratedDeriv n (V t) x|≤D*|y-x| at hx
  have hh := abs_sub_le (iteratedDeriv n (V s) y) (iteratedDeriv n (V t) y) (iteratedDeriv n (V t) x)
  have ht := hc s hs t ht y
  nlinarith [mul_nonneg hC (abs_nonneg (y-x)),mul_nonneg hD (abs_nonneg (s-t))]

lemma LinearEvolution.toBackwardTest {T:ℝ} (hT:0≤T) {γ:ℝ → ℝ} {A V:ℝ → ℝ → ℝ}
    (h:LinearEvolution T γ A V) (hA:SmoothEvolution T γ A)
    (hγ:∀ t∈Icc (0:ℝ) T,0≤γ t) (hmono:MonotoneOn γ (Icc (0:ℝ) T)) :
    ∃ K L,BackwardTest T γ (fun t ↦ deriv (A t)) V K L := by
  obtain ⟨B0,hB0,hb0⟩ := h.bound 0
  obtain ⟨B1,hB1,hb1⟩ := h.bound 1
  obtain ⟨B2,hB2,hb2⟩ := h.bound 2
  obtain ⟨B3,hB3,hb3⟩ := h.bound 3
  obtain ⟨L1,hL1,hl1⟩ := h.jet_joint 1
  obtain ⟨L2,hL2,hl2⟩ := h.jet_joint 2
  obtain ⟨LA,hLA,hlA⟩ := hA.jet_joint 0
  let K := B0+B1+B2+B3
  let L := L2+L1+B1*LA
  have hK:0≤K := by dsimp [K];positivity
  have hL:0≤L := by dsimp [L];positivity
  have hgi:IntervalIntegrable γ volume 0 T := by
    apply MonotoneOn.intervalIntegrable
    simpa only [uIcc_of_le hT] using hmono
  have hc1 (x:ℝ) : ContinuousOn (fun t ↦ deriv (V t) x) (Icc (0:ℝ) T) := by
    simpa only [iteratedDeriv_one] using h.continuous_jet 1 x
  have hc2 (x:ℝ) : ContinuousOn (fun t ↦ deriv (deriv (V t)) x) (Icc (0:ℝ) T) := by
    simpa only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using h.continuous_jet 2 x
  have hcA (x:ℝ) : ContinuousOn (fun t ↦ deriv (A t) x) (Icc (0:ℝ) T) := by
    simpa only [iteratedDeriv_zero] using hA.continuous_jet 0 x
  refine ⟨K,L,hK,hL,hγ,hmono,?_,fun t ht x ↦ hA.deriv_bound ht x,?_,?_,?_,?_,?_,?_,?_,?_,?_,h.pde⟩
  · intro t ht
    exact (hA.slices t ht).jets.smooth.continuous.measurable
  · intro t ht
    exact (h.slices t ht).smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  · intro t ht x
    have hb := hb0 t ht x
    simp only [iteratedDeriv_zero] at hb
    dsimp [K];linarith
  · intro t ht x
    have hb := hb1 t ht x
    simp only [iteratedDeriv_one] at hb
    dsimp [K];linarith
  · intro t ht x
    have hb := hb2 t ht x
    simp only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero] at hb
    dsimp [K];linarith
  · intro t ht x
    have hb := hb3 t ht x
    dsimp [K];linarith
  · intro t ht s hs x y
    have hb := hl2 s hs t ht x y
    simp only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero] at hb
    dsimp [L]
    nlinarith [mul_nonneg (add_nonneg hL1 (mul_nonneg hB1 hLA)) (add_nonneg (abs_nonneg (s-t)) (abs_nonneg (y-x)))]
  · intro t ht s hs x y
    have hf := hlA s hs t ht x y
    have hg := hl1 s hs t ht x y
    have hd := hb1 t ht x
    simp only [iteratedDeriv_zero] at hf
    simp only [iteratedDeriv_one] at hg hd
    have hb := bounded_product_difference (hA.deriv_bound hs y) hd hf hg (by norm_num) hB1
    dsimp [L]
    nlinarith [mul_nonneg hL2 (add_nonneg (abs_nonneg (s-t)) (abs_nonneg (y-x)))]
  · intro x
    exact ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le hT] using hc2 x)
  · intro x
    have hc := (hcA x).mul (hc1 x)
    change ContinuousOn (fun t ↦ deriv (A t) x * deriv (V t) x) (Icc 0 T) at hc
    exact hgi.mul_continuousOn (by rwa [uIcc_of_le hT])
end SKValue

end

end OAI
