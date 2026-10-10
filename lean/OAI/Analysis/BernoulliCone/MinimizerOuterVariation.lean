import OAI.Analysis.BernoulliCone.MinimizerStationarity

namespace OAI

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ENNReal ContDiff
namespace Bernoulli
open scoped _root_.Bernoulli
variable {d : ℕ} {D : Set (Space d)}

/-- Multiplicative variations preserve the positivity set exactly. -/
lemma outerVariation_of_comparison [IsFiniteMeasure (volume.restrict D)]
    {u : Space d → ℝ} {G : Space d → Space d}
    (hD : IsOpen D) (hu : H1 D u G)
    (hn : ∀ᵐ x ∂volume.restrict D, 0 ≤ u x)
    (hmin : ∀ (v : Space d → ℝ) (V : Space d → Space d),
      H1 D v V → (∀ᵐ x ∂volume.restrict D, 0 ≤ v x) →
      H10 D (fun x => v x-u x) (fun x => V x-G x) →
      energy D u G ≤ energy D v V)
    {φ : Space d → ℝ} (hφ : Test D φ) :
    (∫ x in D, inner ℝ (G x) (φ x • G x+u x • gradient φ x)) = 0 := by
  let V : Space d → Space d := fun x => φ x • G x+u x • gradient φ x
  have hp : H10 D (fun x => φ x*u x) V := SobolevDensity.h10_mul_test hu hD hφ
  obtain ⟨C,hC⟩ := (hφ.1.continuous.norm.bddAbove_range_of_hasCompactSupport hφ.2.1.norm)
  have hCB : ∀ x, |φ x| ≤ |C|+1 := by
    intro x
    have hx := hC (mem_range_self x)
    change ‖φ x‖ ≤ C at hx
    rw [Real.norm_eq_abs] at hx
    linarith [le_abs_self C]
  have hCpos : 0 < |C|+1 := by positivity
  apply linear_coefficient_eq_zero _ (∫ x in D, ‖V x‖^2) (div_pos (by norm_num : (0:ℝ)<1) hCpos)
  intro t ht
  have hs : |t| *(|C|+1)<1 := (lt_div_iff₀ hCpos).mp ht
  have hf (x : Space d) : 0 < 1+t*φ x := by
    have hb : |t*φ x|<1 := by
      rw [abs_mul]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hCB x) (abs_nonneg t)) hs
    linarith [neg_abs_le (t*φ x)]
  have he (x : Space d) : u x+t*(φ x*u x)=(1+t*φ x)*u x := by ring
  have hcontrol : ∀ᵐ x ∂volume.restrict D,
      0 ≤ u x+t*(φ x*u x) ∧ ((0 < u x+t*(φ x*u x)) ↔ 0 < u x) := by
    filter_upwards [hn] with x hx
    rw [he]
    exact ⟨mul_nonneg (hf x).le hx, mul_pos_iff_of_pos_left (hf x)⟩
  have hc := hmin (fun x => u x+t*(φ x*u x)) (fun x => G x+t • V x)
    (hu.add (hp.1.const_smul t)) (hcontrol.mono fun _ hx => hx.1)
    (by simpa only [add_sub_cancel_left] using hp.const_smul t)
  rw [energy_affine hu.1 hu.2.1 hp.1.2.1 t (hcontrol.mono fun _ hx => hx.2)] at hc
  linarith

lemma GlobalMinimizer.outerVariation {u : Space d → ℝ} {L : ℝ≥0}
    (hm : GlobalMinimizer u) (huLip : LipschitzWith L u)
    {a : Space d} {R : ℝ} (hR : 0 < R)
    {φ : Space d → ℝ} (hφ : Test (ball a R) φ) :
    (∫ x in ball a R, inner ℝ (gradient u x)
      (φ x • gradient u x+u x • gradient φ x)) = 0 := by
  let : IsFiniteMeasure (volume.restrict (ball a R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  obtain ⟨_,G,hG,hn,hmin⟩ := hm
  have hu := hG a R hR (subset_univ _)
  have he := hu.gradient_unique isOpen_ball (LipschitzSobolev.h1_ball huLip a R)
  have hh := outerVariation_of_comparison isOpen_ball hu
    (ae_restrict_of_ae (by simpa only [Measure.restrict_univ] using hn))
    (hmin a R hR (subset_univ _)) hφ
  rw [← hh]
  apply integral_congr_ae
  filter_upwards [he] with x hx
  rw [hx]
end Bernoulli

end
end

end OAI
