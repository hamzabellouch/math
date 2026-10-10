import OAI.Probability.InvariantIsing.Fields.FieldConstantPrefix
import OAI.Probability.InvariantIsing.Fields.FieldEvenTransition

namespace OAI

/-! Evenness and radial antitonicity of a backward covariance derivative
are preserved by each unchanged earlier Gaussian transition. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma field_gaussianTiltAverage_even (s ζ : ℝ) {F A : ℝ → ℝ}
    (hF : Measurable F) (hFe : Function.Even F)
    (hA : Measurable A) (hAe : Function.Even A) :
    Function.Even (gaussianTiltAverage s ζ F A) := by
  rw [field_gaussianTiltAverage_eq_transition s ζ hF hA]
  exact fieldSpinTransition_even ζ (Real.toNNReal s) hF hFe hA hAe

lemma field_gaussianTiltAverage_even_monotone (s ζ : ℝ) {F A : ℝ → ℝ}
    (hF : Measurable F) (hFe : Function.Even F) (hFg : HasLinearGrowth F)
    (hA : Measurable A) (hAe : Function.Even A) (hAm : MonotoneOn A (Ici 0))
    {K : ℝ} (hAb : ∀ y, |A y| ≤ K) :
    MonotoneOn (gaussianTiltAverage s ζ F A) (Ici 0) := by
  rw [field_gaussianTiltAverage_eq_transition s ζ hF hA]
  exact fieldSpinTransition_even_monotone ζ (Real.toNNReal s) hF hFe hFg hA hAe hAm hAb

lemma field_gaussianTiltAverage_even_antitone (s ζ : ℝ) {F A : ℝ → ℝ}
    (hF : Measurable F) (hFe : Function.Even F) (hFg : HasLinearGrowth F)
    (hA : Measurable A) (hAe : Function.Even A) (hAm : AntitoneOn A (Ici 0))
    {K : ℝ} (hAb : ∀ y, |A y| ≤ K) :
    AntitoneOn (gaussianTiltAverage s ζ F A) (Ici 0) := by
  have hm : Measurable (fun y => -A y) := hA.neg
  have he : Function.Even (fun y => -A y) := fun y => by
    dsimp only
    rw [hAe y]
  have hb : ∀ y, |-A y| ≤ K := fun y => by simpa only [abs_neg] using hAb y
  have hn : MonotoneOn (fun y => -A y) (Ici 0) :=
    fun _ hx _ hy hxy => neg_le_neg (hAm hx hy hxy)
  have h := field_gaussianTiltAverage_even_monotone s ζ hF hFe hFg hm he hn hb
  have hneg (z : ℝ) : gaussianTiltAverage s ζ F (fun y => -A y) z =
      -gaussianTiltAverage s ζ F A z := by
    simpa only [neg_one_mul] using field_gaussianTiltAverage_const_mul s ζ hF hA (-1) z
  intro x hx y hy hxy
  have hh := h hx hy hxy
  rw [hneg, hneg] at hh
  exact neg_le_neg_iff.mp hh

lemma field_negative_square_average_shape (s ζ k : ℝ) (hk : 0 ≤ k)
    {F X : ℝ → ℝ} (hF : Measurable F) (hFe : Function.Even F)
    (hFg : HasLinearGrowth F) (hX : Measurable X) (hXo : Function.Odd X)
    (hXm : MonotoneOn X (Ici 0)) (hXp : ∀ y ∈ Ici (0 : ℝ), 0 ≤ X y)
    {K : ℝ} (hXb : ∀ y, |X y| ≤ K) :
    Function.Even (fun z => -k * gaussianTiltAverage s ζ F (fun y => (X y) ^ 2) z) ∧
      AntitoneOn (fun z => -k * gaussianTiltAverage s ζ F (fun y => (X y) ^ 2) z) (Ici 0) := by
  have he : Function.Even (fun y => (X y) ^ 2) := by
    intro y
    dsimp only
    rw [hXo y, neg_sq]
  have hm : MonotoneOn (fun y => (X y) ^ 2) (Ici 0) := by
    intro x hx y hy hxy
    exact pow_le_pow_left₀ (hXp x hx) (hXm hx hy hxy) 2
  have hb : ∀ y, |(X y) ^ 2| ≤ K ^ 2 := fun y => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hXb y) 2
  have hJ := field_gaussianTiltAverage_even s ζ hF hFe (hX.pow_const 2) he
  have hJm := field_gaussianTiltAverage_even_monotone s ζ hF hFe hFg
    (hX.pow_const 2) he hm hb
  refine ⟨fun z => by dsimp only; rw [hJ z], ?_⟩
  intro x hx y hy hxy
  exact mul_le_mul_of_nonpos_left (hJm hx hy hxy) (neg_nonpos.mpr hk)

namespace FieldSmoothFamily

theorem zero_slope_tangent_shape {I : Set ℝ} (F : FieldSmoothFamily I)
    (a ζ t : ℝ) (ht : t ∈ I)
    (hUe : Function.Even (fun z => F.U (t, z)))
    (hTe : Function.Even (fun z => F.T (t, z)))
    (hTa : AntitoneOn (fun z => F.T (t, z)) (Ici 0)) :
    Function.Even (fun z => F.tangent a 0 ζ (t, z)) ∧
      AntitoneOn (fun z => F.tangent a 0 ζ (t, z)) (Ici 0) := by
  have hU : Measurable (fun z => F.U (t, z)) := F.mU.comp (by fun_prop)
  have hT : Measurable (fun z => F.T (t, z)) := F.mT.comp (by fun_prop)
  simp only [tangent, zero_mul, zero_div, add_zero]
  exact ⟨field_gaussianTiltAverage_even a ζ hU hUe hT hTe,
    field_gaussianTiltAverage_even_antitone a ζ hU hUe (F.growth t) hT hTe hTa
      (fun z => F.bT (t, z) ht)⟩

end FieldSmoothFamily

end InvariantIsing

end

end OAI
