import OAI.Probability.InvariantIsing.Fields.FieldGaussianRecursionOrder
import OAI.Probability.InvariantIsing.Fields.FieldMajorantFold

namespace OAI

/-! The terminal scale comparison propagated through the actual finite
one-site Gaussian recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma gaussianOperator_fold_even (L : List (ℝ × ℝ))
    (hL : ∀ av ∈ L, 0 < av.1 ∧ 0 ≤ av.2) {F : ℝ → ℝ}
    (hF : Measurable F) (hgrowth : HasLinearGrowth F) (hEven : Function.Even F) :
    Function.Even (L.foldr (fun av f => gaussianOperator av.1 av.2 f) F) := by
  induction L with
  | nil => exact hEven
  | cons av L ih =>
    have htail (bv) (hb : bv ∈ L) := hL bv (List.mem_cons_of_mem av hb)
    have hreg := gaussianOperator_fold_growth L (fun bv hb => (htail bv hb).1) hF hgrowth
    have hv := (hL av (List.mem_cons_self)).2
    simpa only [List.foldr_cons, NNReal.coe_mk] using
      (gaussianOperator_even av.1 (NNReal.mk av.2 hv) hreg.1 (ih htail))

lemma gaussianOperator_fold_difference_monotone (L : List (ℝ × ℝ))
    (hL : ∀ av ∈ L, 0 < av.1 ∧ 0 ≤ av.2) {F G : ℝ → ℝ}
    (hF : Measurable F) (hG : Measurable G)
    (hFgrowth : HasLinearGrowth F) (hGgrowth : HasLinearGrowth G)
    (hFeven : Function.Even F) (hGeven : Function.Even G)
    (hFG : MonotoneOn (fun z => G z - F z) (Ici 0)) :
    MonotoneOn (fun z => (L.foldr (fun av f => gaussianOperator av.1 av.2 f) G) z -
      (L.foldr (fun av f => gaussianOperator av.1 av.2 f) F) z) (Ici 0) := by
  induction L with
  | nil => exact hFG
  | cons av L ih =>
    have htail (bv) (hb : bv ∈ L) := hL bv (List.mem_cons_of_mem av hb)
    have hregF := gaussianOperator_fold_growth L (fun bv hb => (htail bv hb).1) hF hFgrowth
    have hregG := gaussianOperator_fold_growth L (fun bv hb => (htail bv hb).1) hG hGgrowth
    have hEvenF := gaussianOperator_fold_even L htail hF hFgrowth hFeven
    have hEvenG := gaussianOperator_fold_even L htail hG hGgrowth hGeven
    have hav := hL av (List.mem_cons_self)
    simpa only [List.foldr_cons, NNReal.coe_mk] using
      gaussianOperator_difference_monotone (NNReal.mk av.2 hav.2) hav.1.le
        _ _ hregF.1 hregG.1 hEvenF hEvenG hregF.2 hregG.2 (ih htail)

/-- The exact scaled Ising terminal used in the radial covariance argument. -/
theorem field_radial_backward_difference_monotone (L : List (ℝ × ℝ))
    (hL : ∀ av ∈ L, 0 < av.1 ∧ 0 ≤ av.2) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    MonotoneOn (fun z =>
      (L.foldr (fun av f => gaussianOperator av.1 av.2 f)
        (fun u => Real.log (Real.cosh (b * u)))) z -
      (L.foldr (fun av f => gaussianOperator av.1 av.2 f)
        (fun u => Real.log (Real.cosh (a * u)))) z) (Ici 0) := by
  apply gaussianOperator_fold_difference_monotone L hL
  · exact measurable_logCosh.comp (measurable_id.const_mul a)
  · exact measurable_logCosh.comp (measurable_id.const_mul b)
  · exact logCosh_linearGrowth.scale_argument a
  · exact logCosh_linearGrowth.scale_argument b
  · intro z
    simp only [mul_neg, Real.cosh_neg]
  · intro z
    simp only [mul_neg, Real.cosh_neg]
  · exact field_logcosh_scaled_difference_monotone ha hab

end InvariantIsing

end

end OAI
