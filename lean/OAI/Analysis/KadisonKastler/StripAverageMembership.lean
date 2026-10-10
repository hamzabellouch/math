import OAI.Analysis.KadisonKastler.StripAverageUniqueness
import OAI.Analysis.KadisonKastler.RegularWeightedIntegral

namespace OAI

/-! # Recovering algebra membership from all strip averages

Once the bounded modular equation identifies these averages with algebra
elements, this lemma gives membership of every operator on the orbit.
-/

namespace KadisonKastler

open MeasureTheory Set

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Exponential strip averages determine membership in a von Neumann algebra. -/
theorem mem_of_strip_averages (M : VonNeumannAlgebra H) {a : ℝ} (ha : 0 < a)
    (F : ℝ → H →L[ℂ] H) (hc : ∀ x, Continuous (fun t => F t x))
    (B : ℝ) (hb : ∀ t, ‖F t‖ ≤ B)
    (hm : ∀ s (hs : |s| < a),
      weightedOperatorIntegral volume (stripAverageKernel a (s : ℂ))
        (stripAverageKernel_integrable (by simpa using hs)) F
        (fun x => (hc x).aestronglyMeasurable) B (Filter.Eventually.of_forall hb) ∈ M) :
    ∀ t, F t ∈ M := by
  intro t
  change F t ∈ (M : Set (H →L[ℂ] H))
  rw [← M.centralizer_centralizer]
  intro A hA
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  let g : ℝ → ℂ := fun u => inner ℂ y (F u (A x) - A (F u x))
  have hgc : Continuous g := continuous_const.inner
    ((hc (A x)).sub (A.continuous.comp (hc x)))
  have hgb : ∀ u, ‖g u‖ ≤ ‖y‖ * (B * ‖A x‖ + ‖A‖ * (B * ‖x‖)) := by
    intro u
    apply (norm_inner_le_norm _ _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg y)
    apply (norm_sub_le _ _).trans
    exact add_le_add
      (((F u).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hb u) (norm_nonneg _)))
      ((A.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (((F u).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hb u) (norm_nonneg _)))
        (norm_nonneg A)))
  have hgz : ∀ s ∈ Ioo (-a) a, (∫ u, stripAverageKernel a (s : ℂ) u * g u) = 0 := by
    intro s hs
    have hs' : |s| < a := abs_lt.mpr hs
    let w := stripAverageKernel a (s : ℂ)
    have hw : Integrable w := stripAverageKernel_integrable (by simpa using hs')
    let V := weightedOperatorIntegral volume w hw F
      (fun z => (hc z).aestronglyMeasurable) B (Filter.Eventually.of_forall hb)
    have hV : V ∈ M := hm s hs'
    have hcomm : V * A = A * V := hA V hV
    have hi (z : H) : Integrable (fun u => w u • F u z) :=
      integrable_weighted_operator_vector volume w hw F
        (fun z => (hc z).aestronglyMeasurable) B (Filter.Eventually.of_forall hb) z
    have hdi : (∫ u, w u • (F u (A x) - A (F u x))) = 0 := by
      have hAs (u : ℝ) : w u • A (F u x) = A (w u • F u x) :=
        (map_smul A (w u) (F u x)).symm
      simp_rw [smul_sub, hAs]
      rw [integral_sub (hi (A x)) (A.integrable_comp (hi x)),
        A.integral_comp_comm (hi x)]
      exact sub_eq_zero.mpr (congrArg (fun T : H →L[ℂ] H => T x) hcomm)
    have hdiI : Integrable (fun u => w u • (F u (A x) - A (F u x))) := by
      convert! (hi (A x)).sub (A.integrable_comp (hi x)) using 1
      funext u
      simp only [Pi.sub_apply, smul_sub, map_smul]
    have he := (innerSL ℂ y).integral_comp_comm hdiI
    change (∫ u, inner ℂ y (w u • (F u (A x) - A (F u x)))) =
      inner ℂ y (∫ u, w u • (F u (A x) - A (F u x))) at he
    rw [hdi, inner_zero_right] at he
    simpa only [inner_smul_right, smul_eq_mul] using he
  have hg0 := zero_of_strip_averages ha g hgc hgb hgz
  have he := congrFun hg0 t
  change inner ℂ y (F t (A x) - A (F t x)) = 0 at he
  rw [inner_sub_right] at he
  exact (sub_eq_zero.mp he).symm

end

end KadisonKastler

end OAI
