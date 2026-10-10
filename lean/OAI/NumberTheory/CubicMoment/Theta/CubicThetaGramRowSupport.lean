import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveProfileSeparation

namespace OAI

/-! Only bounded lower-left denominators can contribute to the exact
positive-cutoff Gram formula. This bound is independent of the frequency. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma CubicThetaBottomRow.norm_height_product_le (r : CubicThetaBottomRow)
    (hr : r.c≠0) {p : ℂ × ℝ} (hp : 0<p.2) :
    norm r.c*(r.height p*p.2)≤1 := by
  have hn : 0<norm r.c := norm_pos_of_ne_zero hr
  have hD : 0<Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2 :=
    add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (mul_pos hn (sq_pos_of_pos hp))
  unfold CubicThetaBottomRow.height
  rw [show norm r.c*(p.2/(Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2)*p.2)=
      (norm r.c*p.2^2)/(Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2) by ring]
  apply (div_le_iff₀ hD).mpr
  nlinarith [Complex.normSq_nonneg ((r.c:ℂ)*p.1+r.d)]

lemma cubicThetaGramRow_large_denominator_point_zero (h k : Eisenstein)
    (W V : C_c(ℝ,ℂ)) {ε δ : ℝ} (_hε : 0<ε) (hδ : 0<δ)
    (hW : ∀ v≤ε,W v=0) (hV : ∀ v≤δ,V v=0)
    (r : CubicThetaBottomRow) (hlarge : 1≤norm r.c*ε*δ) (p : CubicThetaPoint) :
    star (cubicThetaFourierStripSeed h W p)*cubicThetaFourierProfileTerm k r p.val V=0 := by
  by_cases hz : cubicThetaFourierStripSeed h W p=0
  · rw [hz,star_zero,zero_mul]
  have hr : r.c≠0 := by
    intro he
    rw [he] at hlarge
    norm_num [norm] at hlarge
  have hv : ε<p.val.2 := by
    by_contra hn
    apply hz
    simp only [cubicThetaFourierStripSeed,hW _ (le_of_not_gt hn),zero_mul,ite_self]
  have hheight : r.height p.val≤δ := by
    by_contra hh
    have hh' : δ<r.height p.val := lt_of_not_ge hh
    have hm : δ*ε<r.height p.val*p.val.2 := calc
      δ*ε < δ*p.val.2 := mul_lt_mul_of_pos_left hv hδ
      _ < r.height p.val*p.val.2 := mul_lt_mul_of_pos_right hh' p.property
    have hm' := mul_lt_mul_of_pos_left hm (norm_pos_of_ne_zero hr)
    have hb := r.norm_height_product_le hr p.property
    nlinarith
  rw [cubicThetaFourierProfileTerm_zero k r p.val V (hV _ hheight),mul_zero]

theorem cubicThetaGramRow_large_denominator_integral_zero (h k : Eisenstein)
    (W V : C_c(ℝ,ℂ)) {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ)
    (hW : ∀ v≤ε,W v=0) (hV : ∀ v≤δ,V v=0)
    (r : CubicThetaBottomRow) (hlarge : 1≤norm r.c*ε*δ) :
    (∫ p,star (cubicThetaFourierStripSeed h W p)*
      cubicThetaFourierProfileTerm k r p.val V ∂cubicThetaPointMeasure)=0 := by
  simp only [cubicThetaGramRow_large_denominator_point_zero h k W V hε hδ hW hV r hlarge,
    integral_zero]

end CubicFirstMoment

end

end OAI
