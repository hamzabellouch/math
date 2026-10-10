import OAI.MeasureTheory.Falconer.Angular.GnomonicTripleAngle
import OAI.MeasureTheory.Falconer.Slicing.GaussianTruncatedTriple

namespace OAI

/-! # The truncated Gaussian kernel of three original chart labels -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

theorem gnomonic_triple_kernel (p q s : Space n)
    (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1) (hs : ‖s‖ ≤ 1)
    {b r : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hr : 0 < r)
    (hpq : b ≤ ‖q-p‖) (hps : b ≤ ‖s-p‖) :
    (ENNReal.ofReal (r^(-(h:ℝ))))^3 *
      gaussianRows (n+1) h {A | ∀ i,
        |inner ℝ (gnomonicChart p : Space (n+1)) (A i)| ≤ r ∧
        |inner ℝ (gnomonicChart q : Space (n+1)) (A i)| ≤ r ∧
        |inner ℝ (gnomonicChart s : Space (n+1)) (A i)| ≤ r} ≤
      ENNReal.ofReal ((gaussianTripleBandConstant/
        ((b/4)^2*max (displacementAngle p q s) r))^h) := by
  let v : Fin 3 → Space (n+1) :=
    ![(gnomonicChart p : Space (n+1)),(gnomonicChart q : Space (n+1)),
      (gnomonicChart s : Space (n+1))]
  have hsep : b/4 ≤ ‖perpendicularPart (v 0) (v 1)‖ := by
    have hh := gnomonic_pair_separation hp hq
    dsimp [v]
    linarith
  have hqne : q ≠ p := by
    intro he
    rw [he,sub_self,norm_zero] at hpq
    linarith
  have hsne : s ≠ p := by
    intro he
    rw [he,sub_self,norm_zero] at hps
    linarith
  have hgram : (b/4)^2*displacementAngle p q s ≤ Real.sqrt (Matrix.gram ℝ v).det := by
    have hh := gnomonic_triple_sqrt_lower hp hq hs hqne hsne
    have hmul : b^2*displacementAngle p q s ≤
        ‖q-p‖*‖s-p‖*displacementAngle p q s := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hpq hps hb.le (norm_nonneg _)) (displacementAngle_nonneg p q s)
    change _ ≤ Real.sqrt (tripleGram (gnomonicChart p : Space (n+1))
      (gnomonicChart q : Space (n+1)) (gnomonicChart s : Space (n+1)))
    nlinarith [displacementAngle_nonneg p q s]
  have hh := gaussianRows_three_vector_truncated_normalized (h := h) v
    (sphere_norm (gnomonicChart p)) (sphere_norm (gnomonicChart q))
    hr (by positivity : 0 < b/4) (by linarith : b/4 ≤ 1) hsep hgram
  simpa only [v,Fin.forall_fin_succ,Fin.forall_fin_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.head_cons,Matrix.tail_cons,and_true] using hh

end Falconer

end OAI
