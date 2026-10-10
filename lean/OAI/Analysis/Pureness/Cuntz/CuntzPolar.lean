import OAI.Analysis.Pureness.Divisibility.HereditaryCuntz
import OAI.Analysis.Pureness.Divisibility.HereditaryApproximateUnit

namespace OAI
namespace CuntzPureness
open Filter Topology
variable {A : Type*} [CStarAlgebra A]

lemma norm_mul_star_self (x : A) : ‖x * star x‖ = ‖x‖ * ‖x‖ := by
  simpa only [star_star, norm_star] using (CStarRing.norm_star_mul_self (x := star x))

lemma tendsto_mul_zero_of_norm_le_one (z e : ℕ → A)
    (hz : Tendsto z atTop (𝓝 0)) (he : ∀ n, ‖e n‖ ≤ 1) :
    Tendsto (fun n => z n * e n) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (by simpa only [norm_zero] using hz.norm)
  calc
    _ ≤ ‖z n‖ * ‖e n‖ := norm_mul_le _ _
    _ ≤ ‖z n‖ * 1 := mul_le_mul_of_nonneg_left (he n) (norm_nonneg _)
    _ = ‖z n‖ := mul_one _

variable [PartialOrder A] [StarOrderedRing A]

lemma normalizedRoot_mul_of_mul_star_self_tendsto (h x : A) (hh : 0 ≤ h)
    (hx : x * star x ∈ hereditaryCarrier h) :
    Tendsto (fun j => normalizedRoot h j * x) atTop (𝓝 x) := by
  let e := normalizedRoot h
  let z := fun j => x * star x - e j * (x * star x)
  have he (j : ℕ) : ‖e j‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (normalizedRoot_nonneg h j)).mpr
      (normalizedRoot_le_one h hh j)
  have hz : Tendsto z atTop (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := x * star x)).sub
      (normalizedRoot_mul_hereditary_tendsto h hh _ hx)
  have hw : Tendsto (fun j => z j - z j * e j) atTop (𝓝 0) := by
    simpa only [sub_zero] using hz.sub (tendsto_mul_zero_of_norm_le_one z e hz he)
  have hn (j : ℕ) : ‖x - e j * x‖ ^ 2 = ‖z j - z j * e j‖ := by
    calc
      _ = ‖(x - e j * x) * star (x - e j * x)‖ := by
        rw [norm_mul_star_self, pow_two]
      _ = _ := by
        congr 1
        dsimp [z, e]
        simp only [star_sub, star_mul, (normalizedRoot_nonneg h j).star_eq]
        noncomm_ring
  have hsq : Tendsto (fun j => ‖x - e j * x‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hn, norm_zero] using hw.norm
  have hzero : Tendsto (fun j => x - e j * x) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsq.sqrt
  simpa only [sub_sub_cancel, sub_zero] using (tendsto_const_nhds (x := x)).sub hzero

theorem star_mul_self_cuntzSubequiv_of_hereditary (h x : A) (hh : 0 ≤ h)
    (hx : x * star x ∈ hereditaryCarrier h) : CuntzSubequiv (star x * x) h := by
  have ht : Tendsto (fun j => star x * normalizedRoot h j * x) atTop (𝓝 (star x * x)) := by
    simpa only [mul_assoc] using tendsto_const_nhds.mul
      (normalizedRoot_mul_of_mul_star_self_tendsto h x hh hx)
  apply cuntzSubequiv_of_tendsto _ ht
  intro j
  exact (hereditary_cuntzSubequiv h (normalizedRoot h j) hh (normalizedRoot_nonneg h j)
    (normalizedRoot_mem_hereditary hh (self_mem_hereditary h hh) hh j)).conjugate_left x

theorem star_mul_self_cuntzSubequiv (x : A) : CuntzSubequiv (star x * x) (x * star x) :=
  star_mul_self_cuntzSubequiv_of_hereditary _ x (mul_star_self_nonneg x)
    (self_mem_hereditary _ (mul_star_self_nonneg x))

theorem mul_star_self_cuntzSubequiv (x : A) : CuntzSubequiv (x * star x) (star x * x) := by
  simpa only [star_star] using star_mul_self_cuntzSubequiv (star x)
end CuntzPureness

end OAI
