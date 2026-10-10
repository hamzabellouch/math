import OAI.Analysis.Pureness.Cuntz.CuntzPolar
import OAI.Analysis.Pureness.Cuntz.CuntzRankMonotone

namespace OAI
namespace CuntzPureness
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma normalizedRoot_mul_sqrt_of_le_tendsto (a h : A) (ha : 0 ≤ a) (hah : a ≤ h) :
    Tendsto (fun j => normalizedRoot h j * CFC.sqrt a) atTop (𝓝 (CFC.sqrt a)) := by
  have hh := ha.trans hah
  let e := normalizedRoot h
  let z := fun j => h - e j * h
  have he (j : ℕ) : ‖e j‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (normalizedRoot_nonneg h j)).mpr
      (normalizedRoot_le_one h hh j)
  have hz : Tendsto z atTop (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := h)).sub
      (normalizedRoot_mul_self_tendsto h hh)
  have hw : Tendsto (fun j => z j - z j * e j) atTop (𝓝 0) := by
    simpa only [sub_zero] using hz.sub (tendsto_mul_zero_of_norm_le_one z e hz he)
  have hb (j : ℕ) : ‖CFC.sqrt a - e j * CFC.sqrt a‖ ^ 2 ≤ ‖z j - z j * e j‖ := by
    have hstar : star (1 - e j) = 1 - e j := by
      rw [star_sub, star_one, (normalizedRoot_nonneg h j).star_eq]
    have hsq : (CFC.sqrt a - e j * CFC.sqrt a) * star (CFC.sqrt a - e j * CFC.sqrt a) =
        star (1 - e j) * a * (1 - e j) := by
      rw [show CFC.sqrt a - e j * CFC.sqrt a = (1 - e j) * CFC.sqrt a by noncomm_ring]
      rw [star_mul, (CFC.sqrt_nonneg a).star_eq, hstar]
      calc
        _ = (1 - e j) * (CFC.sqrt a * CFC.sqrt a) * (1 - e j) := by noncomm_ring
        _ = _ := by rw [CFC.sqrt_mul_sqrt_self a ha]
    calc
      _ = ‖(CFC.sqrt a - e j * CFC.sqrt a) * star (CFC.sqrt a - e j * CFC.sqrt a)‖ := by
        rw [norm_mul_star_self, pow_two]
      _ ≤ ‖star (1 - e j) * h * (1 - e j)‖ := by
        rw [hsq]
        exact CStarAlgebra.norm_le_norm_of_le_of_nonneg
          (star_left_conjugate_le_conjugate hah _) (star_left_conjugate_nonneg ha _)
      _ = _ := by rw [hstar]; congr 1; dsimp [z]; noncomm_ring
  have hsq : Tendsto (fun j => ‖CFC.sqrt a - e j * CFC.sqrt a‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun j => sq_nonneg _) hb (by simpa only [norm_zero] using hw.norm)
  have hzero : Tendsto (fun j => CFC.sqrt a - e j * CFC.sqrt a) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsq.sqrt
  simpa only [sub_sub_cancel, sub_zero] using (tendsto_const_nhds (x := CFC.sqrt a)).sub hzero

theorem cuntzSubequiv_of_nonneg_of_le (a h : A) (ha : 0 ≤ a) (hah : a ≤ h) :
    CuntzSubequiv a h := by
  have hh := ha.trans hah
  have ht : Tendsto (fun j => star (CFC.sqrt a) * normalizedRoot h j * CFC.sqrt a)
      atTop (𝓝 a) := by
    have ht := (tendsto_const_nhds (x := star (CFC.sqrt a))).mul (normalizedRoot_mul_sqrt_of_le_tendsto a h ha hah)
    simpa only [← mul_assoc, (CFC.sqrt_nonneg a).star_eq, CFC.sqrt_mul_sqrt_self a ha] using ht
  apply cuntzSubequiv_of_tendsto _ ht
  intro j
  exact (hereditary_cuntzSubequiv h (normalizedRoot h j) hh (normalizedRoot_nonneg h j)
    (normalizedRoot_mem_hereditary hh (self_mem_hereditary h hh) hh j)).conjugate_left (CFC.sqrt a)

lemma rank_mono_positive (τ : TracialState A) (a h : A) (ha : 0 ≤ a) (hah : a ≤ h) :
    normalizedRootRank τ a ≤ normalizedRootRank τ h :=
  (cuntzSubequiv_of_nonneg_of_le a h ha hah).rank_le ha (ha.trans hah) τ
end CuntzPureness

end OAI
