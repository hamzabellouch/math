import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CuntzSemigroup.CuntzRankMonotone
import OAI.Analysis.JiangSu.Comparison.CuntzBasic
import OAI.Analysis.JiangSu.CStarAlgebras.CompletedHereditaryWeight

namespace OAI

noncomputable section
namespace Pureness
open Filter Topology
open scoped ComplexOrder ENNReal NNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
local notation "D" => CornerCompletion A
local notation "U" => Unitization ℂ (CornerCompletion A)

abbrev completedRankRealModule : Module ℝ D :=
  UniformSpace.Completion.instModule
attribute [local instance] completedRankRealModule
abbrev completedRankRealSMulZero : SMulZeroClass ℝ D :=
  (completedRankRealModule (A := A)).toDistribMulAction.toDistribSMul.toSMulZeroClass
attribute [local instance] completedRankRealSMulZero
abbrev completedRankRealAlgebra : Algebra ℝ U := Unitization.instAlgebra ℝ ℂ D
attribute [local instance] completedRankRealAlgebra

lemma completed_sqrt_row_hereditary (h : D) (hh : 0 ≤ h) (v : U) (y : D)
    (hy : (y : U) = ((CFC.sqrt h : D) : U) * v) (r : ℝ) :
    ((r • (y * star y) : D) : U) ∈ hereditaryCarrier (h : U) := by
  have hm : ((y * star y : D) : U) ∈ hereditaryCarrier (h : U) := by
    rw [Unitization.inr_mul, Unitization.inr_star, hy, star_mul, ← Unitization.inr_star,
      (CFC.sqrt_nonneg h).star_eq, ← Unitization.sqrt_inr]
    have he : CFC.sqrt (h : U) * v * (star v * CFC.sqrt (h : U)) =
        CFC.sqrt (h : U) * (v * star v) * CFC.sqrt (h : U) := by
      simp only [mul_assoc]
    rw [he]
    exact sqrt_sandwich_mem_hereditary _ _ (Unitization.inr_nonneg_iff.mpr hh)
  rw [Unitization.inr_smul]
  exact (hereditarySubalgebra (h : U) (Unitization.inr_nonneg_iff.mpr hh)).smul_mem r hm

lemma completed_sqrt_row_weight (τ : TracialState A) (h : D) (hh : 0 ≤ h)
    (v : U) (y : D) (hy : (y : U) = ((CFC.sqrt h : D) : U) * v)
    (d : ℝ) (hd : 0 < d) (hbound : ‖star y * y‖ ≤ d) :
    completedDiagonalWeight τ (d⁻¹ • (star y * y)) ≤ completedRootRank τ h := by
  have hnorm : ‖y * star y‖ = ‖star y * y‖ := by
    rw [CStarRing.norm_self_mul_star, CStarRing.norm_star_mul_self]
  have hcontract : ‖d⁻¹ • (y * star y)‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd), hnorm]
    exact (inv_mul_le_one₀ hd).mpr hbound
  calc
    _ = completedDiagonalWeight τ (d⁻¹ • (y * star y)) := by
      rw [completedDiagonalWeight_smul τ _ (le_of_lt (inv_pos.mpr hd)),
        completedDiagonalWeight_smul τ _ (le_of_lt (inv_pos.mpr hd)),
        completedDiagonalWeight_tracial]
    _ ≤ completedRootRank τ h := completedWeight_le_rank_of_hereditary τ h _ hh
      (smul_nonneg (le_of_lt (inv_pos.mpr hd)) (mul_star_self_nonneg _)) hcontract
      (completed_sqrt_row_hereditary h hh v y hy _)

lemma completedWeight_le_rank_of_unitized_cuntz (τ : TracialState A) (c h : D)
    (_ : 0 ≤ c) (hh : 0 ≤ h) (hc1 : ‖c‖ ≤ 1)
    (hch : CuntzSubequiv (c : U) (h : U)) :
    completedDiagonalWeight τ c ≤ completedRootRank τ h := by
  obtain ⟨v, hv⟩ := (cuntzSubequiv_iff_sequence (c : U) (h : U)).mp hch
  let y : ℕ → D := fun j => (((CFC.sqrt h : D) : U) * v j).snd
  have hy (j : ℕ) : (y j : U) = ((CFC.sqrt h : D) : U) * v j := by
    apply Unitization.ext
    · simp [y]
    · rfl
  have hs (j : ℕ) : ((star (y j) * y j : D) : U) = star (v j) * (h : U) * v j := by
    rw [Unitization.inr_mul, Unitization.inr_star, hy, star_mul]
    simp only [← Unitization.inr_star, (CFC.sqrt_nonneg h).star_eq, mul_assoc,
      ← mul_assoc (((CFC.sqrt h : D) : U)), ← Unitization.inr_mul,
      CFC.sqrt_mul_sqrt_self h hh]
  have ht : Tendsto (fun j => star (y j) * y j) atTop (𝓝 c) := by
    apply (Unitization.isometry_inr (𝕜 := ℂ)).isEmbedding.tendsto_nhds_iff.mpr
    change Tendsto (fun j => ((star (y j) * y j : D) : U)) atTop (𝓝 (c : U))
    simpa only [hs] using hv
  let d : ℕ → ℝ := fun j => max 1 ‖star (y j) * y j‖
  have hd (j : ℕ) : 0 < d j := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hdlim : Tendsto d atTop (𝓝 1) := by
    simpa only [max_eq_left hc1] using (tendsto_const_nhds (x := (1 : ℝ))).max ht.norm
  have hlim : Tendsto (fun j => (d j)⁻¹ • (star (y j) * y j)) atTop (𝓝 c) := by
    let : NormedSpace ℝ D := UniformSpace.Completion.instNormedSpace ℝ (FiniteMatrixLimit A)
    let : IsBoundedSMul ℝ D := .of_norm_smul_le NormedSpace.norm_smul_le
    let : ContinuousSMul ℝ D := IsBoundedSMul.continuousSMul
    simpa only [inv_one, one_smul] using (hdlim.inv₀ one_ne_zero).smul ht
  apply completedDiagonalWeight_le_of_tendsto τ hlim
  intro j
  exact completed_sqrt_row_weight τ h hh (v j) (y j) (hy j) (d j) (hd j)
    (le_max_right _ _)

theorem completedRootRank_le_of_unitized_cuntz (τ : TracialState A) (a b : D)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : CuntzSubequiv (a : U) (b : U)) :
    completedRootRank τ a ≤ completedRootRank τ b := by
  apply iSup_le
  intro j
  apply completedWeight_le_rank_of_unitized_cuntz τ _ b (nonUnitalRoot_nonneg a j) hb
    (nonUnitalRoot_norm_le a ha j)
  rw [nonUnitalRoot_inr a ha]
  exact (hereditary_cuntzSubequiv (a : U) (normalizedRoot (a : U) j)
    (Unitization.inr_nonneg_iff.mpr ha) (normalizedRoot_nonneg _ j)
    (normalizedRoot_mem_hereditary (Unitization.inr_nonneg_iff.mpr ha)
      (self_mem_hereditary _ (Unitization.inr_nonneg_iff.mpr ha))
      (Unitization.inr_nonneg_iff.mpr ha) j)).trans hab

end Pureness

end

namespace Pureness
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
      rw [show CFC.sqrt a - e j * CFC.sqrt a = (1 - e j) * CFC.sqrt a by
        rw [sub_mul, one_mul]]
      rw [star_mul, (CFC.sqrt_nonneg a).star_eq, hstar]
      calc
        _ = (1 - e j) * (CFC.sqrt a * CFC.sqrt a) * (1 - e j) := by
          simp only [mul_assoc]
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

end Pureness

end OAI
