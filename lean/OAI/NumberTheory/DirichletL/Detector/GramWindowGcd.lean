import OAI.NumberTheory.DirichletL.Detector.GramFiniteGcd

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss

lemma commonColumns_window (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y) (C : SupportedIdeal) :
    commonColumns (lowGaussColumns W hW Y hY) C=
      lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY) := by
  ext I
  rw [commonColumns_mem,lowGaussColumns_mem,lowGaussColumns_mem,common_column_ratio]

theorem original_window_gcd (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y)
    (f : SupportedIdeal→SupportedIdeal→ℂ) :
    (∑I∈lowGaussColumns W hW Y hY,∑J∈lowGaussColumns W hW Y hY,f I J)=
      ∑C∈commonPool (lowGaussColumns W hW Y hY),
        ∑I∈lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY),
        ∑J∈lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY),
        if IsCoprime I.val J.val then f (supportedIdealProduct C I) (supportedIdealProduct C J) else 0 := by
  rw [finite_pair_gcd]
  simp_rw [commonColumns_window]

lemma commonPool_norm_bound (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y)
    (a b : ℝ) (hs : Function.support W⊆Set.Icc a b)
    (C : SupportedIdeal) (hC : C∈commonPool (lowGaussColumns W hW Y hY)) :
    (Ideal.absNorm C.val:ℝ)≤b*Y := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hC
  have hnp : (Ideal.absNorm p.1.val:ℝ)≤b*Y :=
    (div_le_iff₀ hY).mp (hs ((lowGaussColumns_mem W hW Y hY p.1).mp (Finset.mem_product.mp hp).1)).2
  have hg : Ideal.absNorm (gcdCommon p.1 p.2).val≤Ideal.absNorm p.1.val :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.1.property.1))
      (map_dvd Ideal.absNorm (gcd_dvd_left p.1.val p.2.val))
  exact (by exact_mod_cast hg : (Ideal.absNorm (gcdCommon p.1 p.2).val:ℝ)≤Ideal.absNorm p.1.val).trans hnp

end SevenEighths.ProbeGramCommon
end

end OAI
