import OAI.Analysis.IrrationalRotation.Spectral.InvertibleDeterminant

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal CStarAlgebra
namespace Invariant233

variable {A : Type*} [CStarAlgebra A]

theorem TracialState.re_nonneg {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (τ : TracialState A)
    {a : A} (ha : 0 ≤ a) : 0 ≤ (τ a).re := by
  have h := τ.positive (CFC.sqrt a)
  rw [(CFC.sqrt_nonneg a).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self a ha] at h
  exact h

theorem TracialState.re_mono {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (τ : TracialState A)
    {a b : A} (hab : a ≤ b) : (τ a).re ≤ (τ b).re := by
  have h := τ.re_nonneg (sub_nonneg.mpr hab)
  change 0 ≤ (τ.toContinuousLinearMap (b - a)).re at h
  simpa only [map_sub, Complex.sub_re, sub_nonneg] using h

theorem fugledeKadisonDeterminant_of_isUnit (τ : TracialState A) (a : A)
    (ha : IsUnit a) :
    fugledeKadisonDeterminant τ a =
      ENNReal.ofReal (Real.exp ((τ (CFC.log (star a * a))).re / 2)) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hp : IsStrictlyPositive (star a * a) :=
    ⟨star_mul_self_nonneg a, ha.star.mul ha⟩
  have hcont : Continuous (fun b : A =>
      ENNReal.ofReal (Real.exp ((τ b).re / 2))) := by
    apply ENNReal.continuous_ofReal.comp
    fun_prop
  have hlim := hcont.continuousAt.tendsto.comp (tendsto_log_add_one_div (star a * a) hp)
  unfold fugledeKadisonDeterminant
  apply le_antisymm
  · apply ge_of_tendsto' hlim
    intro n
    exact iInf_le _ (⟨1 / ((n : ℝ) + 1), by positivity⟩ : {r : ℝ // 0 < r})
  · apply le_iInf
    intro ε
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact τ.re_mono (log_le_log_add_smul_one (star a * a) hp ε.val ε.property.le)

theorem fugledeKadisonDeterminant_pos_of_isUnit (τ : TracialState A) (a : A)
    (ha : IsUnit a) : 0 < fugledeKadisonDeterminant τ a := by
  rw [fugledeKadisonDeterminant_of_isUnit τ a ha]
  exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)

end Invariant233

end

end OAI
