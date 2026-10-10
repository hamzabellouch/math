import OAI.NumberTheory.CubicMoment.Transform.MetaplecticPrimalFinite
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCompletedLow

namespace OAI

/-! Elementary scale regularity of the actual completed smooth sums.
Compact support makes every scale neighborhood a common finite sum. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_completed_scale_finite (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {B Y V : ℝ} (hY : 0 < Y) (hBV : B*Y ≤ V)
    (hW : ∀ x : ℝ, B < x → W x = 0) :
    metaplecticCompleted r ℓ W Y =
      ∑ du ∈ metaplecticPrimalElementSupport V, metaplecticPrimalCoefficient r ℓ W Y du := by
  have h := metaplecticHeightCompleted_finite r ℓ W hY hBV hW 0
  simpa only [metaplecticHeightCompleted_zero,mellinPhase,zero_mul,Complex.ofReal_zero,
    Complex.exp_zero,mul_one] using h

lemma continuousOn_metaplecticCompleted_scale (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hc : Continuous W) :
    ContinuousOn (metaplecticCompleted r ℓ W) (Ioi 0) := by
  obtain ⟨B,hB⟩ := hW.isCompact.isBounded.exists_norm_le
  let B' := max B 1
  have hBp : 0 < B' := zero_lt_one.trans_le (le_max_right _ _)
  have hcut : ∀ x : ℝ, B' < x → W x = 0 := by
    intro x hx
    by_contra hn
    have hh := hB x (subset_tsupport W hn)
    rw [Real.norm_eq_abs] at hh
    have hBB : B ≤ B' := le_max_left _ _
    linarith [le_abs_self x]
  intro X hX
  have hXp : 0 < X := hX
  let S := metaplecticPrimalElementSupport (B'*(2*X))
  have hfinite : ContinuousAt (fun Y : ℝ => ∑ du ∈ S,
      metaplecticPrimalCoefficient r ℓ W Y du) X := by
    apply tendsto_finsetSum
    intro du hdu
    unfold metaplecticPrimalCoefficient
    split_ifs
    · exact continuousAt_const.mul (hc.continuousAt.comp
        (continuousAt_const.div continuousAt_id hXp.ne'))
    · exact continuousAt_const
  apply (hfinite.congr ?_).continuousWithinAt
  filter_upwards [Ioo_mem_nhds hXp (show X < 2*X by linarith)] with Y hY
  exact (metaplectic_completed_scale_finite r ℓ W hY.1
    (mul_le_mul_of_nonneg_left hY.2.le hBp.le) hcut).symm

lemma metaplecticCompleted_scale_small (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {B : ℝ} (hB : 0 < B) (hW : ∀ x : ℝ, B < x → W x = 0)
    {X : ℝ} (hX : 0 < X) (hXB : X < 1/B) :
    metaplecticCompleted r ℓ W X = 0 := by
  unfold metaplecticCompleted
  have hzero : ∀ du : PrimaryArgument × PrimaryArgument,
      (if IsCoprime (du.1:Eisenstein) r then
        (Real.sqrt (norm du.1):ℂ)*gauss (r*du.2)*theta ℓ (r*(du.2*du.1^3))*
          W (norm (du.2*du.1^3)/X) else 0) = 0 := by
    intro du
    split_ifs
    · have hn : 1 ≤ norm ((du.2:Eisenstein)*du.1^3) :=
        one_le_norm (mul_ne_zero (primary_ne_zero du.2.property)
        (pow_ne_zero _ (primary_ne_zero du.1.property)))
      have hb : B < norm ((du.2:Eisenstein)*du.1^3)/X := by
        apply (lt_div_iff₀ hX).mpr
        have hBX : B*X < 1 := by nlinarith [(lt_div_iff₀ hB).mp hXB]
        exact hBX.trans_le hn
      rw [hW _ hb,mul_zero]
    · rfl
  simp only [hzero,tsum_zero]

end CubicFirstMoment

end

end OAI
