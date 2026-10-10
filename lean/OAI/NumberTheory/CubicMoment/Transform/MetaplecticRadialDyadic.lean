import OAI.NumberTheory.CubicMoment.Transform.MetaplecticUniformRadialInverse
import OAI.NumberTheory.CubicMoment.Estimates.GammaQuotientGrowth

namespace OAI

/-! The radial dyadic height estimate in the polynomial range used by
the prime decomposition. No metaplectic mean-square input is required. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

theorem UniformLogWeights.radial_dyadic_mean_from_voronoi
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M)
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W)
    {η : ℝ} (hη : 0 < η) (D : ℕ) :
    ∃ K E : ℝ, 0 ≤ K ∧ 0 ≤ E ∧ ∀ i r, primary r → Squarefree r →
      ∀ X U T : ℝ, 1 ≤ X → 1 ≤ U → U ≤ X → 1 ≤ T → T ≤ X^2 → norm r ≤ 2*X →
      ((∫ t in -(2*T)..-T, ‖metaplecticAngularSmoothSum r 0 (W i) U t‖)+
        (∫ t in T..2*T, ‖metaplecticAngularSmoothSum r 0 (W i) U t‖))/T ≤
          K*Real.sqrt U*X^η*norm r^(1/4:ℝ)*Real.sqrt T+
            E*U^(5/6:ℝ)*norm r^(-1/6:ℝ)/T^D := by
  obtain ⟨mp,mn,K,E,_hmp,_hmn,hK,hE,hbound⟩ :=
    h.metaplectic_inverted_radial_mean hV hMV hM hη (by norm_num : (0:ℝ) ≤ 2) D
  let S := max 2 (Real.exp h.radius)
  have hS : 1 ≤ S := le_trans (by norm_num) (le_max_left _ _)
  have hSp : 0 < S := zero_lt_one.trans_le hS
  refine ⟨K*S^η,E,by positivity,hE,?_⟩
  intro i r hr hsr X U T hX hU hUX hT hTX hRX
  have hXp := zero_lt_one.trans_le hX
  have hUp := zero_lt_one.trans_le hU
  let Y := S*X
  have hY : 1 ≤ Y := one_le_mul_of_one_le_of_one_le hS hX
  have hYp := zero_lt_one.trans_le hY
  have hXY : X ≤ Y := le_mul_of_one_le_left hXp.le hS
  have hYsq : Y ≤ Y^2 := by nlinarith only [hY]
  have hR : norm r ≤ Y^2 := by
    apply hRX.trans
    have h2 : 2*X ≤ Y := mul_le_mul_of_nonneg_right (le_max_left _ _) hXp.le
    exact h2.trans hYsq
  have hTY : T ≤ Y^2 := hTX.trans (pow_le_pow_left₀ hXp.le hXY 2)
  have hUY : U ≤ Y^2 := hUX.trans (hXY.trans hYsq)
  have hlo : Y^(-(2:ℝ)) ≤ U := by
    calc
      _ ≤ Y^(0:ℝ) := Real.rpow_le_rpow_of_exponent_le hY (by norm_num)
      _ = 1 := Real.rpow_zero _
      _ ≤ U := hU
  have hFY : Real.exp h.radius*U ≤ Y^2 := by
    have he := le_max_right (2:ℝ) (Real.exp h.radius)
    exact (mul_le_mul he hUX hUp.le hSp.le).trans hYsq
  have hg (m : ℕ) :
      AngularGammaQuotientStripBound (metaplecticAngularShift 0-1/6) (-((m:ℝ)-1/2)) ∧
      AngularGammaQuotientStripBound (metaplecticAngularShift 0+1/6) (-((m:ℝ)-1/2)) := by
    constructor <;> apply angularGammaQuotientStripBound_proved <;>
      norm_num [metaplecticAngularShift]
  have hb := hbound i r hr hsr Y U (Real.exp h.radius*U) T hY hUp hT
    (by simpa only [Real.rpow_two] using hR)
    (by simpa only [Real.rpow_two] using hTY) hlo
    (by simpa only [Real.rpow_two] using hUY) le_rfl
    (by simpa only [Real.rpow_two] using hFY) (hg mp).1 (hg mp).2 (hg mn).1 (hg mn).2
  apply hb.trans_eq
  dsimp [Y]
  rw [Real.mul_rpow hSp.le hXp.le]
  ring

end CubicFirstMoment

end

end OAI
