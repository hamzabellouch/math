import OAI.NumberTheory.CubicMoment.Estimates.IdealMangoldtPrefix
import OAI.NumberTheory.CubicMoment.Estimates.PrimeDyadicScales
import OAI.NumberTheory.CubicMoment.Estimates.PrimeDyadicMajorant

namespace OAI

/-! Quantitative reconstruction of the full ideal von Mangoldt prefix.
The lower endpoint corrections and the square-root prefix are retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem idealMangoldt_full_from_dyadic (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {B c Q X0 X : ℝ}
    (hB : 0 ≤ B) (hc : 0 ≤ c) (hc1 : c ≤ 1/2) (hQ : 1 ≤ Q) (hX0 : 1 ≤ X0)
    (hdyad : ∀ t : ℝ, X0 ≤ t → ‖idealMangoldtDyadic χ t‖ ≤ B*primeCancellationWeight c Q t)
    (hXp : 0 < X) (hX : 2 ≤ Real.log X) (hXX0 : X0^2 ≤ X) :
    ‖idealMangoldtSum χ X‖ ≤ (B+24)*primeCancellationWeight (c/2) Q X := by
  have hX1 : 1 ≤ X := by
    have hh := Real.exp_le_exp.mpr (show (0:ℝ) ≤ Real.log X by linarith)
    simpa [Real.exp_log hXp] using hh
  obtain ⟨N,hrlo,hrhi,hrX,hscales⟩ := exists_primeDyadic_sqrt_split hX1
  have hs0 : X0 ≤ Real.sqrt X := (Real.le_sqrt (by linarith) hXp.le).mpr hXX0
  let E := (Real.log (X*Q))^2*Real.exp (-(c/2)*Real.log X/primeContourDenominator Q X)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hinc (j : ℕ) (hj : j ∈ Finset.range N) :
      ‖dyadicDifference (idealMangoldtSum χ) (X/(2:ℝ)^j)‖ ≤
        (B+8)*(X/(2:ℝ)^(j+1)*E) := by
    let t := X/(2:ℝ)^(j+1)
    obtain ⟨htlo,htX⟩ := hscales j (Finset.mem_range.mp hj)
    have htp : 0 < t := by dsimp [t]; positivity
    have ht0 : X0 ≤ t := hs0.trans htlo
    have ht1 : 1 ≤ t := hX0.trans ht0
    have hxj : X/(2:ℝ)^j = 2*t := by
      dsimp [t]
      rw [pow_succ]
      field_simp
    have he : dyadicDifference (idealMangoldtSum χ) (X/(2:ℝ)^j) =
        idealMangoldtDyadic χ t-
          ∑ ν ∈ fullIdealBall (2*t) with idealExponentNorm ν = t,
            ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν := by
      unfold dyadicDifference
      rw [hxj,show 2*t/2=t by ring,idealMangoldtSum_dyadic χ htp.le]
    have hd := (hdyad t ht0).trans (mul_le_mul_of_nonneg_left
      (primeDyadic_majorant_compare hc hQ hXp hX htlo htX) hB)
    have hb := (idealMangoldt_boundary_bound χ hχ (B := 2*t) ht1).trans
      (primeDyadic_boundary_compare hc hc1 hQ hXp hX htlo htX)
    rw [he]
    calc
      _ ≤ ‖idealMangoldtDyadic χ t‖+
          ‖∑ ν ∈ fullIdealBall (2*t) with idealExponentNorm ν = t,
            ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν‖ := norm_sub_le _ _
      _ ≤ B*(t*(Real.log (X*Q))^2*Real.exp (-(c/2)*Real.log X/primeContourDenominator Q X))+
          8*(t*(Real.log (X*Q))^2*Real.exp (-(c/2)*Real.log X/primeContourDenominator Q X)) :=
        add_le_add hd hb
      _ = _ := by dsimp [t,E]; ring
  have hr1 : 1 ≤ X/(2:ℝ)^N := hX0.trans (hs0.trans hrlo)
  have hsmall := (idealMangoldtSum_norm_bound χ hχ hr1).trans
    (primeDyadic_small_compare hc hc1 hQ hXp hX hr1 hrX hrhi)
  have htel : idealMangoldtSum χ X =
      (∑ j ∈ Finset.range N, dyadicDifference (idealMangoldtSum χ) (X/(2:ℝ)^j))+
        idealMangoldtSum χ (X/(2:ℝ)^N) := by
    rw [dyadicDifference_sum]
    abel
  have hsum : (∑ j ∈ Finset.range N, (B+8)*(X/(2:ℝ)^(j+1)*E)) =
      (B+8)*((∑ j ∈ Finset.range N, X/(2:ℝ)^(j+1))*E) := by
    simp only [Finset.mul_sum,Finset.sum_mul]
  calc
    _ = ‖(∑ j ∈ Finset.range N, dyadicDifference (idealMangoldtSum χ) (X/(2:ℝ)^j))+
        idealMangoldtSum χ (X/(2:ℝ)^N)‖ := congrArg _ htel
    _ ≤ (∑ j ∈ Finset.range N, ‖dyadicDifference (idealMangoldtSum χ) (X/(2:ℝ)^j)‖)+
        ‖idealMangoldtSum χ (X/(2:ℝ)^N)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) le_rfl)
    _ ≤ (∑ j ∈ Finset.range N, (B+8)*(X/(2:ℝ)^(j+1)*E))+
        16*primeCancellationWeight (c/2) Q X := add_le_add (Finset.sum_le_sum hinc) hsmall
    _ = (B+8)*((∑ j ∈ Finset.range N, X/(2:ℝ)^(j+1))*E)+16*primeCancellationWeight (c/2) Q X := by rw [hsum]
    _ ≤ (B+8)*(X*E)+16*primeCancellationWeight (c/2) Q X := by
      exact add_le_add (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (primeDyadic_scale_sum_le hXp.le N) hE) (by linarith)) le_rfl
    _ = _ := by dsimp [E,primeCancellationWeight]; ring

end CubicFirstMoment

end

end OAI
