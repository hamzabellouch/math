import OAI.NumberTheory.CubicMoment.Estimates.PrimeDyadicBoundary
import OAI.NumberTheory.CubicMoment.Estimates.PrimeIdealAnnulus
import OAI.NumberTheory.CubicMoment.Estimates.IdealEulerExclusion
import OAI.NumberTheory.CubicMoment.Estimates.IdealMangoldtMellin

namespace OAI

/-! Exact sharp dyadic ideal sums and the two endpoint errors of the
logarithmic smooth cutoff. All ideals, including those above three, remain. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def idealMangoldtDyadic (χ : EisensteinIdealExponent → ℂ) (X : ℝ) : ℂ :=
  ∑ ν ∈ fullIdealBall (2*X) with X ≤ idealExponentNorm ν,
    ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν

lemma idealMangoldtDyadic_eq_sum (χ : EisensteinIdealExponent → ℂ)
    {X B : ℝ} (hB : 2*X ≤ B) :
    idealMangoldtDyadic χ X =
      ∑ ν ∈ fullIdealBall B with X ≤ idealExponentNorm ν ∧ idealExponentNorm ν ≤ 2*X,
        ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν := by
  unfold idealMangoldtDyadic
  congr 1
  ext ν
  simp only [Finset.mem_filter,mem_fullIdealBall]
  constructor
  · rintro ⟨hhi,hlo⟩
    exact ⟨hhi.trans hB,hlo,hhi⟩
  · rintro ⟨_,hlo,hhi⟩
    exact ⟨hhi,hlo⟩

lemma idealMangoldtSmooth_dyadic_eq_sum (χ : EisensteinIdealExponent → ℂ)
    {J X : ℝ} (hJ : 1 ≤ J) (hX : 0 < X) :
    idealMangoldtSmooth χ (primeDyadicWeight J hJ) X =
      ∑ ν ∈ fullIdealBall (2*Real.exp (1/J)*X),
        (((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν)*
          primeDyadicWeight J hJ (idealExponentNorm ν/X) := by
  apply tsum_eq_sum
  intro ν hν
  have hw : primeDyadicWeight J hJ (idealExponentNorm ν/X)=0 := by
    by_contra hn
    have hh := (primeDyadicWeight_support_interval hJ hn).2
    exact hν (mem_fullIdealBall.mpr ((div_le_iff₀ hX).mp hh))
  rw [hw,mul_zero]

theorem idealMangoldt_dyadic_smoothing_error (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {J X : ℝ} (hJ : 1 ≤ J) (hX : 0 < X)
    (hlo : 1 ≤ Real.exp (-1/J)*X) :
    ‖idealMangoldtSmooth χ (primeDyadicWeight J hJ) X-idealMangoldtDyadic χ X‖ ≤
      4*(X-Real.exp (-1/J)*X+Real.sqrt X+Real.sqrt (Real.exp (-1/J)*X))*Real.log X+
      4*(2*Real.exp (1/J)*X-2*X+Real.sqrt (2*Real.exp (1/J)*X)+Real.sqrt (2*X))*
        Real.log (2*Real.exp (1/J)*X) := by
  have hJ0 : 0 < J := zero_lt_one.trans_le hJ
  have he : 1 ≤ Real.exp (1/J) := Real.one_le_exp (by positivity)
  have he' : Real.exp (-1/J) ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (by norm_num) hJ0.le)
  have hAX : Real.exp (-1/J)*X ≤ X := mul_le_of_le_one_left hX.le he'
  have hXB : 2*X ≤ 2*Real.exp (1/J)*X := by nlinarith
  have hX1 : 1 ≤ X := hlo.trans hAX
  let S := fullIdealBall (2*Real.exp (1/J)*X)
  let c := fun ν => ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν
  rw [idealMangoldtSmooth_dyadic_eq_sum χ hJ hX,idealMangoldtDyadic_eq_sum χ hXB]
  apply (primeDyadicWeight_boundary_error S idealExponentNorm c hJ hX).trans
  have hs : (∑ ν ∈ S with
      (Real.exp (-1/J)*X ≤ idealExponentNorm ν ∧ idealExponentNorm ν < X) ∨
      (2*X < idealExponentNorm ν ∧ idealExponentNorm ν ≤ 2*Real.exp (1/J)*X), ‖c ν‖) ≤
      (∑ ν ∈ S with Real.exp (-1/J)*X ≤ idealExponentNorm ν ∧ idealExponentNorm ν ≤ X, ‖c ν‖)+
      (∑ ν ∈ S with 2*X ≤ idealExponentNorm ν ∧ idealExponentNorm ν ≤ 2*Real.exp (1/J)*X, ‖c ν‖) := by
    rw [Finset.sum_filter,Finset.sum_filter,Finset.sum_filter,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro ν hν
    by_cases hL : Real.exp (-1/J)*X ≤ idealExponentNorm ν ∧ idealExponentNorm ν < X
    · have hLc : Real.exp (-1/J)*X ≤ idealExponentNorm ν ∧ idealExponentNorm ν ≤ X :=
        ⟨hL.1,hL.2.le⟩
      rw [ite_eq_left (Or.inl hL),ite_eq_left hLc]
      split_ifs <;> simp only [add_zero,le_add_iff_nonneg_right,_root_.norm_nonneg,le_refl]
    · by_cases hR : 2*X < idealExponentNorm ν ∧
          idealExponentNorm ν ≤ 2*Real.exp (1/J)*X
      · have hRc : 2*X ≤ idealExponentNorm ν ∧
            idealExponentNorm ν ≤ 2*Real.exp (1/J)*X := ⟨hR.1.le,hR.2⟩
        rw [ite_eq_left (Or.inr hR),ite_eq_left hRc]
        split_ifs <;> simp only [zero_add,le_add_iff_nonneg_left,_root_.norm_nonneg,le_refl]
      · rw [ite_eq_right (not_or.mpr ⟨hL,hR⟩)]
        split_ifs <;> positivity
  apply hs.trans
  apply add_le_add
  · apply idealMangoldt_annulus_mass _ χ hχ hlo hAX
    intro ν hν
    exact (Finset.mem_filter.mp hν).2
  · apply idealMangoldt_annulus_mass _ χ hχ (by linarith) hXB
    intro ν hν
    exact (Finset.mem_filter.mp hν).2

end CubicFirstMoment

end

end OAI
