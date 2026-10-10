import OAI.NumberTheory.CubicMoment.Estimates.IdealMangoldtDyadic
import OAI.NumberTheory.CubicMoment.Estimates.DyadicReconstruction

namespace OAI

/-! Complete ideal von Mangoldt prefixes, exact half-open dyadic
increments, and the cost of their closed lower endpoints. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def idealMangoldtSum (χ : EisensteinIdealExponent → ℂ) (X : ℝ) : ℂ :=
  ∑ ν ∈ fullIdealBall X, ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν

lemma fullIdealBall_sum_on {A B : ℝ} (hAB : A ≤ B)
    (f : EisensteinIdealExponent → ℂ) :
    (∑ ν ∈ fullIdealBall A, f ν) =
      ∑ ν ∈ fullIdealBall B, if idealExponentNorm ν ≤ A then f ν else 0 := by
  have hs : fullIdealBall A = (fullIdealBall B).filter (fun ν => idealExponentNorm ν ≤ A) := by
    ext ν
    simp only [Finset.mem_filter,mem_fullIdealBall]
    exact ⟨fun h => ⟨h.trans hAB,h⟩,And.right⟩
  rw [hs,Finset.sum_filter]

lemma idealMangoldtSum_zero_small (χ : EisensteinIdealExponent → ℂ)
    {X : ℝ} (hX : X < 1) : idealMangoldtSum χ X = 0 := by
  unfold idealMangoldtSum
  apply Finset.sum_eq_zero
  intro ν hν
  exact ((not_lt_of_ge ((idealExponentNorm_ge_one ν).trans (mem_fullIdealBall.mp hν))) hX).elim

lemma idealMangoldtSum_dyadic (χ : EisensteinIdealExponent → ℂ) {X : ℝ} (hX : 0 ≤ X) :
    idealMangoldtSum χ (2*X)-idealMangoldtSum χ X = idealMangoldtDyadic χ X-
      ∑ ν ∈ fullIdealBall (2*X) with idealExponentNorm ν = X,
        ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν := by
  unfold idealMangoldtSum idealMangoldtDyadic
  rw [fullIdealBall_sum_on (show X ≤ 2*X by linarith),
    ←Finset.sum_sub_distrib,Finset.sum_filter,Finset.sum_filter,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ν hν
  by_cases he : idealExponentNorm ν = X
  · simp [he]
  · by_cases hlo : idealExponentNorm ν ≤ X
    · have hn : ¬X ≤ idealExponentNorm ν := fun h => he (le_antisymm hlo h)
      simp [he,hlo,hn]
    · have hl : X ≤ idealExponentNorm ν := (lt_of_not_ge hlo).le
      simp [he,hlo,hl]

lemma idealMangoldt_boundary_bound (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {X B : ℝ} (hX : 1 ≤ X) :
    ‖∑ ν ∈ fullIdealBall B with idealExponentNorm ν = X,
      ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν‖ ≤
      8*Real.sqrt X*Real.log X := by
  apply (norm_sum_le _ _).trans
  have hh := idealMangoldt_annulus_mass
    ((fullIdealBall B).filter (fun ν => idealExponentNorm ν = X)) χ hχ hX le_rfl (by
      intro ν hν
      have he := (Finset.mem_filter.mp hν).2
      exact ⟨he.ge,he.le⟩)
  convert hh using 1
  ring

lemma idealMangoldtSum_norm_bound (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {X : ℝ} (hX : 1 ≤ X) :
    ‖idealMangoldtSum χ X‖ ≤ 8*X*Real.log X := by
  have hh := idealMangoldt_annulus_mass (fullIdealBall X) χ hχ (by norm_num : (1:ℝ) ≤ 1) hX
    (fun ν hν => ⟨idealExponentNorm_ge_one ν,mem_fullIdealBall.mp hν⟩)
  have hs : Real.sqrt X ≤ X := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by linarith,by nlinarith⟩
  calc
    _ ≤ ∑ ν ∈ fullIdealBall X, ‖((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν‖ := norm_sum_le _ _
    _ ≤ 4*(X-1+Real.sqrt X+Real.sqrt 1)*Real.log X := hh
    _ ≤ _ := by
      norm_num only [Real.sqrt_one]
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.log_nonneg hX)

end CubicFirstMoment

end

end OAI
