import OAI.Analysis.LipschitzHilbert.Fourier.FiniteVerticalBins
import OAI.Analysis.LipschitzHilbert.Fourier.SchwartzVerticalProjection

namespace OAI

/-! Cardinality-independent square-function energy for the finite vertical bins. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem binSquareStep_nonneg (x : ℝ) : 0≤binSquareStep x := sq_nonneg _

theorem binSquareStep_le_one (x : ℝ) : binSquareStep x≤1 := by
  exact Real.sin_sq_le_one _

theorem verticalBinProfile_sum_norm_sq_le (x : ℝ) (N : ℕ) :
    (∑ n∈Finset.range N, ‖verticalBinProfile (x-(n:ℝ))‖^2)≤1 := by
  have hn (y : ℝ) : ‖verticalBinProfile y‖^2=verticalBinProfileReal y^2 := by
    simp only [verticalBinProfile_apply,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  simp_rw [hn]
  rw [verticalBinProfileReal_sum_sq]
  exact (sub_le_self _ (binSquareStep_nonneg _)).trans (binSquareStep_le_one _)

theorem verticalBinWindow_sum_norm_sq_le (K : ℕ) (W : ℝ) (hW : 0<W)
    (eta : ℝ) (I : Finset ℕ) (hI : I⊆Finset.range (2*K+1)) :
    (∑ n∈I, ‖verticalBinWindow K W n eta‖^2)≤1 := by
  calc
    _ ≤ ∑ n∈Finset.range (2*K+1), ‖verticalBinWindow K W n eta‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hI (fun _ _ _ => sq_nonneg _)
    _ ≤ 1 := by
      simp_rw [verticalBinWindow_apply K W hW]
      exact verticalBinProfile_sum_norm_sq_le (W*eta+K) (2*K+1)

theorem planar_integral_norm_sq_fourier (f : SchwartzMap (ℝ×ℝ) ℂ) :
    (∫ omega, ‖planarFourier f omega‖^2 ∂planeMeasure)=∫ z, ‖f z‖^2 ∂planeMeasure := by
  have h := planar_integral_inner_fourier f f
  simp only [inner_self_eq_norm_sq_to_K,←RCLike.ofReal_pow] at h
  change (∫ omega, ((‖planarFourier f omega‖^2 : ℝ) : ℂ) ∂planeMeasure)=
    (∫ z, ((‖f z‖^2 : ℝ) : ℂ) ∂planeMeasure) at h
  simp only [integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

theorem verticalBin_schwartz_energy_le (f : SchwartzMap (ℝ×ℝ) ℂ)
    (K : ℕ) (W : ℝ) (hW : 0<W) (I : Finset ℕ) (hI : I⊆Finset.range (2*K+1)) :
    (∑ n∈I, ∫ z, ‖schwartzVerticalProjection verticalBinProfile W
      (verticalBinCenter K W n) f z‖^2 ∂planeMeasure)≤∫ z, ‖f z‖^2 ∂planeMeasure := by
  have hp (n : ℕ) := planar_integral_norm_sq_fourier
    (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter K W n) f)
  have hpi (n : ℕ) : Integrable (fun omega =>
      ‖planarFourier (schwartzVerticalProjection verticalBinProfile W
        (verticalBinCenter K W n) f) omega‖^2) planeMeasure := by
    simpa only [planarFourierSchwartz_apply] using
      ((planarFourierSchwartz (schwartzVerticalProjection verticalBinProfile W
        (verticalBinCenter K W n) f)).memLp 2 planeMeasure).integrable_norm_pow (by decide : 2≠0)
  calc
    _ = ∑ n∈I, ∫ omega, ‖planarFourier (schwartzVerticalProjection
        verticalBinProfile W (verticalBinCenter K W n) f) omega‖^2 ∂planeMeasure := by
      exact Finset.sum_congr rfl (fun n _ => (hp n).symm)
    _ = ∫ omega, ∑ n∈I, ‖planarFourier (schwartzVerticalProjection
        verticalBinProfile W (verticalBinCenter K W n) f) omega‖^2 ∂planeMeasure :=
      (integral_finsetSum I (fun n _ => hpi n)).symm
    _ ≤ ∫ omega, ‖planarFourier f omega‖^2 ∂planeMeasure := by
      apply integral_mono (integrable_finsetSum I (fun n _ => hpi n))
      · simpa only [planarFourierSchwartz_apply] using
          ((planarFourierSchwartz f).memLp 2 planeMeasure).integrable_norm_pow (by decide : 2≠0)
      · intro omega
        simp only [schwartzVerticalProjection_fourier,norm_mul,mul_pow]
        rw [←Finset.sum_mul]
        exact mul_le_of_le_one_left (sq_nonneg _) (verticalBinWindow_sum_norm_sq_le
          K W hW omega.2 I hI)
    _ = _ := planar_integral_norm_sq_fourier f

end LipschitzHilbert.PacketRepresentation

end

end OAI
