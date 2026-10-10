import OAI.Analysis.LipschitzHilbert.Estimates.HorizontalHilbertPairing
import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeDisparity

namespace OAI

/-! Actual integral sizes of restricted Schwartz tests and the elementary
mass inequalities used to combine the scalar endpoint remainders. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem restrictedSchwartz_l1 (f : SchwartzMap (ℝ×ℝ) ℂ) (hf : ∀ z, ‖f z‖≤1)
    (A : Set (ℝ×ℝ)) (hA : MeasurableSet A) (hAfin : planeMeasure A≠∞)
    (hsupp : ∀ z, z∉A → f z=0) :
    (∫ z, ‖f z‖ ∂planeMeasure)≤planeMeasure.real A := by
  have hi : Integrable (A.indicator (fun _ : ℝ×ℝ => (1:ℝ))) planeMeasure :=
    (integrableOn_const hAfin).integrable_indicator hA
  calc
    _ ≤ ∫ z, A.indicator (fun _ : ℝ×ℝ => (1:ℝ)) z ∂planeMeasure := by
      apply integral_mono f.integrable.norm hi
      intro z
      by_cases hz : z∈A
      · simpa only [Set.indicator_of_mem hz] using hf z
      · simp only [Set.indicator_of_notMem hz,hsupp z hz,norm_zero,le_refl]
    _ = _ := by simpa only [smul_eq_mul,mul_one] using integral_indicator_const (1:ℝ) hA

theorem restrictedSchwartz_energy (f : SchwartzMap (ℝ×ℝ) ℂ) (hf : ∀ z, ‖f z‖≤1)
    (A : Set (ℝ×ℝ)) (hA : MeasurableSet A) (hAfin : planeMeasure A≠∞)
    (hsupp : ∀ z, z∉A → f z=0) :
    (∫ z, ‖f z‖^2 ∂planeMeasure)≤planeMeasure.real A := by
  have h := schwartz_power_le_l1 f hf 2 (by norm_num)
  rw [show (fun z : ℝ×ℝ => ‖f z‖^(2:ℝ))=(fun z => ‖f z‖^2) by
    funext z; exact Real.rpow_two _] at h
  exact h.trans (restrictedSchwartz_l1 f hf A hA hAfin hsupp)

theorem min_mass_le_sqrt (F E : ℝ) (hF : 0≤F) (hE : 0≤E) :
    min (4*F) E≤4*(Real.sqrt F*Real.sqrt E) := by
  have hmin : min F E≤Real.sqrt F*Real.sqrt E := by
    rcases le_total F E with h | h
    · rw [min_eq_left h]
      calc
        F = Real.sqrt F*Real.sqrt F := (Real.mul_self_sqrt hF).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) (Real.sqrt_nonneg _)
    · rw [min_eq_right h]
      calc
        E = Real.sqrt E*Real.sqrt E := (Real.mul_self_sqrt hE).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt h) (Real.sqrt_nonneg _)
  calc
    min (4*F) E ≤ min (4*F) (4*E) := min_le_min le_rfl (by linarith)
    _ = 4*min F E := (mul_min_of_nonneg F E (by norm_num)).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hmin (by norm_num)

theorem reverse_mass_bound (F E : ℝ) (hF : 0<F) (hE : 0<E) (hEF : E≤F) :
    E≤Real.sqrt (F*E)*(E/F)^(9/20:ℝ) := by
  let r := E/F
  have hr : 0<r := div_pos hE hF
  have hr1 : r≤1 := (div_le_one hF).2 hEF
  have heq : E=F*r := by dsimp [r]; field_simp
  have hs : Real.sqrt (F*E)=F*Real.sqrt r := by
    rw [heq,←mul_assoc,←pow_two,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos hF]
  change E≤Real.sqrt (F*E)*r^(9/20:ℝ)
  rw [hs,Real.sqrt_eq_rpow,heq,mul_assoc,←Real.rpow_add hr]
  apply mul_le_mul_of_nonneg_left _ hF.le
  exact Real.self_le_rpow_of_le_one hr.le hr1 (by norm_num)

end LipschitzHilbert.PacketRepresentation

end

end OAI
