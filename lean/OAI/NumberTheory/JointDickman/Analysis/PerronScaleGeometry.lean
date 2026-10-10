import OAI.NumberTheory.JointDickman.Analysis.ZetaRectangleLog
import OAI.NumberTheory.JointDickman.Analysis.ZetaPerronScale

namespace OAI

/-! # Compatible logarithms and geometry at the concrete Perron scale -/
namespace JointDickman
open Set Complex

theorem zeta_rectangle_log_below : ∃ A₀ : ℝ, 0 < A₀ ∧ A₀ ≤ 1/4 ∧
    ∀ A : ℝ, 0 < A → A ≤ A₀ → ∀ T : ℝ, 0 < T →
      ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f (zetaOpenRectangle (zetaContourWidth A T) T) ∧
        f 1 = 0 ∧ ∀ s ∈ zetaOpenRectangle (zetaContourWidth A T) T,
          exp (f s) = zetaPoleFactor s := by
  obtain ⟨A₀,hA₀,hA₀4,hlog⟩ := zeta_rectangle_log
  refine ⟨A₀,hA₀,hA₀4,?_⟩
  intro A _ hAA T hT
  obtain ⟨f,hf,hf1,he⟩ := hlog T hT
  have hw : zetaContourWidth A T ≤ zetaContourWidth A₀ T := by
    unfold zetaContourWidth
    exact div_le_div_of_nonneg_right hAA (pow_nonneg (by
      have := Real.log_pos (show 1 < T+3 by linarith)
      linarith) _)
  have hsub : zetaOpenRectangle (zetaContourWidth A T) T ⊆
      zetaOpenRectangle (zetaContourWidth A₀ T) T := by
    intro s hs
    exact ⟨⟨by linarith [hs.1.1],hs.1.2⟩,hs.2⟩
  exact ⟨f,hf.mono hsub,hf1,fun s hs => he s (hsub hs)⟩

theorem perronScale_height_gt_three {q : ℝ} (hq : 8 ≤ q) :
    3 < Real.exp q/2 := by
  linarith [Real.add_one_le_exp q]

theorem perronScaleWidth_le_log_height {A q : ℝ} (hA : 0 < A) (hq : 8 ≤ q) :
    perronScaleWidth A q ≤ A/Real.log (Real.exp q/2) := by
  have hq0 : 0 < q := by linarith
  have hT := perronScale_height_gt_three hq
  have hlog : 0 < Real.log (Real.exp q/2) := Real.log_pos (by linarith)
  have hlogq : Real.log (Real.exp q/2) ≤ q := by
    calc
      _ ≤ Real.log (Real.exp q) := Real.log_le_log (by positivity) (by linarith [Real.exp_pos q])
      _ = q := Real.log_exp q
  apply (le_div_iff₀ hlog).mpr
  calc
    perronScaleWidth A q*Real.log (Real.exp q/2) ≤ perronScaleWidth A q*q :=
      mul_le_mul_of_nonneg_left hlogq (perronScaleWidth_pos hA).le
    _ ≤ (A/(4*q))*q :=
      mul_le_mul_of_nonneg_right (perronScaleWidth_upper hA.le (by linarith)) hq0.le
    _ = A/4 := by field_simp
    _ ≤ A := by linarith

theorem perronScaleWidth_four_le {A q : ℝ} (hA : 0 < A) (hq : 2 ≤ q) :
    4*perronScaleWidth A q ≤ A := by
  have hq0 : 0 < q := by linarith
  calc
    _ ≤ 4*(A/(4*q)) := mul_le_mul_of_nonneg_left (perronScaleWidth_upper hA.le hq) (by norm_num)
    _ = A/q := by ring
    _ ≤ A := div_le_self hA.le (by linarith)

theorem perron_inner_contour_mem {η c T : ℝ} (hη : 0 < η) (hη1 : η ≤ 1/4)
    (hc : c ≤ η) (hT : 0 < T) {w : ℂ}
    (hr : -η ≤ w.re ∧ w.re ≤ c) (hi : |w.im| ≤ T) :
    1+w ∈ zetaOpenRectangle (4*η) (2*T) := by
  have him := abs_le.mp hi
  change (1-4*η < (1+w).re ∧ (1+w).re < 2) ∧
    (-(2*T) < (1+w).im ∧ (1+w).im < 2*T)
  simp only [add_re,one_re,add_im,one_im,zero_add]
  constructor <;> constructor <;> linarith [hr.1,hr.2,him.1,him.2]

end JointDickman

end OAI
