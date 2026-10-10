import OAI.NumberTheory.DirichletL.Reflection.KernelSeparation

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform
noncomputable section

def reciprocalWindow (w : ℝ→ℂ) (α M : ℝ) (y : ℝ) : ℂ :=
  (Real.exp (-α*M):ℂ)*(w y*(Real.exp (-α*y):ℂ))

lemma reciprocalWindow_norm_le_one (w : ℝ→ℂ) (α M : ℝ) (hα : 0≤α)
    (hw : ∀ y, ‖w y‖≤1) (hs : ∀ y, w y≠0 → -M≤y) (y : ℝ) :
    ‖reciprocalWindow w α M y‖≤1 := by
  by_cases hy : w y=0
  · simp [reciprocalWindow,hy]
  · have he : Real.exp (-α*M)*Real.exp (-α*y) ≤ 1 := by
      rw [← Real.exp_add,← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hα (show 0≤M+y by linarith [hs y hy])]
    simp only [reciprocalWindow,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-α*M)*(1*Real.exp (-α*y)) := by gcongr; exact hw y
      _ ≤ 1 := by simpa only [one_mul] using he

lemma reciprocalWindow_support (w : ℝ→ℂ) (α M y : ℝ) :
    reciprocalWindow w α M y≠0 → w y≠0 := by
  intro h hw
  apply h
  simp [reciprocalWindow,hw]

lemma reciprocalWindow_reconstruct (w : ℝ→ℂ) (α M y : ℝ) :
    w y*(Real.exp (-α*y):ℂ) =
      (Real.exp (α*M):ℂ)*reciprocalWindow w α M y := by
  unfold reciprocalWindow
  rw [← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
  simp

lemma reciprocal_norm_log (Q q : ℝ) (hQ : 0<Q) (hq : 0<q) :
    Real.exp (-(1/2:ℝ)*Real.log (q/Q)) = Real.sqrt Q/Real.sqrt q := by
  rw [show -(1/2:ℝ)*Real.log (q/Q) = Real.log (q/Q)*(-(1/2:ℝ)) by ring,
    ← Real.rpow_def_of_pos (div_pos hq hQ),Real.div_rpow hq.le hQ.le,
    Real.rpow_neg hq.le,Real.rpow_neg hQ.le,← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow]
  field_simp

lemma reciprocal_cube_log (Q q : ℝ) (hQ : 0<Q) (hq : 0<q) :
    Real.exp (-Real.log (q/Q)) = Q/q := by
  rw [Real.exp_neg,Real.exp_log (div_pos hq hQ),inv_div]

def reciprocalKernelWindows (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ) : Fin 4→ℝ→ℂ :=
  ![windows 0,windows 1,reciprocalWindow (windows 2) (1/2) (M 2),
    reciprocalWindow (windows 3) 1 (M 3)]

lemma reciprocalKernelWindows_norm (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hw : ∀ i y, ‖windows i y‖≤1)
    (hs : ∀ i y, windows i y≠0 → |y|≤M i) :
    ∀ i y, ‖reciprocalKernelWindows windows M i y‖≤1 := by
  intro i y
  fin_cases i
  · exact hw 0 y
  · exact hw 1 y
  · exact reciprocalWindow_norm_le_one _ _ _ (by norm_num) (hw 2)
      (fun y hy => (abs_le.mp (hs 2 y hy)).1) y
  · exact reciprocalWindow_norm_le_one _ _ _ (by norm_num) (hw 3)
      (fun y hy => (abs_le.mp (hs 3 y hy)).1) y

lemma reciprocalKernelWindows_support (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hs : ∀ i y, windows i y≠0 → |y|≤M i) :
    ∀ i y, reciprocalKernelWindows windows M i y≠0 → |y|≤M i := by
  intro i y hy
  fin_cases i
  · exact hs 0 y hy
  · exact hs 1 y hy
  · exact hs 2 y (reciprocalWindow_support _ _ _ _ hy)
  · exact hs 3 y (reciprocalWindow_support _ _ _ _ hy)

lemma reciprocal_window_product (windows : Fin 4→ℝ→ℂ) (M y : Fin 4→ℝ) :
    (∏ i, windows i (y i)) *
      ((Real.exp (-(1/2:ℝ)*y 2):ℂ)*(Real.exp (-y 3):ℂ)) =
    (Real.exp (M 2/2+M 3):ℂ)*(∏ i, reciprocalKernelWindows windows M i (y i)) := by
  have h2 := reciprocalWindow_reconstruct (windows 2) (1/2) (M 2) (y 2)
  have h3 := reciprocalWindow_reconstruct (windows 3) 1 (M 3) (y 3)
  have hp : (Real.exp (M 2/2+M 3):ℂ) =
      (Real.exp ((1/2:ℝ)*M 2):ℂ)*(Real.exp (1*M 3):ℂ) := by
    rw [← Complex.ofReal_mul,← Real.exp_add]
    congr 2
    ring
  rw [hp]
  simp only [reciprocalKernelWindows,Fin.prod_univ_succ,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Fin.prod_univ_zero,mul_one]
  simp only [Fin.succ,Fin.val_mk]
  simp only [one_mul,neg_one_mul] at h3 ⊢
  change (windows 0 (y 0)*(windows 1 (y 1)*(windows 2 (y 2)*windows 3 (y 3)))) *
    ((Real.exp (-(1/2:ℝ)*y 2):ℂ)*(Real.exp (-y 3):ℂ)) =
    ((Real.exp ((1/2:ℝ)*M 2):ℂ)*(Real.exp (M 3):ℂ))*
      (windows 0 (y 0)*(windows 1 (y 1)*
        (reciprocalWindow (windows 2) (1/2) (M 2) (y 2)*
         reciprocalWindow (windows 3) 1 (M 3) (y 3))))
  calc
    _ = windows 0 (y 0)*windows 1 (y 1)*
      (windows 2 (y 2)*(Real.exp (-(1/2:ℝ)*y 2):ℂ))*
      (windows 3 (y 3)*(Real.exp (-y 3):ℂ)) := by ring
    _ = _ := by rw [h2,h3]; ring

theorem reciprocal_source_window_identity (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (QK QP Qn Qb k p n b r : ℝ) (hQn : 0<Qn) (hQb : 0<Qb)
    (hn : 0<n) (hb : 0<b) (hr : 0<r) :
    (∏ i, windows i (kernelLogCoordinates QK QP Qn Qb k p n b i)) /
      ((r*Real.sqrt n*b:ℝ):ℂ) =
    ((Real.exp (M 2/2+M 3)/(r*Real.sqrt Qn*Qb):ℝ):ℂ) *
      (∏ i, reciprocalKernelWindows windows M i (kernelLogCoordinates QK QP Qn Qb k p n b i)) := by
  have hp := reciprocal_window_product windows M (kernelLogCoordinates QK QP Qn Qb k p n b)
  change (∏ i, windows i (kernelLogCoordinates QK QP Qn Qb k p n b i))*
      ((Real.exp (-(1/2:ℝ)*Real.log (n/Qn)):ℂ)*(Real.exp (-Real.log (b/Qb)):ℂ)) = _ at hp
  rw [reciprocal_norm_log Qn n hQn hn,reciprocal_cube_log Qb b hQb hb] at hp
  have he := congrArg (fun z : ℂ => z/((r*Real.sqrt Qn*Qb:ℝ):ℂ)) hp
  have hn0 := (Real.sqrt_pos.mpr hn).ne'
  have hQn0 := (Real.sqrt_pos.mpr hQn).ne'
  simp only [Complex.ofReal_mul,Complex.ofReal_div] at he ⊢
  have hrC : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hbC : (b:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have hQbC : (Qb:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hQb.ne'
  have hnC : (Real.sqrt n:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hn0
  have hQnC : (Real.sqrt Qn:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hQn0
  convert he using 1 <;> field_simp

end
end SevenEighths.InverseReflectedPhase

end OAI
