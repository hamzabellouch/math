import OAI.Analysis.StrictMeans.SquaredPotential

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma fderiv_apply_of_line {u : E → ℝ} {p d : E} {a : ℝ}
    (hu : DifferentiableAt ℝ u p)
    (ha : HasDerivAt (fun t : ℝ=>u (p+t•d)) a 0) : fderiv ℝ u p d=a := by
  have hl : HasDerivAt (fun t : ℝ=>p+t•d) d 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const d).const_add p
  have hc := hu.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) hl (by simp)
  exact hc.unique ha

lemma derivative_homotopy_regular {g : E → F} {H : E →L[ℝ] F} {p : E}
    (hg : HasFDerivAt g H p) (hp : g p=0) {m : ℝ} (hm : 0 < m)
    (hH : ∀ d, m*‖d‖≤‖H d‖) :
    ∀ᶠ z in 𝓝 p, z≠p → ∀ t∈Icc (0:ℝ) 1,
      (1-t)•g z+t•H (z-p)≠0 := by
  filter_upwards [hg.isLittleO.bound (show 0 < m/2 by positivity)] with z hz
  intro hzp t ht he
  have hd : 0<‖z-p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzp)
  have herr : ‖g z-H (z-p)‖≤ m/2*‖z-p‖ := by simpa only [hp,sub_zero] using hz
  have hid : H (z-p) = -(1-t)•(g z-H (z-p)) := by
    have hh : (1-t)•(g z-H (z-p))+H (z-p) = (1-t)•g z+t•H (z-p) := by
      simp only [smul_sub,sub_smul,one_smul]
      abel
    rw [he] at hh
    exact (eq_neg_of_add_eq_zero_right hh).trans (by simp only [neg_smul])
  have hcoef : |-(1-t)|≤1 := by rw [abs_neg,abs_of_nonneg (by linarith [ht.2])]; linarith [ht.1]
  have hn : ‖H (z-p)‖≤ m/2*‖z-p‖ := calc
    ‖H (z-p)‖ = |-(1-t)| * ‖g z-H (z-p)‖ := by
      calc
        ‖H (z-p)‖ = ‖-(1-t)•(g z-H (z-p))‖ := congrArg norm hid
        _ = _ := by rw [norm_smul,Real.norm_eq_abs]
    _ ≤ 1*‖g z-H (z-p)‖ := mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
    _ ≤ m/2*‖z-p‖ := by simpa using herr
  have := hH (z-p)
  nlinarith

def quadratic (a b c : ℝ) (z : ℂ) : ℝ :=
  (a*z.re^2+2*b*z.re*z.im+c*z.im^2)/2

def quadraticFamily (A B C : ℝ → ℝ) (p : ℂ) (q : ℝ × ℂ) : ℝ :=
  quadratic (A q.1) (B q.1) (C q.1) (q.2-p)

lemma quadraticFamily_contDiff {A B C : ℝ → ℝ} {n : WithTop ℕ∞}
    (hA : ContDiff ℝ n A) (hB : ContDiff ℝ n B) (hC : ContDiff ℝ n C) (p : ℂ) :
    ContDiff ℝ n (quadraticFamily A B C p) := by
  have hr : ContDiff ℝ n (fun q : ℝ × ℂ => (q.2-p).re) :=
    Complex.reCLM.contDiff.comp (contDiff_snd.sub contDiff_const)
  have hi : ContDiff ℝ n (fun q : ℝ × ℂ => (q.2-p).im) :=
    Complex.imCLM.contDiff.comp (contDiff_snd.sub contDiff_const)
  exact ((((hA.comp contDiff_fst).mul (hr.pow 2)).add
    (((contDiff_const.mul (hB.comp contDiff_fst)).mul hr).mul hi)).add
    ((hC.comp contDiff_fst).mul (hi.pow 2))).div_const 2

lemma quadraticFamily_dx {A B C : ℝ → ℝ} {p : ℂ} {q : ℝ × ℂ}
    (hu : DifferentiableAt ℝ (quadraticFamily A B C p) q) :
    fderiv ℝ (quadraticFamily A B C p) q (0,1) =
      A q.1*(q.2-p).re+B q.1*(q.2-p).im := by
  apply fderiv_apply_of_line hu
  have he : (fun t : ℝ=>quadraticFamily A B C p (q+t•(0,1))) =
      (fun t : ℝ=>(A q.1*((q.2-p).re+t)^2+
        2*B q.1*((q.2-p).re+t)*(q.2-p).im+C q.1*(q.2-p).im^2)/2) := by
    funext t
    simp [quadraticFamily,quadratic,Complex.sub_re,Complex.sub_im]
    ring
  rw [he]
  convert (((((hasDerivAt_id (0:ℝ)).const_add ((q.2-p).re)).pow 2).const_mul (A q.1)).add
    ((((hasDerivAt_id (0:ℝ)).const_add ((q.2-p).re)).const_mul (2*B q.1)).mul_const ((q.2-p).im))).add_const
      (C q.1*(q.2-p).im^2) |>.div_const 2 using 1 <;> (first | rfl | (simp only [id_eq]; ring))

lemma quadraticFamily_dy {A B C : ℝ → ℝ} {p : ℂ} {q : ℝ × ℂ}
    (hu : DifferentiableAt ℝ (quadraticFamily A B C p) q) :
    fderiv ℝ (quadraticFamily A B C p) q (0,Complex.I) =
      B q.1*(q.2-p).re+C q.1*(q.2-p).im := by
  apply fderiv_apply_of_line hu
  have he : (fun t : ℝ=>quadraticFamily A B C p (q+t•(0,Complex.I))) =
      (fun t : ℝ=>(A q.1*(q.2-p).re^2+
        2*B q.1*(q.2-p).re*((q.2-p).im+t)+C q.1*((q.2-p).im+t)^2)/2) := by
    funext t
    simp [quadraticFamily,quadratic,Complex.sub_re,Complex.sub_im]
    ring
  rw [he]
  convert (((((hasDerivAt_id (0:ℝ)).const_add ((q.2-p).im)).const_mul
    (2*B q.1*(q.2-p).re)).const_add (A q.1*(q.2-p).re^2)).add
    ((((hasDerivAt_id (0:ℝ)).const_add ((q.2-p).im)).pow 2).const_mul (C q.1))).div_const 2 using 1 <;> (first | rfl | (simp only [id_eq]; ring))

lemma quadraticFamily_regular {A B C : ℝ → ℝ} {p : ℂ} {q : ℝ × ℂ}
    (hu : ContDiffAt ℝ 1 (quadraticFamily A B C p) q)
    (hD : A q.1*C q.1-(B q.1)^2≠0) (hp : q.2≠p) :
    ∃ L : (ℝ × ℂ) →L[ℝ] ℝ, HasStrictFDerivAt (quadraticFamily A B C p) L q ∧
      (L (0,1)≠0 ∨ L (0,Complex.I)≠0) := by
  refine ⟨_,hu.hasStrictFDerivAt one_ne_zero,?_⟩
  rw [quadraticFamily_dx (hu.differentiableAt one_ne_zero),
    quadraticFamily_dy (hu.differentiableAt one_ne_zero)]
  by_contra hn
  obtain ⟨hx,hy⟩ := not_or.mp hn
  simp only [not_not] at hx hy
  have hxr : (q.2-p).re=0 := by
    apply (mul_eq_zero.mp (show (A q.1*C q.1-(B q.1)^2)*(q.2-p).re=0 by
      linear_combination C q.1 * hx - B q.1 * hy)).resolve_left hD
  have hyr : (q.2-p).im=0 := by
    apply (mul_eq_zero.mp (show (A q.1*C q.1-(B q.1)^2)*(q.2-p).im=0 by
      linear_combination A q.1 * hy - B q.1 * hx)).resolve_left hD
  exact hp (sub_eq_zero.mp (Complex.ext (by simpa using hxr) (by simpa using hyr)))

end
end StrictInverseFirstPower.Grid

end

end OAI
