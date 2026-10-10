import OAI.Geometry.Immersion.ClosedSurface.SecondForms
import OAI.Geometry.Immersion.ClosedSurface.PhaseGrid

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry

lemma coordDeriv_comp_smooth {n : ℕ} {F : RField n} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (w p : Base) :
    coordDeriv w (F ∘ φ) p = fderiv ℝ F (φ p) (coordDeriv w φ p) := by
  simp only [coordDeriv,fderiv_comp p (hF.differentiable (by simp) _) (hφ.differentiable (by simp) _),
    ContinuousLinearMap.comp_apply]

lemma second_coordDeriv_comp_smooth {n : ℕ} {F : RField n} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (v w p : Base) :
    coordDeriv v (coordDeriv w (F ∘ φ)) p =
      coordDeriv (fderiv ℝ φ p v) (coordDeriv (fderiv ℝ φ p w) F) (φ p) +
      fderiv ℝ F (φ p) (coordDeriv v (coordDeriv w φ) p) := by
  have hDF : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (m := ∞) (by simp)
  have hD1 := ((hDF.differentiable (by simp)) (φ p)).hasFDerivAt.comp p
    ((hφ.differentiable (by simp)) p).hasFDerivAt
  have hD2 := ((contDiffAt_coordDeriv (p := p) hφ.contDiffAt w).differentiableAt (by simp)).hasFDerivAt
  have hp := hD1.clm_apply hD2
  have he : (fun q => (fderiv ℝ F ∘ φ) q (coordDeriv w φ q)) = coordDeriv w (F ∘ φ) := by
    funext q
    exact (coordDeriv_comp_smooth hF hφ w q).symm
  rw [he] at hp
  have heval := congrArg (fun L => L v) hp.fderiv
  rw [real_second_coordDeriv ((hDF.differentiable (by simp)) (φ p))]
  simpa only [coordDeriv,add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,Function.comp_apply,add_comm] using heval

lemma realNormalPart_fderiv {F : RField 4} (p v : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0) :
    realNormalPart (coordDeriv dx F p) (coordDeriv dy F p) (fderiv ℝ F p v) = 0 := by
  change realNormalPart (coordDeriv dx F p) (coordDeriv dy F p) (coordDeriv v F p) = 0
  conv_lhs => arg 3; rw [coordDeriv_eq_basis F v p]
  have hl := realNormalPart_linear (coordDeriv dx F p) (coordDeriv dy F p)
  rw [hl.map_add,hl.map_smul,hl.map_smul,realNormalPart_self_left _ _ hD,
    realNormalPart_self_right _ _ hD,smul_zero,smul_zero,add_zero]



lemma realSecondForm_comp_smooth {F : RField 4} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (v w p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : (fderiv ℝ φ p dx).1*(fderiv ℝ φ p dy).2-
      (fderiv ℝ φ p dx).2*(fderiv ℝ φ p dy).1 ≠ 0) :
    realSecondForm (F ∘ φ) v w p =
      realSecondForm F (fderiv ℝ φ p v) (fderiv ℝ φ p w) (φ p) := by
  unfold realSecondForm
  rw [coordDeriv_comp_smooth hF hφ,coordDeriv_comp_smooth hF hφ,
    second_coordDeriv_comp_smooth hF hφ]
  change realNormalPart (coordDeriv (fderiv ℝ φ p dx) F (φ p))
    (coordDeriv (fderiv ℝ φ p dy) F (φ p)) _ = _
  rw [coordDeriv_eq_basis F (fderiv ℝ φ p dx),coordDeriv_eq_basis F (fderiv ℝ φ p dy),
    realNormalPart_change_basis _ _ _ _ _ _ _ hD hdet]
  rw [(realNormalPart_linear _ _).map_add,realNormalPart_fderiv _ _ hD,add_zero]

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry

def coordDet (A : Base →L[ℝ] Base) : ℝ :=
  (A dx).1*(A dy).2-(A dx).2*(A dy).1

def pullCovector (A : Base →L[ℝ] Base) (ξ : Base) : Base :=
  (ξ.1*(A dx).1+ξ.2*(A dx).2,ξ.1*(A dy).1+ξ.2*(A dy).2)

lemma linear_apply_basis (A : Base →L[ℝ] Base) (v : Base) :
    A v = v.1 • A dx + v.2 • A dy := by
  calc A v = A (v.1 • dx + v.2 • dy) := congrArg A (base_eq_basis v)
       _ = _ := by simp

lemma rotated_pullCovector (A : Base →L[ℝ] Base) (ξ : Base) :
    A (-(pullCovector A ξ).2,(pullCovector A ξ).1) = coordDet A • (-ξ.2,ξ.1) := by
  rw [linear_apply_basis]
  ext <;> simp [pullCovector,coordDet,Prod.smul_mk] <;> ring

lemma phase_length_comp_smooth {F : RField 4} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (ξ p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : coordDet (fderiv ℝ φ p) ≠ 0) :
    secondQuadratic (realSecondTensor (F ∘ φ) p)
      (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1) =
      (coordDet (fderiv ℝ φ p))^2 •
        secondQuadratic (realSecondTensor F (φ p)) (-ξ.2,ξ.1) := by
  rw [← realSecondForm_quadratic (hF.comp hφ),realSecondForm_comp_smooth hF hφ _ _ _ hD hdet,
    rotated_pullCovector,realSecondForm_quadratic hF,secondQuadratic_smul]

lemma norm_phase_length_comp_smooth {F : RField 4} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (ξ p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : coordDet (fderiv ℝ φ p) ≠ 0) :
    ‖secondQuadratic (realSecondTensor (F ∘ φ) p)
      (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1)‖ =
      (coordDet (fderiv ℝ φ p))^2 *
        ‖secondQuadratic (realSecondTensor F (φ p)) (-ξ.2,ξ.1)‖ := by
  rw [phase_length_comp_smooth hF hφ ξ p hD hdet,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]

lemma norm_realSecondForm_le {F : RField 4} (hF : ContDiff ℝ ∞ F) (v w p : Base) :
    ‖realSecondForm F v w p‖ ≤ 4*‖realSecondTensor F p‖*‖v‖*‖w‖ := by
  have h11 : |v.1*w.1| ≤ ‖v‖*‖w‖ := by
    rw [abs_mul]
    exact mul_le_mul (by simpa using norm_fst_le v) (by simpa using norm_fst_le w)
      (abs_nonneg _) (norm_nonneg _)
  have h22 : |v.2*w.2| ≤ ‖v‖*‖w‖ := by
    rw [abs_mul]
    exact mul_le_mul (by simpa using norm_snd_le v) (by simpa using norm_snd_le w)
      (abs_nonneg _) (norm_nonneg _)
  have h12 : |v.1*w.2+v.2*w.1| ≤ 2*‖v‖*‖w‖ := by
    have ha : |v.1*w.2| ≤ ‖v‖*‖w‖ := by
      rw [abs_mul]
      exact mul_le_mul (by simpa using norm_fst_le v) (by simpa using norm_snd_le w)
        (abs_nonneg _) (norm_nonneg _)
    have hb : |v.2*w.1| ≤ ‖v‖*‖w‖ := by
      rw [abs_mul]
      exact mul_le_mul (by simpa using norm_snd_le v) (by simpa using norm_fst_le w)
        (abs_nonneg _) (norm_nonneg _)
    linarith [abs_add_le (v.1*w.2) (v.2*w.1)]
  rw [realSecondForm_bilinear hF]
  calc
    _ ≤ (‖(v.1*w.1) • realSecondTensor F p 0‖+
        ‖(v.1*w.2+v.2*w.1) • realSecondTensor F p 1‖)+
        ‖(v.2*w.2) • realSecondTensor F p 2‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (‖v‖*‖w‖*‖realSecondTensor F p‖+
        (2*‖v‖*‖w‖)*‖realSecondTensor F p‖)+‖v‖*‖w‖*‖realSecondTensor F p‖ := by
      simp only [norm_smul,Real.norm_eq_abs]
      gcongr
      · exact norm_le_pi_norm _ 0
      · exact norm_le_pi_norm _ 1
      · exact norm_le_pi_norm _ 2
    _ = _ := by ring

lemma norm_realSecondTensor_comp_smooth {F : RField 4} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : coordDet (fderiv ℝ φ p) ≠ 0) :
    ‖realSecondTensor (F ∘ φ) p‖ ≤
      4*‖realSecondTensor F (φ p)‖*‖fderiv ℝ φ p‖^2 := by
  have hbound (v : Base) (hv : ‖v‖ = 1) : ‖fderiv ℝ φ p v‖ ≤ ‖fderiv ℝ φ p‖ := by
    simpa only [hv,mul_one] using (fderiv ℝ φ p).le_opNorm v
  have hx : ‖dx‖ = 1 := by simp [dx,Prod.norm_def]
  have hy : ‖dy‖ = 1 := by simp [dy,Prod.norm_def]
  have hb (v w : Base) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
      ‖realSecondForm (F ∘ φ) v w p‖ ≤ 4*‖realSecondTensor F (φ p)‖*‖fderiv ℝ φ p‖^2 := by
    rw [realSecondForm_comp_smooth hF hφ _ _ _ hD hdet]
    calc
      _ ≤ 4*‖realSecondTensor F (φ p)‖*‖fderiv ℝ φ p v‖*‖fderiv ℝ φ p w‖ :=
        norm_realSecondForm_le hF _ _ _
      _ ≤ 4*‖realSecondTensor F (φ p)‖*‖fderiv ℝ φ p‖*‖fderiv ℝ φ p‖ := by
        gcongr
        · exact hbound v hv
        · exact hbound w hw
      _ = _ := by ring
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i
  · exact hb dx dx hx hx
  · exact hb dx dy hx hy
  · exact hb dy dy hy hy

end ClosedSurfaceR4.RealModes

end

end OAI
