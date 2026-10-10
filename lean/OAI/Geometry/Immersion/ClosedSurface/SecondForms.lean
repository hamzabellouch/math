import OAI.Geometry.Immersion.ClosedSurface.NormalProjection
import OAI.Geometry.Immersion.ClosedSurface.GoodPhases

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set

lemma real_second_coordDeriv {n : ℕ} {F : RField n} {p : Base}
    (hF : DifferentiableAt ℝ (fderiv ℝ F) p) (v w : Base) :
    coordDeriv v (coordDeriv w F) p = fderiv ℝ (fderiv ℝ F) p v w := by
  have h := (hF.hasFDerivAt.clm_apply (hasFDerivAt_const w p)).fderiv
  change (fderiv ℝ (fun q => (fderiv ℝ F q) w) p) v = _
  rw [h]
  simp

lemma real_second_coordDeriv_comm {n : ℕ} {F : RField n} (hF : ContDiff ℝ ∞ F)
    (p v w : Base) : coordDeriv v (coordDeriv w F) p = coordDeriv w (coordDeriv v F) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
  rw [real_second_coordDeriv hd, real_second_coordDeriv hd]
  exact second_derivative_symmetric
    (fun q => (hF.differentiable (by simp) q).hasFDerivAt) hd.hasFDerivAt v w

lemma base_eq_basis (v : Base) : v = v.1 • dx + v.2 • dy := by ext <;> simp [dx,dy]

lemma coordDeriv_eq_basis {n : ℕ} (F : RField n) (v p : Base) :
    coordDeriv v F p = v.1 • coordDeriv dx F p + v.2 • coordDeriv dy F p := by
  conv_lhs => arg 1; rw [base_eq_basis v]
  simp [coordDeriv]

lemma second_coordDeriv_quadratic {n : ℕ} {F : RField n} (hF : ContDiff ℝ ∞ F)
    (v p : Base) : coordDeriv v (coordDeriv v F) p =
      (v.1^2) • coordDeriv dx (coordDeriv dx F) p +
      (2*v.1*v.2) • coordDeriv dx (coordDeriv dy F) p +
      (v.2^2) • coordDeriv dy (coordDeriv dy F) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
  have hsym := real_second_coordDeriv_comm hF p dy dx
  simp only [real_second_coordDeriv hd] at hsym ⊢
  conv_lhs => arg 2; rw [base_eq_basis v]
  conv_lhs => arg 1; arg 2; rw [base_eq_basis v]
  simp only [map_add, map_smul, add_apply, smul_apply,
    hsym]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma coordDeriv_comp_linear {n : ℕ} {F : RField n} (hF : ContDiff ℝ ∞ F)
    (e : Base →L[ℝ] Base) (v p : Base) :
    coordDeriv v (F ∘ e) p = coordDeriv (e v) F (e p) := by
  simp only [coordDeriv, fderiv_comp p (hF.differentiable (by simp) _) e.differentiableAt,
    e.fderiv, ContinuousLinearMap.comp_apply]

lemma second_coordDeriv_comp_linear {n : ℕ} {F : RField n} (hF : ContDiff ℝ ∞ F)
    (e : Base →L[ℝ] Base) (v w p : Base) :
    coordDeriv v (coordDeriv w (F ∘ e)) p =
      coordDeriv (e v) (coordDeriv (e w) F) (e p) := by
  have he : coordDeriv w (F ∘ e) = (coordDeriv (e w) F) ∘ e := by
    funext q; exact coordDeriv_comp_linear hF e w q
  rw [he, coordDeriv_comp_linear (contDiff_real_coordDeriv hF (e w))]


def realSecondForm (F : RField 4) (v w : Base) (p : Base) : RVec 4 :=
  realNormalPart (coordDeriv dx F p) (coordDeriv dy F p) (coordDeriv v (coordDeriv w F) p)

def realSecondTensor (F : RField 4) (p : Base) : Fin 3 → RVec 4 :=
  ![realSecondForm F dx dx p, realSecondForm F dx dy p, realSecondForm F dy dy p]

lemma realSecondForm_quadratic {F : RField 4} (hF : ContDiff ℝ ∞ F) (v p : Base) :
    realSecondForm F v v p = secondQuadratic (realSecondTensor F p) v := by
  unfold realSecondForm
  rw [second_coordDeriv_quadratic hF]
  have hlin := realNormalPart_linear (coordDeriv dx F p) (coordDeriv dy F p)
  rw [hlin.map_add, hlin.map_add, hlin.map_smul, hlin.map_smul, hlin.map_smul]
  simp [secondQuadratic, realSecondTensor, realSecondForm]

lemma gramDet_comp_linear {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (e : Base →L[ℝ] Base) (p : Base) :
    NormalFrame.gramDet (coordDeriv dx (F ∘ e) p) (coordDeriv dy (F ∘ e) p) =
    ((e dx).1 * (e dy).2 - (e dx).2 * (e dy).1)^2 *
      NormalFrame.gramDet (coordDeriv dx F (e p)) (coordDeriv dy F (e p)) := by
  rw [coordDeriv_comp_linear hF, coordDeriv_comp_linear hF,
    coordDeriv_eq_basis F (e dx), coordDeriv_eq_basis F (e dy), gramDet_change_basis]

lemma realSecondForm_comp_linear {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (e : Base →L[ℝ] Base) (v w p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F (e p)) (coordDeriv dy F (e p)) ≠ 0)
    (hdet : (e dx).1 * (e dy).2 - (e dx).2 * (e dy).1 ≠ 0) :
    realSecondForm (F ∘ e) v w p = realSecondForm F (e v) (e w) (e p) := by
  unfold realSecondForm
  rw [coordDeriv_comp_linear hF, coordDeriv_comp_linear hF, second_coordDeriv_comp_linear hF,
    coordDeriv_eq_basis F (e dx), coordDeriv_eq_basis F (e dy), realNormalPart_change_basis]
  · exact hD
  · exact hdet

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set

lemma second_coordDeriv_bilinear {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (v w p : Base) : coordDeriv v (coordDeriv w F) p =
      (v.1*w.1) • coordDeriv dx (coordDeriv dx F) p +
      (v.1*w.2+v.2*w.1) • coordDeriv dx (coordDeriv dy F) p +
      (v.2*w.2) • coordDeriv dy (coordDeriv dy F) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
  have hsym := real_second_coordDeriv_comm hF p dy dx
  simp only [real_second_coordDeriv hd] at hsym ⊢
  conv_lhs => arg 2; rw [base_eq_basis w]
  conv_lhs => arg 1; arg 2; rw [base_eq_basis v]
  simp only [map_add, map_smul, add_apply, smul_apply,
    hsym]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma realSecondForm_bilinear {F : RField 4} (hF : ContDiff ℝ ∞ F) (v w p : Base) :
    realSecondForm F v w p =
      (v.1*w.1) • realSecondTensor F p 0 +
      (v.1*w.2+v.2*w.1) • realSecondTensor F p 1 +
      (v.2*w.2) • realSecondTensor F p 2 := by
  unfold realSecondForm
  rw [second_coordDeriv_bilinear hF]
  have hlin := realNormalPart_linear (coordDeriv dx F p) (coordDeriv dy F p)
  rw [hlin.map_add, hlin.map_add, hlin.map_smul, hlin.map_smul, hlin.map_smul]
  simp [realSecondTensor, realSecondForm]

lemma realSecondTensor_ne_zero_iff {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : Base) :
    realSecondTensor F p ≠ 0 ↔ ∃ v w : Base, realSecondForm F v w p ≠ 0 := by
  constructor
  · intro hB
    by_contra hh
    push Not at hh
    apply hB
    ext i
    fin_cases i <;> simp [realSecondTensor, hh]
  · rintro ⟨v,w,hvw⟩ hB
    apply hvw
    rw [realSecondForm_bilinear hF, hB]
    simp



theorem actual_positive_phase_data {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p : Base) (hB : ∃ v w : Base, realSecondForm F v w p ≠ 0)
    (H : PhaseMean.Tensor) (hH0 : 0 < H 0) (hHdet : 0 < H 0 * H 2 - (H 1)^2) :
    ∃ (ξ : Fin 3 → Base) (Q : Fin 3 → PhaseMean.Tensor →L[ℝ] ℝ),
      (∀ A, ∑ i, Q i A • covectorSquare (ξ i) = A) ∧
      (∀ i, 0 < Q i H) ∧
      (∀ i, Good (realSecondTensor F p) (ξ i)) ∧
      (∀ i j, i ≠ j → Good (realSecondTensor F p) (ξ i + ξ j) ∧
        Good (realSecondTensor F p) (ξ i - ξ j)) :=
  positive_good_phase_data ((realSecondTensor_ne_zero_iff hF p).mpr hB) hH0 hHdet

end ClosedSurfaceR4.RealModes

end

end OAI
