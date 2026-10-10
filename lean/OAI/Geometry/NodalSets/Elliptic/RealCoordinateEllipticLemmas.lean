import OAI.Geometry.NodalSets.Coefficients.GlobalCorrection

namespace OAI

noncomputable section

namespace Yau
open scoped ContDiff
variable {n : ℕ}

lemma real_coordPartial_smooth (f : Coord n → ℝ) (hf : ContDiff ℝ ∞ f) (i : Fin n) :
    ContDiff ℝ ∞ (fun x ↦ coordPartial f x i) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma real_coordPartial_mul (f g : Coord n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : Coord n) (i : Fin n) :
    coordPartial (fun y ↦ f y*g y) x i =
      coordPartial f x i*g x + f x*coordPartial g x i := by
  unfold coordPartial
  rw [fderiv_fun_mul (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

lemma real_coordPartial_sum (f : Fin n → Coord n → ℝ)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (x : Coord n) (i : Fin n) :
    coordPartial (fun y ↦ ∑ j, f j y) x i = ∑ j, coordPartial (f j) x i := by
  unfold coordPartial
  rw [fderiv_fun_sum (fun j _ ↦ (hf j).differentiable (by simp) x)]
  simp

def realEllipticDrift (gamma : Coord n → ℝ)
    (B : Coord n → Fin n → Fin n → ℝ) (x : Coord n) (j : Fin n) : ℝ :=
  (gamma x)⁻¹ * ∑ i, coordPartial (fun y ↦ gamma y*B y i j) x i

lemma realEllipticDrift_smooth (gamma : Coord n → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (B : Coord n → Fin n → Fin n → ℝ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (j : Fin n) :
    ContDiff ℝ ∞ (fun x ↦ realEllipticDrift gamma B x j) :=
  (hg.inv hgn).mul (ContDiff.sum (fun i _ ↦
    real_coordPartial_smooth _ (hg.mul (hB i j)) i))

theorem real_weighted_elliptic_expansion (gamma : Coord n → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (B : Coord n → Fin n → Fin n → ℝ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (w : Coord n → ℝ) (hw : ContDiff ℝ ∞ w) (x : Coord n) :
    weightedDiv gamma (fun y i ↦ ∑ j, B y i j*coordPartial w y j) x =
      (∑ i, ∑ j, B x i j*coordPartial (fun y ↦ coordPartial w y j) x i) +
      ∑ j, realEllipticDrift gamma B x j*coordPartial w x j := by
  have he (i : Fin n) :
      (fun y ↦ gamma y*(∑ j, B y i j*coordPartial w y j)) =
      (fun y ↦ ∑ j, (gamma y*B y i j)*coordPartial w y j) := by
    funext y
    simp only [Finset.mul_sum,mul_assoc]
  unfold weightedDiv coordDiv
  simp_rw [he,real_coordPartial_sum _ (fun j ↦
    (hg.mul (hB _ j)).mul (real_coordPartial_smooth w hw j)),
    real_coordPartial_mul _ _ (hg.mul (hB _ _)) (real_coordPartial_smooth w hw _)]
  simp only [Finset.sum_add_distrib]
  have hcancel (i j : Fin n) :
      (gamma x)⁻¹ * ((gamma x*B x i j)*coordPartial (fun y ↦ coordPartial w y j) x i) =
      B x i j*coordPartial (fun y ↦ coordPartial w y j) x i := by
    rw [mul_assoc,← mul_assoc (gamma x)⁻¹,inv_mul_cancel₀ (hgn x),one_mul]
  simp only [mul_add,Finset.mul_sum,hcancel]
  rw [add_comm]
  congr 1
  rw [Finset.sum_comm]
  unfold realEllipticDrift
  simp only [Finset.mul_sum,Finset.sum_mul,mul_assoc]

end Yau

namespace Yau.Target
open Set
open scoped ContDiff
variable {d : ℕ}

def simplicityDensityPerturbation (gamma u zeta : Yau.Coord d → ℝ)
    (V : Yau.Coord d → Yau.Coord d) (lam : ℝ) (x : Yau.Coord d) : ℝ :=
  -lam⁻¹ * (u x * Yau.weightedDiv gamma (fun y i ↦ zeta y * V y i) x +
    2*zeta x*Yau.pairing u V x)

lemma pairing_square_scaled (u zeta : Yau.Coord d → ℝ)
    (V : Yau.Coord d → Yau.Coord d) (x : Yau.Coord d)
    (hu : DifferentiableAt ℝ u x) :
    Yau.pairing (fun y ↦ u y^2) (fun y i ↦ zeta y*V y i) x =
      2*zeta x*u x*Yau.pairing u V x := by
  unfold Yau.pairing Yau.coordPartial
  simp_rw [pow_two,fderiv_fun_mul hu hu]
  simp only [add_apply,smul_apply,smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem simplicity_coordinate_cancellation
    (gamma u zeta : Yau.Coord d → ℝ) (V : Yau.Coord d → Yau.Coord d)
    (lam : ℝ) (hlam : lam ≠ 0) (x : Yau.Coord d)
    (hg : DifferentiableAt ℝ gamma x) (hgn : gamma x ≠ 0)
    (hu : DifferentiableAt ℝ u x) (hz : DifferentiableAt ℝ zeta x)
    (hV : ∀ i, DifferentiableAt ℝ (fun y ↦ V y i) x) :
    Yau.weightedDiv gamma (fun y i ↦ (zeta y*u y^2)*V y i) x +
      lam*simplicityDensityPerturbation gamma u zeta V lam x*u x = 0 := by
  have he : (fun y i ↦ (zeta y*u y^2)*V y i) =
      (fun y i ↦ u y^2*(zeta y*V y i)) := by
    funext y i
    ring
  have hu2 : DifferentiableAt ℝ (fun y ↦ u y^2) x := by
    convert hu.mul hu using 1
    first | rfl | (funext y; exact pow_two (u y))
  have hd := Yau.weightedDiv_mul (u := fun y ↦ u y^2) (V := fun y i ↦ zeta y*V y i)
    hg hgn hu2 (fun i ↦ hz.mul (hV i))
  rw [he,hd,pairing_square_scaled u zeta V x hu]
  exact Yau.simplicity_preserves hlam

lemma simplicityDensityPerturbation_smooth
    (gamma u zeta : Yau.Coord d → ℝ) (V : Yau.Coord d → Yau.Coord d) (lam : ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hu : ContDiff ℝ ∞ u) (hz : ContDiff ℝ ∞ zeta)
    (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (simplicityDensityPerturbation gamma u zeta V lam) := by
  have hv (i : Fin d) := (contDiff_pi.mp hV) i
  exact contDiff_const.mul ((hu.mul
    (Yau.weightedDiv_smooth hg hgn (fun i ↦ hz.mul (hv i)))).add
    ((contDiff_const.mul hz).mul (Yau.pairing_smooth hu hv)))

lemma simplicityDensityPerturbation_tsupport_subset
    (gamma u zeta : Yau.Coord d → ℝ) (V : Yau.Coord d → Yau.Coord d) (lam : ℝ) :
    tsupport (simplicityDensityPerturbation gamma u zeta V lam) ⊆ tsupport zeta := by
  apply closure_minimal _ (isClosed_tsupport zeta)
  intro x hx
  by_contra h
  have hz := image_eq_zero_of_notMem_tsupport h
  have hd := Yau.weightedDiv_zero_off_support gamma zeta V h
  exact hx (by simp [simplicityDensityPerturbation,hz,hd])

end Yau.Target

end

end OAI
