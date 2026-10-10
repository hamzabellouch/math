import OAI.NumberTheory.CubicMoment.Estimates.PrincipalLatticeTheta

namespace OAI

/-! The principal theta function includes the zero vector. Its exact
unit multiplicity gives the inhomogeneous transformation of the ideal
theta sum and therefore the principal zeta pole. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma principalIdealTheta_nonzero {A t : ℝ} (hA : 0 < A) (ht : 0 < t) :
    (∑' a : {a : Eisenstein // a ≠ 0}, (Real.exp (-norm a.val*t/A):ℂ))=
      (Nat.card (Eisensteinˣ):ℂ)*idealTheta A (fun _ => 1) t := by
  let : Finite (Eisensteinˣ) := idealTheta_units_finite
  let : Fintype (Eisensteinˣ) := Fintype.ofFinite _
  let f : EisensteinIdealExponent → ℂ := fun ν => (Real.exp (-idealExponentNorm ν*t/A):ℂ)
  have hf : Summable f := by
    simpa only [one_mul] using idealTheta_summable hA ht (fun _ => 1) (by simp)
  have hp : Summable (fun x : EisensteinIdealExponent × Eisensteinˣ => f x.1) := by
    simpa only [mul_one] using summable_mul_of_summable_norm
      (g := fun _ : Eisensteinˣ => (1:ℂ)) hf.norm (hasSum_fintype _).summable
  rw [←idealElementCoordinates.tsum_eq]
  simp_rw [idealElementCoordinates_norm]
  change (∑' x : EisensteinIdealExponent × Eisensteinˣ, f x.1)=_
  rw [hp.tsum_prod' (fun _ => (hasSum_fintype _).summable)]
  simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [tsum_mul_left]
  simp only [Nat.card_eq_fintype_card,idealTheta,one_mul]
  rfl

lemma principalLatticeTheta_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun a : Eisenstein => (Real.exp (-norm a*t/residueHeckeScale 1):ℂ)) := by
  have hA := residueHeckeScale_pos (q := 1) one_ne_zero
  have h := schwartz_summable_eisenstein
    (radialGaussianSchwartz (t/residueHeckeScale 1) (div_pos ht hA))
  convert h using 1
  funext a
  rw [radialGaussianSchwartz_apply]
  change (Real.exp (-Complex.normSq (a:ℂ)*t/residueHeckeScale 1):ℂ)=
    (Real.exp (-(t/residueHeckeScale 1)*‖(a:ℂ)‖^2):ℂ)
  rw [Complex.normSq_eq_norm_sq]
  congr 2
  ring

lemma principalLatticeTheta_eq_ideal {t : ℝ} (ht : 0 < t) :
    principalLatticeTheta t=1+(Nat.card (Eisensteinˣ):ℂ)*
      idealTheta (residueHeckeScale 1) (fun _ => 1) t := by
  classical
  have h := (principalLatticeTheta_summable ht).tsum_eq_add_tsum_ite 0
  have hzero : (Real.exp (-norm (0:Eisenstein)*t/residueHeckeScale 1):ℂ)=1 := by
    norm_num [norm]
  rw [hzero] at h
  rw [principalLatticeTheta,h,←principalIdealTheta_nonzero
    (residueHeckeScale_pos (q := 1) one_ne_zero) ht]
  congr 1
  calc
    _ = ∑' a : Eisenstein, Set.indicator {a : Eisenstein | a ≠ 0}
        (fun a => (Real.exp (-norm a*t/residueHeckeScale 1):ℂ)) a := by
      apply tsum_congr
      intro a
      by_cases ha : a=0 <;> simp [ha,Set.indicator]
    _ = _ := (tsum_subtype {a : Eisenstein | a ≠ 0}
      (fun a => (Real.exp (-norm a*t/residueHeckeScale 1):ℂ))).symm

theorem principalIdealTheta_inversion {t : ℝ} (ht : 0 < t) :
    idealTheta (residueHeckeScale 1) (fun _ => 1) (1/t)=
      (t:ℂ)*idealTheta (residueHeckeScale 1) (fun _ => 1) t+
        ((t:ℂ)-1)/(Nat.card (Eisensteinˣ):ℂ) := by
  have h := principalLatticeTheta_inversion (one_div_pos.mpr ht)
  rw [one_div_one_div,principalLatticeTheta_eq_ideal (one_div_pos.mpr ht),
    principalLatticeTheta_eq_ideal ht] at h
  have hU := residueTheta_unit_multiplicity_ne_zero
  field_simp
  linear_combination h

end CubicFirstMoment

end

end OAI
