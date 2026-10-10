import Mathlib
import OAI.Geometry.PrescribedRicci.ComplexIntegrationByParts

namespace OAI

/-! Wirtinger Scalar. -/

noncomputable section
open Matrix Filter Set Topology
open scoped ContDiff ComplexOrder
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ}

lemma holDeriv_mul {f g : Coordinates d → ℂ} {z : Coordinates d}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (a : Fin d) :
    holDeriv (fun y => f y*g y) z a = holDeriv f z a*g z+f z*holDeriv g z a := by
  unfold holDeriv
  rw [fderiv_fun_mul hf hg]
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  ring

lemma holDeriv_add {f g : Coordinates d → ℂ} {z : Coordinates d}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (a : Fin d) :
    holDeriv (fun y => f y+g y) z a = holDeriv f z a+holDeriv g z a := by
  unfold holDeriv
  rw [fderiv_fun_add hf hg]
  simp only [_root_.add_apply]
  ring

lemma holDeriv_sum {ι : Type*} [Fintype ι] {f : ι → Coordinates d → ℂ}
    {z : Coordinates d} (hf : ∀ i, DifferentiableAt ℝ (f i) z) (a : Fin d) :
    holDeriv (fun y => ∑ i, f i y) z a = ∑ i, holDeriv (f i) z a := by
  unfold holDeriv
  rw [fderiv_fun_sum (fun i _ => hf i)]
  simp only [_root_.sum_apply,← Finset.sum_sub_distrib,Finset.mul_sum]

lemma holDeriv_star (f : Coordinates d → ℂ) (z : Coordinates d) (a : Fin d) :
    holDeriv (fun y => star (f y)) z a = star (barDeriv f z a) := by
  unfold holDeriv barDeriv
  rw [fderiv_star]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,starL'_apply,
    map_mul,map_add,map_inv₀,map_ofNat,Complex.star_def,Complex.conj_I]
  ring

lemma barDeriv_star (f : Coordinates d → ℂ) (z : Coordinates d) (a : Fin d) :
    barDeriv (fun y => star (f y)) z a = star (holDeriv f z a) := by
  have h := holDeriv_star (fun y => star (f y)) z a
  simpa only [star_star] using congrArg star h.symm

lemma contDiffAt_holDeriv {f : Coordinates d → ℂ} {z : Coordinates d}
    (hf : ContDiffAt ℝ ∞ f z) (a : Fin d) :
    ContDiffAt ℝ ∞ (fun y => holDeriv f y a) z := by
  unfold holDeriv
  exact contDiffAt_const.mul (((hf.fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const).sub
    (contDiffAt_const.mul ((hf.fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const)))

def scalarHolForm (a : Fin d) : (Coordinates d →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (2:ℂ)⁻¹ • (ContinuousLinearMap.apply ℝ ℂ (coordinateVector a) -
    Complex.I • ContinuousLinearMap.apply ℝ ℂ (Complex.I • coordinateVector a))

def scalarBarForm (a : Fin d) : (Coordinates d →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (2:ℂ)⁻¹ • (ContinuousLinearMap.apply ℝ ℂ (coordinateVector a) +
    Complex.I • ContinuousLinearMap.apply ℝ ℂ (Complex.I • coordinateVector a))

lemma fderiv_holDeriv {f : Coordinates d → ℂ} {z : Coordinates d}
    (hf : ContDiffAt ℝ ∞ f z) (a : Fin d) (v : Coordinates d) :
    fderiv ℝ (fun y => holDeriv f y a) z v =
      (2:ℂ)⁻¹ * (fderiv ℝ (fderiv ℝ f) z v (coordinateVector a) -
        Complex.I*fderiv ℝ (fderiv ℝ f) z v (Complex.I • coordinateVector a)) := by
  exact congrArg (fun L : Coordinates d →L[ℝ] ℂ => L v)
    (((scalarHolForm a).hasFDerivAt.comp z
      ((hf.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)).hasFDerivAt).fderiv)

lemma fderiv_barDeriv {f : Coordinates d → ℂ} {z : Coordinates d}
    (hf : ContDiffAt ℝ ∞ f z) (a : Fin d) (v : Coordinates d) :
    fderiv ℝ (fun y => barDeriv f y a) z v =
      (2:ℂ)⁻¹ * (fderiv ℝ (fderiv ℝ f) z v (coordinateVector a) +
        Complex.I*fderiv ℝ (fderiv ℝ f) z v (Complex.I • coordinateVector a)) := by
  exact congrArg (fun L : Coordinates d →L[ℝ] ℂ => L v)
    (((scalarBarForm a).hasFDerivAt.comp z
      ((hf.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)).hasFDerivAt).fderiv)

lemma scalar_bar_hol_comm {f : Coordinates d → ℂ} {z : Coordinates d}
    (hf : ContDiffAt ℝ ∞ f z) (a b : Fin d) :
    barDeriv (fun y => holDeriv f y a) z b = holDeriv (fun y => barDeriv f y b) z a := by
  change (2:ℂ)⁻¹ * (fderiv ℝ (fun y => holDeriv f y a) z (coordinateVector b) +
    Complex.I*fderiv ℝ (fun y => holDeriv f y a) z (Complex.I • coordinateVector b)) =
    (2:ℂ)⁻¹ * (fderiv ℝ (fun y => barDeriv f y b) z (coordinateVector a) -
    Complex.I*fderiv ℝ (fun y => barDeriv f y b) z (Complex.I • coordinateVector a))
  rw [fderiv_holDeriv hf,fderiv_holDeriv hf,fderiv_barDeriv hf,fderiv_barDeriv hf]
  have hs (u v : Coordinates d) : fderiv ℝ (fderiv ℝ f) z u v = fderiv ℝ (fderiv ℝ f) z v u := by
    exact hf.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      change ((2:ℕ∞):WithTop ℕ∞) ≤ ((⊤:ℕ∞):WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top) u v
  rw [hs (coordinateVector a) (coordinateVector b),
    hs (coordinateVector a) (Complex.I • coordinateVector b),
    hs (Complex.I • coordinateVector a) (coordinateVector b),
    hs (Complex.I • coordinateVector a) (Complex.I • coordinateVector b)]
  ring

end Anticanonical.SourceSmooth.KaehlerMetric

end

end OAI
