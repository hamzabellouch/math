import OAI.Geometry.NodalSets.Elliptic.RealCarlemanCoercivity
import OAI.Geometry.NodalSets.Elliptic.RealCarlemanConjugation

namespace OAI

namespace Yau.Geometry
open Matrix MeasureTheory
open scoped ContDiff
noncomputable section

variable (gamma phi v : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgp : ∀ x, 0 < gamma x)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hs : ∀ x i j, B x i j = B x j i)
    (hphi : ContDiff ℝ ∞ phi) (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v)
    (a b C s t : ℝ) (hC : 0 ≤ C) (ht : 1 ≤ t) (hlarge : C+s^2 ≤ b*t)
    (hquad : ∀ x ∈ tsupport v, ∀ xi : Yau.Jets.Coord,
      a*(∑ i, (xi i)^2) ≤ realTransportQuadratic B (realMatrixFlux B phi) x xi +
        s*coordMatrixForm (B x) xi xi)
    (hweight : ∀ x ∈ tsupport v, b ≤
      Yau.pairing (realMatrixEnergy B phi phi) (realMatrixFlux B phi) x-s*realMatrixEnergy B phi phi x)
    (herror : ∀ x ∈ tsupport v,
      realWeightedElliptic gamma B (realWeightedElliptic gamma B phi) x ≤ C)

include hg hgp hB hs hphi hv hc hC ht hlarge hquad hweight herror

theorem real_carleman_estimate :
    2*a*t*(∫ x, gamma x*realGradientSquare v x) + b*t^3*(∫ x, gamma x*v x^2) ≤
      (∫ x, gamma x*(Real.exp (t*phi x)*realWeightedElliptic gamma B
        (fun y ↦ Real.exp (-t*phi y)*v y) x)^2) := by
  simp_rw [real_carleman_conjugation gamma phi v B hg (fun x ↦ (hgp x).ne') hB hs hphi hv]
  exact real_carleman_coercivity gamma (realMatrixEnergy B phi phi) v B (realMatrixFlux B phi)
    hg hgp (realMatrixEnergy_smooth B hB phi phi hphi hphi) hv hc hB hs
    (realMatrixFlux_smooth B phi hB hphi) a b C s t hC ht hlarge hquad hweight herror

theorem real_carleman_potential_estimate (potential : Yau.Jets.Coord → ℝ)
    (hpot : ContDiff ℝ ∞ potential) (M : ℝ)
    (hM : ∀ x ∈ tsupport v, (potential x)^2 ≤ M) (habs : 4*M ≤ b*t^3) :
    a*t*(∫ x, gamma x*realGradientSquare v x) + (b*t^3/4)*(∫ x, gamma x*v x^2) ≤
      (∫ x, gamma x*(Real.exp (t*phi x)*realWeightedElliptic gamma B
        (fun y ↦ Real.exp (-t*phi y)*v y) x + potential x*v x)^2) := by
  let P := fun x ↦ Real.exp (t*phi x)*realWeightedElliptic gamma B
    (fun y ↦ Real.exp (-t*phi y)*v y) x
  have hP : ContDiff ℝ ∞ P := (contDiff_const.mul hphi).exp.mul
    (realWeightedElliptic_smooth gamma B _ hg (fun x ↦ (hgp x).ne') hB
      (((contDiff_const.mul hphi).exp).mul hv))
  have hPc : HasCompactSupport P :=
    (realWeightedElliptic_compact gamma B _ hc.mul_left).mul_left
  have hF : ContDiff ℝ ∞ (fun x ↦ P x+potential x*v x) := hP.add (hpot.mul hv)
  have hFc : HasCompactSupport (fun x ↦ P x+potential x*v x) := hPc.add hc.mul_left
  have hP2 : HasCompactSupport (fun x ↦ (P x)^2) := by
    convert hPc.mul_right (f' := P) using 1
    first | rfl | (ext point; simp [pow_two])
  have hF2 : HasCompactSupport (fun x ↦ (P x+potential x*v x)^2) := by
    convert hFc.mul_right (f' := fun point ↦ P point+potential point*v point) using 1
    first | rfl | (ext point; simp [pow_two])
  have hv2 : HasCompactSupport (fun x ↦ v x^2) := by
    convert hc.mul_right (f' := v) using 1
    first | rfl | (ext point; simp [pow_two])
  have hiP : Integrable (fun x ↦ gamma x*(P x)^2) :=
    (hg.mul (hP.pow 2)).continuous.integrable_of_hasCompactSupport hP2.mul_left
  have hiF : Integrable (fun x ↦ gamma x*(P x+potential x*v x)^2) :=
    (hg.mul (hF.pow 2)).continuous.integrable_of_hasCompactSupport hF2.mul_left
  have hiv : Integrable (fun x ↦ gamma x*v x^2) :=
    (hg.mul (hv.pow 2)).continuous.integrable_of_hasCompactSupport hv2.mul_left
  have hpoint (x : Yau.Jets.Coord) : gamma x*(P x)^2 ≤
      2*(gamma x*(P x+potential x*v x)^2)+2*M*(gamma x*v x^2) := by
    have hMv : (potential x)^2*v x^2 ≤ M*v x^2 := by
      by_cases hx : x ∈ tsupport v
      · exact mul_le_mul_of_nonneg_right (hM x hx) (sq_nonneg _)
      · simp [image_eq_zero_of_notMem_tsupport hx]
    have halg : (P x)^2 ≤ 2*(P x+potential x*v x)^2+2*M*v x^2 := by
      nlinarith only [hMv,sq_nonneg (P x+2*potential x*v x)]
    nlinarith only [mul_le_mul_of_nonneg_left halg (hgp x).le]
  have hi := integral_mono hiP ((hiF.const_mul 2).add (hiv.const_mul (2*M))) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_add (hiF.const_mul 2) (hiv.const_mul (2*M)),integral_const_mul,integral_const_mul] at hi
  have he := real_carleman_estimate gamma phi v B hg hgp hB hs hphi hv hc a b C s t
    hC ht hlarge hquad hweight herror
  have hv0 : 0 ≤ ∫ x, gamma x*v x^2 := integral_nonneg (fun x ↦ mul_nonneg (hgp x).le (sq_nonneg _))
  have habsm := mul_le_mul_of_nonneg_right habs hv0
  change _ ≤ ∫ x, gamma x*(P x+potential x*v x)^2
  change _ ≤ ∫ x, gamma x*(P x)^2 at he
  nlinarith only [he,hi,habsm]

end
end Yau.Geometry

end OAI
