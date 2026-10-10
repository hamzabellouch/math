import OAI.MathematicalPhysics.Transonic.Exterior.Conv

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorJet
open PowerSeries Finset

def scaledPref (h sigma : ℝ) : Series :=
  C (p0 sigma)+C (h*p1 sigma)*X+C (h^2*p2 sigma)*X^2+C (h^3*p3 sigma)*X^3

def scaledResidual (h sigma kappa c : ℝ) (w : Series) : Series :=
  scaledPref h sigma*(derivative (w^2)-C (1/3)*derivative (w^3))+
  C (3*(1-c)*h^2)*X+
  (C (h*i10 kappa c)+C (h^2*i11 kappa c)*X)*w+
  (C (h*i20 kappa c)+C (h^2*i21 kappa c)*X)*w^2+
  (C (h*i30 kappa c)+C (h^2*i31 kappa c)*X)*w^3+
  (C (h*i40 kappa c)+C (h^2*i41 kappa c)*X)*w^4

lemma rescale_C' (h x : ℝ) : rescale h (C x : Series)=C x := by
  ext n;simp [coeff_C];split_ifs <;> simp_all
lemma rescale_X' (h : ℝ) : rescale h (X : Series)=C h*X := by
  ext n;simp [coeff_X]

lemma scaledResidual_rescale (h sigma kappa c : ℝ) (w : Series) :
    scaledResidual h sigma kappa c (rescale h w)=C h*rescale h (residual sigma kappa c w) := by
  have hd2 : derivative ((rescale h w)^2)=C h*rescale h (derivative (w^2)) := by
    rw [← map_pow];exact derivative_rescale h (w^2)
  have hd3 : derivative ((rescale h w)^3)=C h*rescale h (derivative (w^3)) := by
    rw [← map_pow];exact derivative_rescale h (w^3)
  rw [residual_expansion,pref_expansion]
  unfold scaledResidual scaledPref
  rw [hd2,hd3]
  simp only [map_mul,map_add,map_sub,map_pow,rescale_C',rescale_X']
  ring

lemma coeff_scaledPref_derivative (h sigma : ℝ) (w : Series) (n : ℕ) :
    coeff (n+2) (scaledPref h sigma*derivative w)=
      p0 sigma*(n+3)*coeff (n+3) w+
      h*p1 sigma*(n+2)*coeff (n+2) w+
      h^2*p2 sigma*(n+1)*coeff (n+1) w+
      h^3*p3 sigma*n*coeff n w := by
  unfold scaledPref
  simp only [add_mul,map_add]
  have h1 : ∀ a : ℝ, coeff (n+2) (C a*X*derivative w)=a*(n+2)*coeff (n+2) w := by
    intro a;rw [mul_assoc,coeff_C_mul,EulerFormal.coeff_X_mul_derivative];push_cast;ring
  have h2 : ∀ a : ℝ, coeff (n+2) (C a*X^2*derivative w)=a*(n+1)*coeff (n+1) w := by
    intro a
    rw [mul_assoc,coeff_C_mul,show X^2*derivative w=X*(X*derivative w) by ring,
      show n+2=(n+1)+1 by omega,coeff_succ_X_mul,EulerFormal.coeff_X_mul_derivative]
    push_cast;ring
  have h3 : ∀ a : ℝ, coeff (n+2) (C a*X^3*derivative w)=a*n*coeff n w := by
    intro a
    rw [mul_assoc,coeff_C_mul,show X^3*derivative w=X^2*(X*derivative w) by ring,
      coeff_X_pow_mul,EulerFormal.coeff_X_mul_derivative];ring
  rw [h1,h2,h3,coeff_C_mul,coeff_derivative]
  push_cast;ring

def scaledRatioStep (h sigma kappa c : ℝ) (n : ℕ) (sq cu qu : ℕ → ℝ) (sr : ℝ) : ℝ :=
  p0 sigma*(n+1)*(sr-cu (n+1)/3)+
  h*p1 sigma*n*(sq n-cu n/3)+
  h^2*p2 sigma*(n-1)*(sq (n-1)-cu (n-1)/3)+
  h^3*p3 sigma*(n-2)*(sq (n-2)-cu (n-2)/3)+
  h^2*i11 kappa c+h*i20 kappa c*sq n+h^2*i21 kappa c*sq (n-1)+
  h*i30 kappa c*cu n+h^2*i31 kappa c*cu (n-1)+
  h*i40 kappa c*qu n+h^2*i41 kappa c*qu (n-1)

lemma scaled_normalized_recurrence (h sigma kappa c s rho : ℝ) (w : Series)
    (hw0 : coeff 0 w=0) (hw1 : coeff 1 w=s) (he : scaledResidual h sigma kappa c w=0)
    (hrho : rho*(2*(1-sigma)*s)=h*(1-c)*(2*kappa+3)-2*(1-sigma)*s)
    (n : ℕ) (hn : 2≤n) (hb : coeff (n-1) w≠0) :
    (2*(1-sigma)*s*(rho-n))*(coeff n w/coeff (n-1) w)=
      scaledRatioStep h sigma kappa c n (powerRatio w (n-1) 2) (powerRatio w (n-1) 3)
        (powerRatio w (n-1) 4) (squareRRatio w n) := by
  obtain ⟨k,rfl⟩ : ∃ k, n=k+2 := ⟨n-2,by omega⟩
  have hh := congrArg (coeff (k+2) : Series → ℝ) he
  unfold scaledResidual at hh
  rw [show scaledPref h sigma*(derivative (w^2)-C (1/3)*derivative (w^3))=
    scaledPref h sigma*derivative (w^2)-C (1/3)*(scaledPref h sigma*derivative (w^3)) by ring] at hh
  simp only [map_add,map_sub,map_zero,coeff_C_mul,coeff_scaledPref_derivative,
    EulerFormal.coeff_affine_mul] at hh
  have hx : coeff (k+2) (X : Series)=0 := by simp [coeff_X,show k+2≠1 by omega]
  rw [hx] at hh
  have hs := EulerFormal.coeff_square_remainder w hw0 (k+2) (by omega)
  rw [hw1,show k+2+1=k+3 by omega] at hs
  rw [hs] at hh
  unfold scaledRatioStep powerRatio squareRRatio p0 p1 p2 p3 i10 i11 i20 i21 i30 i31 i40 i41 at *
  simp only [show k+2-1=k+1 by omega,show k+2-2=k by omega,
    show k+2+1=k+3 by omega] at *
  push_cast
  field_simp
  linear_combination -3*hh+3*(coeff (k+2) w)*hrho

end SepticProfile.ExteriorJet

end
end

end OAI
