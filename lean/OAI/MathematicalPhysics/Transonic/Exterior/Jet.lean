import OAI.MathematicalPhysics.Transonic.Core

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorJet
open PowerSeries Finset
abbrev Series := PowerSeries ℝ

def reflected (u : Series) : Series := 1-rescale (-1) u

def pref (sigma : ℝ) : Series := (1-X)*(1-C sigma*(1-X)^2)
def residual (sigma kappa c : ℝ) (w : Series) : Series :=
  pref sigma*(2*w-w^2)*derivative w-
    (C (1-c)+2*C c*w-C c*w^2)*
      (C kappa*(1-X)*(2*w-w^2)+3*(w-X))

lemma derivative_rescale (a : ℝ) (u : Series) :
    derivative (rescale a u)=C a*rescale a (derivative u) := by
  ext n
  simp only [coeff_derivative,coeff_rescale,coeff_C_mul,pow_succ]
  ring

lemma reflected_equation (sigma kappa c : ℝ) (u : Series)
    (he : Formal.residual sigma kappa c u=0) :
    residual sigma kappa c (reflected u)=0 := by
  have h := congrArg (rescale (-1)) he
  have hd : rescale (-1) (derivative u)=derivative (reflected u) := by
    simp only [reflected,map_sub,derivative_one,derivative_rescale]
    simp
  have hx : rescale (-1) (X : Series) = -X := by ext n; simp [coeff_X]
  have hz : rescale (-1) (Formal.z : Series)=1-X := by simp [Formal.z,hx,sub_eq_add_neg]
  have hc (x : ℝ) : rescale (-1) (C x : Series)=C x := by ext n; simp [coeff_C]; split_ifs <;> simp_all
  unfold Formal.residual Formal.den Formal.prefactor Formal.r Formal.t at h
  simp only [map_mul,map_sub,map_pow,map_add,map_one,map_ofNat,hc,hz,map_zero,hd] at h
  unfold residual pref reflected
  rw [show derivative (1-rescale (-1) u)=derivative (reflected u) from rfl]
  convert h using 1 ; simp only [map_sub,map_one] ; ring

lemma reflected_zero {u : Series} (h : coeff 0 u=1) : coeff 0 (reflected u)=0 := by
  simp only [reflected,map_sub,coeff_zero_one,coeff_rescale,pow_zero,one_mul,h,sub_self]
lemma reflected_one {u : Series} {s : ℝ} (h : coeff 1 u=s) : coeff 1 (reflected u)=s := by
  simp [reflected,h]

def p0 (sigma : ℝ) : ℝ := 1-sigma
def p1 (sigma : ℝ) : ℝ := 3*sigma-1
def p2 (sigma : ℝ) : ℝ := -3*sigma
def p3 (sigma : ℝ) : ℝ := sigma

def i10 (kappa c : ℝ) : ℝ := -(1-c)*(2*kappa+3)
def i11 (kappa c : ℝ) : ℝ := 2*(1-c)*kappa+6*c
def i20 (kappa c : ℝ) : ℝ := -kappa*(-(1-c)+4*c)-6*c
def i21 (kappa c : ℝ) : ℝ := kappa*(-(1-c)+4*c)-3*c
def i30 (kappa c : ℝ) : ℝ := 4*c*kappa+3*c
def i31 (kappa c : ℝ) : ℝ := -4*c*kappa
def i40 (kappa c : ℝ) : ℝ := -c*kappa
def i41 (kappa c : ℝ) : ℝ := c*kappa

lemma pref_expansion (sigma : ℝ) :
    pref sigma=C (p0 sigma)+C (p1 sigma)*X+C (p2 sigma)*X^2+C (p3 sigma)*X^3 := by
  unfold pref p0 p1 p2 p3
  simp only [map_sub,map_neg,map_mul,map_ofNat,map_one]
  ring

lemma residual_expansion (sigma kappa c : ℝ) (w : Series) :
    residual sigma kappa c w =
      pref sigma*(derivative (w^2)-C (1/3)*derivative (w^3))+
      C (3*(1-c))*X+
      (C (i10 kappa c)+C (i11 kappa c)*X)*w+
      (C (i20 kappa c)+C (i21 kappa c)*X)*w^2+
      (C (i30 kappa c)+C (i31 kappa c)*X)*w^3+
      (C (i40 kappa c)+C (i41 kappa c)*X)*w^4 := by
  unfold residual i10 i11 i20 i21 i30 i31 i40 i41
  simp only [derivative_pow]
  norm_num only [Nat.cast_ofNat,map_sub,map_mul,map_add,map_neg,map_one,map_ofNat]
  have hh : (C (1/3) : Series)*3=1 := by
    rw [← map_ofNat C 3,← map_mul];norm_num
  have h3 : ∀ v : Series, C (1/3)*(3*v)=v := by intro v;rw [← mul_assoc,hh,one_mul]
  simp only [mul_assoc,h3]
  ring

lemma coeff_pref_derivative (sigma : ℝ) (w : Series) (n : ℕ) :
    coeff (n+2) (pref sigma*derivative w)=
      p0 sigma*(n+3)*coeff (n+3) w+
      p1 sigma*(n+2)*coeff (n+2) w+
      p2 sigma*(n+1)*coeff (n+1) w+
      p3 sigma*n*coeff n w := by
  rw [pref_expansion]
  simp only [add_mul,map_add]
  have h0 : coeff (n+2) (C (p0 sigma)*derivative w)=p0 sigma*(n+3)*coeff (n+3) w := by
    rw [coeff_C_mul,coeff_derivative];push_cast;ring
  have h1 : coeff (n+2) (C (p1 sigma)*X*derivative w)=p1 sigma*(n+2)*coeff (n+2) w := by
    rw [mul_assoc,coeff_C_mul,EulerFormal.coeff_X_mul_derivative];push_cast;ring
  have h2 : coeff (n+2) (C (p2 sigma)*X^2*derivative w)=p2 sigma*(n+1)*coeff (n+1) w := by
    rw [mul_assoc,coeff_C_mul,show X^2*derivative w=X*(X*derivative w) by ring,
      show n+2=(n+1)+1 by omega,coeff_succ_X_mul,EulerFormal.coeff_X_mul_derivative]
    push_cast;ring
  have h3 : coeff (n+2) (C (p3 sigma)*X^3*derivative w)=p3 sigma*n*coeff n w := by
    rw [mul_assoc,coeff_C_mul,show X^3*derivative w=X^2*(X*derivative w) by ring,
      coeff_X_pow_mul,EulerFormal.coeff_X_mul_derivative];ring
  rw [h0,h1,h2,h3]

lemma coefficient_equation (sigma kappa c : ℝ) (w : Series) (n : ℕ)
    (he : residual sigma kappa c w=0) :
    p0 sigma*(n+3)*(coeff (n+3) (w^2)-coeff (n+3) (w^3)/3)+
      p1 sigma*(n+2)*(coeff (n+2) (w^2)-coeff (n+2) (w^3)/3)+
      p2 sigma*(n+1)*(coeff (n+1) (w^2)-coeff (n+1) (w^3)/3)+
      p3 sigma*n*(coeff n (w^2)-coeff n (w^3)/3)+
      i10 kappa c*coeff (n+2) w+i11 kappa c*coeff (n+1) w+
      i20 kappa c*coeff (n+2) (w^2)+i21 kappa c*coeff (n+1) (w^2)+
      i30 kappa c*coeff (n+2) (w^3)+i31 kappa c*coeff (n+1) (w^3)+
      i40 kappa c*coeff (n+2) (w^4)+i41 kappa c*coeff (n+1) (w^4)=0 := by
  have h := congrArg (coeff (n+2) : Series → ℝ) he
  rw [residual_expansion] at h
  rw [show pref sigma*(derivative (w^2)-C (1/3)*derivative (w^3))=
    pref sigma*derivative (w^2)-C (1/3)*(pref sigma*derivative (w^3)) by ring] at h
  simp only [map_add,map_sub,map_zero,coeff_C_mul,coeff_pref_derivative,
    EulerFormal.coeff_affine_mul] at h
  have hx : coeff (n+2) (X : Series)=0 := by simp [coeff_X,show n+2≠1 by omega]
  rw [hx] at h
  linear_combination h

end SepticProfile.ExteriorJet

end
end

end OAI
