import OAI.MathematicalPhysics.Transonic.Exterior.Scaled

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorJet
open PowerSeries Finset

lemma scaledResidual_expansion (h sigma kappa c : ℝ) (w : Series) :
    scaledResidual h sigma kappa c w=
      (1-C h*X)*(1-C sigma*(1-C h*X)^2)*(2*w-w^2)*derivative w-
      C h*(C (1-c)+2*C c*w-C c*w^2)*
        (C kappa*(1-C h*X)*(2*w-w^2)+3*(w-C h*X)) := by
  unfold scaledResidual scaledPref p0 p1 p2 p3 i10 i11 i20 i21 i30 i31 i40 i41
  simp only [derivative_pow]
  norm_num only [Nat.cast_ofNat,map_mul,map_sub,map_add,map_neg,map_pow,map_one,map_ofNat]
  have hh : (C (1/3) : Series)*3=1 := by
    rw [← map_ofNat C 3,← map_mul];norm_num
  have h3 : ∀ v : Series, C (1/3)*(3*v)=v := by intro v;rw [← mul_assoc,hh,one_mul]
  simp only [mul_assoc,h3]
  ring

lemma scaledResidual_coeff (h sigma kappa c : ℝ) (w : Series) (n : ℕ) :
    coeff (n+2) (scaledResidual h sigma kappa c w)=
      p0 sigma*(n+3)*(coeff (n+3) (w^2)-coeff (n+3) (w^3)/3)+
      h*p1 sigma*(n+2)*(coeff (n+2) (w^2)-coeff (n+2) (w^3)/3)+
      h^2*p2 sigma*(n+1)*(coeff (n+1) (w^2)-coeff (n+1) (w^3)/3)+
      h^3*p3 sigma*n*(coeff n (w^2)-coeff n (w^3)/3)+
      h*i10 kappa c*coeff (n+2) w+h^2*i11 kappa c*coeff (n+1) w+
      h*i20 kappa c*coeff (n+2) (w^2)+h^2*i21 kappa c*coeff (n+1) (w^2)+
      h*i30 kappa c*coeff (n+2) (w^3)+h^2*i31 kappa c*coeff (n+1) (w^3)+
      h*i40 kappa c*coeff (n+2) (w^4)+h^2*i41 kappa c*coeff (n+1) (w^4) := by
  unfold scaledResidual
  rw [show scaledPref h sigma*(derivative (w^2)-C (1/3)*derivative (w^3))=
    scaledPref h sigma*derivative (w^2)-C (1/3)*(scaledPref h sigma*derivative (w^3)) by ring]
  simp only [map_add,map_sub,coeff_C_mul,coeff_scaledPref_derivative,EulerFormal.coeff_affine_mul]
  have hx : coeff (n+2) (X : Series)=0 := by simp [coeff_X,show n+2≠1 by omega]
  rw [hx];ring

lemma scaledResidual_congr (h sigma kappa c : ℝ) (u v : Series) (m : ℕ)
    (hm : 1 ≤ m) (hu0 : coeff 0 u=0) (hdiv : X^m ∣ u-v) :
    X^m ∣ scaledResidual h sigma kappa c u-scaledResidual h sigma kappa c v := by
  obtain ⟨w,hw⟩ := hdiv
  have hu : u=v+X^m*w := by linear_combination hw
  have hu2 : X^m ∣ u^2-v^2 := ⟨w*(u+v),by linear_combination (u+v)*hw⟩
  have hx : X ∣ 2*u-u^2 := by
    rw [X_dvd_iff]
    have hu0' : constantCoeff u=0 := by simpa using hu0
    simp only [map_sub,map_mul,map_ofNat,map_pow,hu0',mul_zero,zero_pow (by norm_num : (2:ℕ)≠0),sub_self]
  obtain ⟨z,hz⟩ := hx
  have hd : derivative u-derivative v=
      (m:ℝ) • (X^(m-1)*w)+X^m*derivative w := by
    rw [hu,map_add,add_sub_cancel_left,Derivation.leibniz,derivative_pow,derivative_X]
    simp only [mul_one,Algebra.smul_def,Algebra.algebraMap_self_apply]
    push_cast;ring
  have hp : X*X^(m-1)=(X:Series)^m := by rw [←pow_succ'];congr 1;omega
  have hd1 : X^m ∣ (2*u-u^2)*(derivative u-derivative v) := by
    refine ⟨(m:ℝ) • (z*w)+X*z*derivative w,?_⟩
    rw [hd,hz]
    simp only [Algebra.smul_def]
    calc
      _ = (m:ℝ) • ((X*X^(m-1))*(z*w))+X^m*(X*z*derivative w) := by
        simp only [Algebra.smul_def];ring
      _ = _ := by rw [hp];simp only [Algebra.smul_def];ring
  have hd2 : X^m ∣ (2*u-u^2)-(2*v-v^2) := by
    convert ((show X^m ∣ u-v from ⟨w,hw⟩).mul_left 2).sub hu2 using 1 ; ring
  have hd3 : X^m ∣ (2*u-u^2)*derivative u-(2*v-v^2)*derivative v := by
    convert hd1.add (hd2.mul_right (derivative v)) using 1 ; ring
  have houter : X^m ∣ (C (1-c)+2*C c*u-C c*u^2)-(C (1-c)+2*C c*v-C c*v^2) := by
    convert ((show X^m ∣ u-v from ⟨w,hw⟩).mul_left (2*C c)).sub (hu2.mul_left (C c)) using 1 ; ring
  have hinner : X^m ∣ (C kappa*(1-C h*X)*(2*u-u^2)+3*(u-C h*X))-
      (C kappa*(1-C h*X)*(2*v-v^2)+3*(v-C h*X)) := by
    convert (hd2.mul_left (C kappa*(1-C h*X))).add
      ((show X^m ∣ u-v from ⟨w,hw⟩).mul_left 3) using 1 ; ring
  rw [scaledResidual_expansion,scaledResidual_expansion]
  have hprod := houter.mul_right (C kappa*(1-C h*X)*(2*u-u^2)+3*(u-C h*X))
  have hprod2 := hinner.mul_left (C (1-c)+2*C c*v-C c*v^2)
  have hprod3 := hprod.add hprod2
  convert (hd3.mul_left ((1-C h*X)*(1-C sigma*(1-C h*X)^2))).sub (hprod3.mul_left (C h)) using 1 ; ring

end SepticProfile.ExteriorJet

end
end

end OAI
