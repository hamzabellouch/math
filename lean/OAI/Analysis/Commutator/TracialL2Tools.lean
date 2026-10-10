import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.TracialL2

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ)

def norm (a : A) : ℝ := ‖τ.toPreGNS a‖

lemma norm_nonneg (a : A) : 0≤norm τ a := _root_.norm_nonneg _

lemma norm_sq (a : A) : norm τ a^2=(τ (star a*a)).re := by
  rw [norm,InnerProductSpace.norm_sq_eq_re_inner (𝕜:=ℂ)]
  rfl

@[simp] lemma norm_zero : norm τ 0=0 := by simp [norm]

lemma norm_add (a b : A) : norm τ (a+b)≤norm τ a+norm τ b := by
  simpa only [norm,map_add] using norm_add_le (τ.toPreGNS a) (τ.toPreGNS b)

lemma norm_sub (a b : A) : norm τ (a-b)≤norm τ a+norm τ b := by
  simpa only [norm,map_sub] using norm_sub_le (τ.toPreGNS a) (τ.toPreGNS b)

lemma norm_smul (c : ℂ) (a : A) : norm τ (c • a)=‖c‖*norm τ a := by
  simp only [norm,map_smul,_root_.norm_smul]

lemma norm_real_smul (c : ℝ) (a : A) : norm τ (c • a)=|c| *norm τ a := by
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),norm_smul]
  congr 1
  exact RCLike.norm_ofReal _

lemma norm_mul_left (a b : A) : norm τ (a*b)≤‖a‖*norm τ b := by
  change ‖τ.leftMulMapPreGNS a (τ.toPreGNS b)‖≤‖a‖*‖τ.toPreGNS b‖
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right
      (LinearMap.mkContinuous_norm_le _ (_root_.norm_nonneg _) _) (_root_.norm_nonneg _))

variable (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

include hτ in
lemma norm_star (a : A) : norm τ (star a)=norm τ a := by
  apply (sq_eq_sq₀ (norm_nonneg τ _) (norm_nonneg τ _)).mp
  rw [norm_sq,norm_sq,star_star,hτ]

include hτ in
lemma norm_mul_right (a b : A) : norm τ (a*b)≤norm τ a*‖b‖ := by
  calc
    _=norm τ (star b*star a) := by rw [←star_mul,norm_star τ hτ]
    _≤‖star b‖*norm τ (star a) := norm_mul_left τ _ _
    _=_ := by rw [_root_.norm_star,norm_star τ hτ,mul_comm]

include hτ in
lemma norm_trace_mul (a b : A) : ‖τ (a*b)‖≤norm τ a*norm τ b := by
  have h := norm_inner_le_norm (𝕜:=ℂ) (τ.toPreGNS (star a)) (τ.toPreGNS b)
  change ‖τ (star (star a)*b)‖≤norm τ (star a)*norm τ b at h
  simpa only [star_star,norm_star τ hτ] using h

lemma norm_projection_sq {p : A} (hp : IsStarProjection p) : norm τ p^2=(τ p).re := by
  rw [norm_sq,hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq]

lemma norm_mono_square {a b : A} (hab : star a*a ≤ star b*b) : norm τ a≤norm τ b := by
  apply (sq_le_sq₀ (norm_nonneg τ _) (norm_nonneg τ _)).mp
  rw [norm_sq,norm_sq]
  exact (τ.monotone hab).1

lemma norm_le_opnorm (hone : τ 1=1) (a : A) : norm τ a≤‖a‖ := by
  have h1 : norm τ (1:A)=1 := by
    have h := norm_sq τ (1:A)
    simp only [star_one,mul_one,hone,Complex.one_re] at h
    nlinarith [norm_nonneg τ (1:A)]
  simpa only [mul_one,h1] using norm_mul_left τ a 1

include hτ in
lemma trace_two_corner_letters {q a b c w z : A} (_hq : IsStarProjection q)
    (hw : w*q=w) (hz : q*z=z)
    (ha : ‖a‖≤1) (hc : ‖c‖≤1) (hwn : ‖w‖≤1) (hzn : ‖z‖≤1) :
    ‖τ (a*w*b*z*c)‖≤norm τ (q*b*q)*norm τ q := by
  have he : τ (a*w*b*z*c)=τ ((q*b*q)*(z*c*a*w)) := by
    calc
      _=τ ((a*w)*(b*(z*c))) := by simp only [mul_assoc]
      _=τ ((b*(z*c))*(a*w)) := hτ _ _
      _=τ (b*(z*c*a*w)) := by simp only [mul_assoc]
      _=τ (q*(b*(z*c*a*w))) := by
        rw [hτ q]
        congr 1
        rw [mul_assoc b, mul_assoc (z*c*a) w q,hw]
      _=_ := by
        congr 1
        have hqR : q*(z*c*a*w)=z*c*a*w := by
          rw [←mul_assoc,←mul_assoc,←mul_assoc,hz]
        rw [mul_assoc (q*b) q,hqR,mul_assoc q b]
  have hnorm : norm τ (z*c*a*w)≤norm τ q := by
    have hzq : z=q*z := hz.symm
    calc
      _≤norm τ (z*c*a)*‖w‖ := norm_mul_right τ hτ _ _
      _≤norm τ (z*c*a) := mul_le_of_le_one_right (norm_nonneg τ _) hwn
      _≤norm τ (z*c)*‖a‖ := norm_mul_right τ hτ _ _
      _≤norm τ (z*c) := mul_le_of_le_one_right (norm_nonneg τ _) ha
      _≤norm τ z*‖c‖ := norm_mul_right τ hτ _ _
      _≤norm τ z := mul_le_of_le_one_right (norm_nonneg τ _) hc
      _=norm τ (q*z) := congrArg (norm τ) hzq
      _≤norm τ q*‖z‖ := norm_mul_right τ hτ _ _
      _≤norm τ q := mul_le_of_le_one_right (norm_nonneg τ _) hzn
  rw [he]
  exact (norm_trace_mul τ hτ _ _).trans
    (mul_le_mul_of_nonneg_left hnorm (norm_nonneg τ _))

end Kadison.TracialL2

end

end
end

end OAI
