import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialRegularization
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaProjectedFiniteOrder
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaProjectedLineBounds

namespace OAI

/-! The actual radial pole-removed series has finite vertical order and
polynomial boundary bounds. These estimates use the literal theta tails. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

private lemma finite_order_mul_polynomial {f h : ℂ→ℂ} {a b D : ℝ}
    (hf : FiniteVerticalOrder f a b) (hD : 0≤D) (m : ℕ)
    (hh : ∀ s : ℂ,s.re∈Icc a b → ‖h s‖≤D*(1+|s.im|)^m) :
    FiniteVerticalOrder (fun s => f s*h s) a b := by
  obtain ⟨C,k,hC,hf⟩ := hf
  refine ⟨C+D,max k m,add_nonneg hC hD,?_⟩
  intro s hs
  have hq : 1≤1+|s.im| := by linarith [abs_nonneg s.im]
  have hk : (1+|s.im|)^k≤(1+|s.im|)^(max k m) :=
    pow_le_pow_right₀ hq (le_max_left _ _)
  have hm : (1+|s.im|)^m≤(1+|s.im|)^(max k m) :=
    pow_le_pow_right₀ hq (le_max_right _ _)
  have hexp : D*(1+|s.im|)^m≤Real.exp (D*(1+|s.im|)^m) :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  calc
    ‖f s*h s‖ = ‖f s‖*‖h s‖ := norm_mul _ _
    _ ≤ Real.exp (C*(1+|s.im|)^k)*Real.exp (D*(1+|s.im|)^m) :=
      mul_le_mul (hf s hs) ((hh s hs).trans hexp) (_root_.norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (C*(1+|s.im|)^k+D*(1+|s.im|)^m) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ C*(1+|s.im|)^(max k m)+D*(1+|s.im|)^(max k m) :=
          add_le_add (mul_le_mul_of_nonneg_left hk hC) (mul_le_mul_of_nonneg_left hm hD)
        _ = _ := by ring

lemma cubicTheta_radial_affine_bound (a b : ℝ) (s : ℂ) (hs : s.re∈Icc a b) :
    ‖s-(5/6:ℂ)‖≤(2+|a|+|b|)*(1+|s.im|) := by
  have hr : |s.re|≤|a|+|b| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le a,abs_nonneg b,hs.1]
    · linarith [le_abs_self b,abs_nonneg a,hs.2]
  have he := Complex.norm_le_abs_re_add_abs_im (s-(5/6:ℂ))
  have ht := abs_sub_le s.re 0 (5/6:ℝ)
  simp only [sub_zero,zero_sub,abs_neg] at ht
  norm_num at ht
  norm_num [Complex.sub_re,Complex.sub_im] at he
  nlinarith [abs_nonneg a,abs_nonneg b,abs_nonneg s.im,
    mul_nonneg (abs_nonneg a) (abs_nonneg s.im),
    mul_nonneg (abs_nonneg b) (abs_nonneg s.im)]

lemma cubicThetaSelectedRadialTail_bounded (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (a b : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ s : ℂ,s.re∈Icc a b → ‖cubicThetaSelectedRadialTail g hc s‖≤C := by
  obtain ⟨C,hC,hb⟩ := cubicThetaPairedUpper_bounded_strip
    (cubicThetaSelectedRadialAxis g) (cubicThetaProjectedRadialAxis g hc) 1 0
    (fun s => cubicThetaBoundedScaledUpper_mellinConvergent (by norm_num : (0:ℝ)≤81)
      cubicThetaSelectedCoefficient_arithmetic_bound 0 _ (cubicThetaLevelScale_pos hc) s)
    (fun s => cubicThetaBoundedScaledUpper_mellinConvergent (by norm_num : (0:ℝ)≤243)
      (cubicThetaProjectedCoefficient_arithmetic_bound g hc) 0 _ (cubicThetaLevelScale_pos hc) s)
    (2*a-1) (2*b-1)
  refine ⟨C,hC,?_⟩
  intro s hs
  have hh := hb (2*s-1) (by
    simp only [mem_Icc,Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,
      Complex.one_re,zero_mul,sub_zero]
    constructor <;> linarith [hs.1,hs.2])
  simpa only [cubicThetaSelectedRadialTail,Nat.mul_zero,Nat.cast_zero,zero_sub,one_mul] using hh

lemma cubicThetaSelectedRadialRegularized_finiteOrder (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (a b : ℝ) :
    FiniteVerticalOrder (cubicThetaSelectedRadialRegularized g hc) a b := by
  have hu : FiniteVerticalOrder (cubicThetaAngularUncompletion (g 1 0) 0) a b := by
    simpa only [mul_one] using cubicThetaUncompleted_finiteOrder hc 0 (fun _ => 1)
      (fun _ _ => ⟨1,zero_le_one,fun _ _ => by norm_num⟩) a b
  obtain ⟨C,hC,hT⟩ := cubicThetaSelectedRadialTail_bounded g hc a b
  let D := (2+|a|+|b|)*C+‖cubicThetaProjectedRadialConstant g hc/2‖
  apply finite_order_mul_polynomial hu (show 0≤D by dsimp [D]; positivity) 1
  intro s hs
  rw [pow_one]
  calc
    _ ≤ ‖s-(5/6:ℂ)‖*‖cubicThetaSelectedRadialTail g hc s‖+
        ‖cubicThetaProjectedRadialConstant g hc/2‖ := by
          exact (norm_add_le _ _).trans_eq (by rw [norm_mul])
    _ ≤ ((2+|a|+|b|)*(1+|s.im|))*C+‖cubicThetaProjectedRadialConstant g hc/2‖ := by
      gcongr
      · exact cubicTheta_radial_affine_bound a b s hs
      · exact hT s hs
    _ ≤ D*(1+|s.im|) := by
      dsimp [D]
      nlinarith [abs_nonneg s.im,mul_nonneg (_root_.norm_nonneg
        (cubicThetaProjectedRadialConstant g hc/2)) (abs_nonneg s.im)]

lemma cubicThetaSelectedRadialDirichlet_right_bound (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) {σ : ℝ} (hσ : 3/2<σ) (s : ℂ) (hs : s.re=σ) :
    ‖cubicThetaSelectedRadialDirichlet g hc s‖≤81*cubicThetaDirichletNormMass (2*σ-1) := by
  rw [cubicThetaSelectedRadialDirichlet_initial g hc (by linarith)]
  apply cubicThetaDirichlet_norm_le (fun n _hn => ?_) (by linarith : 2<2*σ-1) _ (by
    simp only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,
      Complex.one_re,zero_mul,sub_zero,hs])
  rw [cubicThetaCoefficientTwist_norm]
  exact cubicThetaSelectedCoefficient_norm n

lemma cubicThetaProjectedRadialDirichlet_right_bound (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) {σ : ℝ} (hσ : 3/2<σ) (s : ℂ) (hs : s.re=σ) :
    ‖cubicThetaProjectedRadialDirichlet g hc s‖≤243*cubicThetaDirichletNormMass (2*σ-1) := by
  rw [cubicThetaProjectedRadialDirichlet_initial g hc (by linarith)]
  apply cubicThetaDirichlet_norm_le (fun n _hn => ?_) (by linarith : 2<2*σ-1) _ (by
    simp only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,
      Complex.one_re,zero_mul,sub_zero,hs])
  rw [cubicThetaCoefficientTwist_norm]
  exact cubicThetaProjectedCoefficient_bound g hc n

lemma cubicThetaSelectedRadialDirichlet_left_bound (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) {m : ℕ} (hm : 2 ≤ m) :
    ∃ C : ℝ,0≤C ∧ ∀ s : ℂ,s.re=1/2-(m:ℝ) →
      ‖cubicThetaSelectedRadialDirichlet g hc s‖≤C*(1+|s.im|)^(4*m) := by
  obtain ⟨G,hG,hΓ⟩ := metaplecticGamma_half_integer_bound 0 m
  let A := cubicThetaLevelScale (g 1 0)^(-4*(m:ℝ))*(2*Real.pi)^(-4*(m:ℝ))
  let B := 243*cubicThetaDirichletNormMass (2*(m:ℝ))
  have hA : 0≤A := mul_nonneg (Real.rpow_nonneg (cubicThetaLevelScale_pos hc).le _)
    (Real.rpow_nonneg (by positivity) _)
  have hB : 0≤B := mul_nonneg (by norm_num) (cubicThetaDirichletNormMass_nonneg _)
  refine ⟨A*G*B,by positivity,?_⟩
  intro s hs
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have he : s=(1/2:ℂ)-(m:ℂ)+(s.im:ℂ)*Complex.I := by
    apply Complex.ext <;> simp [hs]
  have hgamma : ‖metaplecticGammaQuotient 0 s‖≤G*(1+|s.im|)^(4*m) := by
    rw [he]
    simpa using hΓ s.im
  have hdual := cubicThetaProjectedRadialDirichlet_right_bound g hc
    (σ:=1/2+(m:ℝ)) (by linarith) (1-s) (by simp [hs]; ring)
  have hb : ‖cubicThetaProjectedRadialDirichlet g hc (1-s)‖≤B := by
    simpa only [show 2*(1/2+(m:ℝ))-1=2*(m:ℝ) by ring] using hdual
  have hpow : (4*s-2).re= -4*(m:ℝ) := by
    simp only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero,hs]
    ring
  rw [cubicThetaSelectedRadialDirichlet_functional g hc (by linarith),norm_mul,norm_mul,norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (cubicThetaLevelScale_pos hc),
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0<2*Real.pi),hpow]
  calc
    _ ≤ A*(G*(1+|s.im|)^(4*m))*B := by
      change A*‖metaplecticGammaQuotient 0 s‖*‖cubicThetaProjectedRadialDirichlet g hc (1-s)‖≤_
      gcongr
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
