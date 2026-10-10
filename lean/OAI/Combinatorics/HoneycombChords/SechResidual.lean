import OAI.Combinatorics.HoneycombChords.FamilyGram
import OAI.Combinatorics.HoneycombChords.SechExpectation
import OAI.Combinatorics.HoneycombChords.CauchyResidual

namespace OAI

/-! Polynomial generating functions and hyperbolic secant Gram residuals. -/

section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real Filter Topology MeasureTheory
open Analytic
noncomputable def alpha (c : ℝ) : ℝ := Real.pi/(2*c)
noncomputable def A (c m x : ℝ) : ℝ := Real.cos (alpha c*m)*(C m x).re
noncomputable def w (c m : ℝ) : ℝ := Real.tan (alpha c*m)^2
lemma sec_pair_identity {a b : ℝ} (h : |a|+|b| < Real.pi/2) :
    Real.cos a*Real.cos b*(1/Real.cos (a+b)+1/Real.cos (a-b))/2=
      1/(1-Real.tan a^2*Real.tan b^2) := by
  have hp := (Real.cos_pos_of_mem_Ioo (abs_lt.mp (lt_of_le_of_lt (abs_add_le a b) h))).ne'
  have hm := (Real.cos_pos_of_mem_Ioo (abs_lt.mp (lt_of_le_of_lt (abs_sub a b) h))).ne'
  have ha := (Real.cos_pos_of_mem_Ioo (abs_lt.mp (show |a| < Real.pi/2 by linarith [abs_nonneg b]))).ne'
  have hb := (Real.cos_pos_of_mem_Ioo (abs_lt.mp (show |b| < Real.pi/2 by linarith [abs_nonneg a]))).ne'
  have hd : Real.cos (a+b)*Real.cos (a-b)=Real.cos a^2*Real.cos b^2-Real.sin a^2*Real.sin b^2 := by
    rw [Real.cos_add,Real.cos_sub];ring
  have ht : 1-Real.tan a^2*Real.tan b^2=
      Real.cos (a+b)*Real.cos (a-b)/(Real.cos a^2*Real.cos b^2) := by
    rw [hd,Real.tan_eq_sin_div_cos,Real.tan_eq_sin_div_cos]
    field_simp
  rw [ht]
  field_simp [ha,hb,hp,hm]
  rw [Real.cos_add,Real.cos_sub]
  ring
lemma alpha_pair_bound {c m n : ℝ} (hc : 0 < c) (h : |m|+|n| < c) :
    |alpha c*m|+|alpha c*n| < Real.pi/2 := by
  have hα : 0 < alpha c := by unfold alpha;positivity
  have he : alpha c*c=Real.pi/2 := by unfold alpha;field_simp
  rw [abs_mul,abs_mul,abs_of_pos hα,←mul_add,←he]
  exact mul_lt_mul_of_pos_left h hα
lemma A_sq (c m : ℝ) {p : ℝ} (hp : 0 ≤ p) :
    A c m (p^2)=Real.cos (alpha c*m)*Real.cosh (m*p) := by
  simp only [A,C_sq m hp,Complex.ofReal_re]
lemma A_pair_integrable {c m n : ℝ} (hc : 0 < c) (h : |m|+|n| < c) :
    IntegrableOn (fun p => A c m (p^2)*A c n (p^2)/Real.cosh (c*p)) (Set.Ioi 0) := by
  apply ((sech_pair_integrable hc h).const_mul (Real.cos (alpha c*m)*Real.cos (alpha c*n))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  rw [A_sq c m hp.le,A_sq c n hp.le]
  ring

lemma polynomial_generating_identity {c m n : ℝ} (hc : 0 < c) (h : |m|+|n| < c) :
    sechExpectation c (fun x => A c m x*A c n x)=1/(1-w c m*w c n) := by
  have he : (∫ p in Set.Ioi (0:ℝ),A c m (p^2)*A c n (p^2)/Real.cosh (c*p))=
      (Real.cos (alpha c*m)*Real.cos (alpha c*n))*
        ∫ p in Set.Ioi (0:ℝ),Real.cosh (m*p)*Real.cosh (n*p)/Real.cosh (c*p) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    rw [A_sq c m hp.le,A_sq c n hp.le]
    ring
  unfold sechExpectation
  rw [he,sech_pair_integral hc h]
  have hp : Real.pi*(m+n)/(2*c)=alpha c*m+alpha c*n := by unfold alpha;ring
  have hm : Real.pi*(m-n)/(2*c)=alpha c*m-alpha c*n := by unfold alpha;ring
  rw [hp,hm]
  have coeff : (2*c/Real.pi)*(Real.pi/(4*c))=(1:ℝ)/2 := by field_simp; ring
  calc
    _=(Real.cos (alpha c*m)*Real.cos (alpha c*n)) *
      (1/Real.cos (alpha c*m+alpha c*n)+1/Real.cos (alpha c*m-alpha c*n))/2 := by
        calc
          _=((2*c/Real.pi)*(Real.pi/(4*c)))*
            ((Real.cos (alpha c*m)*Real.cos (alpha c*n))*
              (1/Real.cos (alpha c*m+alpha c*n)+1/Real.cos (alpha c*m-alpha c*n))) := by ring
          _=_ := by rw [coeff];ring
    _=1/(1-w c m*w c n) := sec_pair_identity (alpha_pair_bound hc h)
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Honeycomb370 Matrix Finset MeasureTheory

lemma meanResidualRatio_coefficients {n : ℕ} (w : ℝ → ℝ) (F G : Fin n → ℝ → ℝ)
    (H : ℝ → ℝ) (a : ℝ) (c : Fin n → ℝ)
    (hi : ∀ i j,IntegrableOn (fun p ↦ F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (hH : ∀ j,IntegrableOn (fun p ↦ H (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (hd : (familyGram w F G).det≠0) (ha : H a≠0)
    (horth : c ᵥ* familyGram w F G=fun j ↦ ∫ p in Set.Ioi 0,H (p^2)*G j (p^2)*w p) :
    H a*meanResidualRatio w F G H a=H a-∑ i,c i*F i a := by
  rw [meanResidualRatio_formula w F G H a hi hH hd,←horth,
    Matrix.dotProduct_mulVec,Matrix.vecMul_vecMul,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd),
    Matrix.vecMul_one]
  simp only [dotProduct,mul_sub,mul_one,mul_sum]
  congr 1
  apply sum_congr rfl
  intro i _
  field_simp

/-- Binding the explicit Cauchy model estimate to the actual nonsymmetric
Gram projection. Its analytic realization is supplied by the sech transform. -/
theorem cauchyGram_coefficient_lower (N : ℕ) (q : Fin (2*N) → ℝ) (u t : ℝ)
    (w : ℝ → ℝ) (F G : Fin (2*N+1) → ℝ → ℝ) (H : ℝ → ℝ)
    (hq : ∀ i,0≤q i ∧ q i≤1/2) (hu : 0≤u ∧ u≤1/2) (ht : 0≤t ∧ t≤1/2)
    (hinj : Function.Injective (Fin.lastCases t q))
    (hi : ∀ i j,IntegrableOn (fun p ↦ F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (hH : ∀ j,IntegrableOn (fun p ↦ H (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (hd : (familyGram w F G).det≠0)
    (hGram : ∀ i j,familyGram w F G i j=1/(1-Fin.lastCases u q i*Fin.lastCases t q j))
    (hMom : ∀ j,(∫ p in Set.Ioi 0,H (p^2)*G j (p^2)*w p)=1/(1-Fin.lastCases t q j))
    (hF0 : ∀ i,F i 0=1/Real.sqrt (1+Fin.lastCases u q i)) (hH0 : H 0=1/Real.sqrt 2) :
    1/(68*Real.pi*Real.sqrt ((N:ℝ)+1)) ≤ -(H 0*meanResidualRatio w F G H 0) := by
  let M:=familyGram w F G
  let v:=fun j ↦ ∫ p in Set.Ioi 0,H (p^2)*G j (p^2)*w p
  let c:=v ᵥ* M⁻¹
  have horth : c ᵥ* M=v := by
    dsimp [c]
    rw [Matrix.vecMul_vecMul,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd),Matrix.vecMul_one]
  have hco (j : Fin (2*N+1)) : 1/(1-Fin.lastCases t q j)=
      ∑ i,c i/(1-Fin.lastCases u q i*Fin.lastCases t q j) := by
    have h:=congrFun horth j
    dsimp only [Matrix.vecMul,dotProduct,M,v] at h
    simp_rw [hGram,hMom,mul_one_div] at h
    exact h.symm
  have hh:=cauchyResidual_zero_lower N q u t c hq hu ht hinj hco
  rw [meanResidualRatio_coefficients w F G H 0 c hi hH hd (by rw [hH0]; positivity) horth,hH0]
  simpa only [hF0,mul_one_div] using hh

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Honeycomb370 Matrix Finset MeasureTheory Real

noncomputable def sechProbDensity (c p : ℝ) : ℝ := (2*c/Real.pi)/Real.cosh (c*p)

lemma A_pair_prob_integrable {c m n : ℝ} (hc : 0<c) (h : |m|+|n|<c) :
    IntegrableOn (fun p ↦ A c m (p^2)*A c n (p^2)*sechProbDensity c p) (Set.Ioi 0) := by
  apply ((A_pair_integrable hc h).const_mul (2*c/Real.pi)).congr
  filter_upwards with p
  unfold sechProbDensity
  ring

lemma A_pair_prob_integral {c m n : ℝ} (hc : 0<c) (h : |m|+|n|<c) :
    (∫ p in Set.Ioi 0,A c m (p^2)*A c n (p^2)*sechProbDensity c p)=1/(1-w c m*w c n) := by
  have he : (fun p ↦ A c m (p^2)*A c n (p^2)*sechProbDensity c p)=
      fun p ↦ (2*c/Real.pi)*(A c m (p^2)*A c n (p^2)/Real.cosh (c*p)) := by
    funext p
    unfold sechProbDensity
    ring
  rw [he,integral_const_mul]
  exact polynomial_generating_identity hc h

lemma alpha_mul_third {c : ℝ} (hc : c≠0) : alpha c*(c/3)=Real.pi/6 := by
  unfold alpha
  field_simp
  ring

lemma alpha_mul_half {c : ℝ} (hc : c≠0) : alpha c*(c/2)=Real.pi/4 := by
  unfold alpha
  field_simp
  ring

lemma w_bounds_third {c m : ℝ} (hc : 0<c) (hm : 0 ≤ m) (hm' : m ≤ c/3) :
    0 ≤ w c m ∧ w c m ≤ 1/2 := by
  have ha : 0<alpha c := by unfold alpha; positivity
  have hm0 : 0 ≤ alpha c*m := mul_nonneg ha.le hm
  have hm1 : alpha c*m ≤ Real.pi/6 := by
    rw [←alpha_mul_third hc.ne']
    exact mul_le_mul_of_nonneg_left hm' ha.le
  have ht0 : 0 ≤ Real.tan (alpha c*m) := Real.tan_nonneg_of_nonneg_of_le_pi_div_two hm0 (by linarith [Real.pi_pos])
  have ht1 : Real.tan (alpha c*m) ≤ Real.tan (Real.pi/6) := by
    exact Real.strictMonoOn_tan.monotoneOn ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
      ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩ hm1
  rw [Real.tan_pi_div_six] at ht1
  have hs:=Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)
  have hs0 : 0<Real.sqrt 3 := by positivity
  have ht2:=sq_le_sq₀ ht0 (show 0≤1/Real.sqrt 3 by positivity) |>.mpr ht1
  unfold w
  constructor
  · positivity
  · have hsq : (1/Real.sqrt 3)^2=(1:ℝ)/3 := by rw [div_pow,one_pow,hs]
    rw [hsq] at ht2
    linarith

lemma A_zero {c m : ℝ} (hc : 0<c) (hm : |m|<c) :
    A c m 0=1/Real.sqrt (1+w c m) := by
  have ht : |alpha c*m|<Real.pi/2 := by
    have h:=alpha_pair_bound hc (m:=m) (n:=0) (by simpa using hm)
    simpa using h
  have hp := Real.cos_pos_of_mem_Ioo (abs_lt.mp ht)
  have he := Real.inv_sqrt_one_add_tan_sq hp
  simp only [A,C,le_refl,ite_true,Real.sqrt_zero,mul_zero,Real.cosh_zero,
    Complex.ofReal_re,mul_one,w,one_div]
  exact he.symm

lemma w_half {c : ℝ} (hc : c≠0) : w c (c/2)=1 := by
  rw [w,alpha_mul_half hc,Real.tan_pi_div_four]
  norm_num

lemma w_injectiveOn_third {c : ℝ} (hc : 0<c) : Set.InjOn (w c) (Set.Icc 0 (c/3)) := by
  intro m hm n hn h
  have ha : 0<alpha c := by unfold alpha; positivity
  have hmb : 0 ≤ alpha c*m ∧ alpha c*m ≤ Real.pi/6 :=
    ⟨mul_nonneg ha.le hm.1,by rw [←alpha_mul_third hc.ne']; exact mul_le_mul_of_nonneg_left hm.2 ha.le⟩
  have hnb : 0 ≤ alpha c*n ∧ alpha c*n ≤ Real.pi/6 :=
    ⟨mul_nonneg ha.le hn.1,by rw [←alpha_mul_third hc.ne']; exact mul_le_mul_of_nonneg_left hn.2 ha.le⟩
  have htm:=Real.tan_nonneg_of_nonneg_of_le_pi_div_two hmb.1 (show alpha c*m≤Real.pi/2 by linarith [Real.pi_pos])
  have htn:=Real.tan_nonneg_of_nonneg_of_le_pi_div_two hnb.1 (show alpha c*n≤Real.pi/2 by linarith [Real.pi_pos])
  have he : Real.tan (alpha c*m)=Real.tan (alpha c*n) := (sq_eq_sq₀ htm htn).mp h
  have hh:=Real.strictMonoOn_tan.injOn
    (show alpha c*m∈Set.Ioo (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_pos])
    (show alpha c*n∈Set.Ioo (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_pos]) he
  exact mul_left_cancel₀ ha.ne' hh

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open MeasureTheory

lemma sech_label_margin {b c : ℝ} (hb : b ≤ (3*angle/2)^2) (hc : c ≤ angle^2) :
    Real.sqrt (b+angle^2/100)+Real.sqrt (c+angle^2/100)<3*angle := by
  have hangle := strip_angle_pos
  have hb' : Real.sqrt (b+angle^2/100) ≤ 8*angle/5 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg angle]
  have hc' : Real.sqrt (c+angle^2/100) ≤ 6*angle/5 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg angle]
  linarith [strip_angle_pos]

lemma sech_jet_pair_integrable {b c : ℝ} (hb0 : 0 ≤ b) (hc0 : 0 ≤ c)
    (hb : b ≤ (3*angle/2)^2) (hc : c ≤ angle^2) (r s : ℕ) :
    IntegrableOn (fun p ↦ cosineKernelJet r 0 b (p^2)*cosineKernelJet s 0 c (p^2)*
      sechProbDensity (3*angle) p) (Set.Ioi 0) := by
  have hangle := strip_angle_pos
  let δ := angle^2/100
  have hd : 0<δ := by dsimp [δ]; positivity
  have hmargin : |Real.sqrt (b+δ)|+|Real.sqrt (c+δ)|<3*angle := by
    simp only [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact sech_label_margin hb hc
  have hi := (Analytic.sech_pair_integrable (show 0<3*angle by positivity) hmargin).const_mul
    (δ^(-(r:ℤ))*δ^(-(s:ℤ))*(2*(3*angle)/Real.pi))
  apply hi.mono'
  · exact ((((cosineKernelJet_contDiff_right r 0 b 0).continuous.comp (continuous_id.pow 2)).measurable.mul
      (((cosineKernelJet_contDiff_right s 0 c 0).continuous.comp (continuous_id.pow 2)).measurable)).mul
      (by unfold sechProbDensity; fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    have hr := cosineKernelJet_label_bound hb0 (sq_nonneg p) hd r
    have hs := cosineKernelJet_label_bound hc0 (sq_nonneg p) hd s
    have he1 : cosineKernelJet 0 0 (b+δ) (p^2)=Real.cosh (Real.sqrt (b+δ)*p) := by
      rw [cosineKernelJet_zero_zero_cosh (by positivity) (sq_nonneg p),Real.sqrt_sq hp.le]
    have he2 : cosineKernelJet 0 0 (c+δ) (p^2)=Real.cosh (Real.sqrt (c+δ)*p) := by
      rw [cosineKernelJet_zero_zero_cosh (by positivity) (sq_nonneg p),Real.sqrt_sq hp.le]
    rw [he1] at hr
    rw [he2] at hs
    rw [Real.norm_of_nonneg (by apply mul_nonneg (mul_nonneg (cosineKernelJet_nonneg hb0 (sq_nonneg p) _ _)
      (cosineKernelJet_nonneg hc0 (sq_nonneg p) _ _)); unfold sechProbDensity; positivity)]
    calc
      _ ≤ (δ^(-(r:ℤ))*Real.cosh (Real.sqrt (b+δ)*p))*(δ^(-(s:ℤ))*Real.cosh (Real.sqrt (c+δ)*p))*
          sechProbDensity (3*angle) p := by
        apply mul_le_mul_of_nonneg_right _ (by unfold sechProbDensity; positivity)
        exact mul_le_mul hr hs (cosineKernelJet_nonneg hc0 (sq_nonneg p) _ _) (by positivity)
      _ = _ := by unfold sechProbDensity; ring

lemma sech_jet_gram_det_pos {n : ℕ} (b c : ℕ → ℝ)
    (hb : Monotone (fun i : Fin n ↦ b i)) (hc : Monotone (fun i : Fin n ↦ c i))
    (hb0 : ∀ i : Fin n,0 ≤ b i) (hc0 : ∀ i : Fin n,0 ≤ c i)
    (hb1 : ∀ i : Fin n,b i ≤ (3*angle/2)^2) (hc1 : ∀ i : Fin n,c i ≤ angle^2) :
    0 < (jetGram (n:=n) (sechProbDensity (3*angle)) b c).det := by
  have hangle := strip_angle_pos
  apply jetGram_det_pos _ b c hb hc hb0 hc0
  · intro p hp
    unfold sechProbDensity
    positivity
  · intro i j
    exact sech_jet_pair_integrable (hb0 i) (hc0 j) (hb1 i) (hc1 j) _ _

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Finset Matrix MeasureTheory

lemma meanResidualRatio_reindex {n : ℕ} (w : ℝ → ℝ) (F G : Fin n → ℝ → ℝ)
    (H : ℝ → ℝ) (a : ℝ) (e : Equiv.Perm (Fin n)) :
    meanResidualRatio w (F ∘ e) (G ∘ e) H a=meanResidualRatio w F G H a := by
  unfold meanResidualRatio
  have he (f : Fin n → ℝ → ℝ) : familyGram w (f ∘ e) (G ∘ e)=(familyGram w f G).submatrix e e := rfl
  have hr : residualFamily (F ∘ e) H a=(residualFamily F H a) ∘ e := rfl
  rw [hr,he,he,Matrix.det_submatrix_equiv_self,Matrix.det_submatrix_equiv_self]

lemma residualFamily_scale_target {n : ℕ} (F : Fin n → ℝ → ℝ) (H : ℝ → ℝ) (a s : ℝ) (hs : s≠0) :
    residualFamily F (fun x ↦ s*H x) a=residualFamily F H a := by
  funext i x
  unfold residualFamily
  congr 1
  rw [mul_left_comm (F i a) s (H x),mul_div_mul_left _ _ hs]

lemma meanResidualRatio_scale_target {n : ℕ} (w : ℝ → ℝ) (F G : Fin n → ℝ → ℝ)
    (H : ℝ → ℝ) (a s : ℝ) (hs : s≠0) :
    meanResidualRatio w F G (fun x ↦ s*H x) a=meanResidualRatio w F G H a := by
  unfold meanResidualRatio
  rw [residualFamily_scale_target F H a s hs]

lemma finiteFamilyCombination_diagonal {n : ℕ} (F : Fin n → ℝ → ℝ) (u : Fin n → ℝ) (i : Fin n) :
    finiteFamilyCombination F (Matrix.diagonal u i)=fun x ↦ u i*F i x := by
  funext x
  simp [finiteFamilyCombination,Matrix.diagonal_apply]

lemma familyGram_scalars {n : ℕ} (w : ℝ → ℝ) (F G : Fin n → ℝ → ℝ) (u v : Fin n → ℝ)
    (hi : ∀ i j,IntegrableOn (fun p ↦ F i (p^2)*G j (p^2)*w p) (Set.Ioi 0)) :
    familyGram w (fun i x ↦ u i*F i x) (fun j x ↦ v j*G j x)=
      Matrix.diagonal u*familyGram w F G*Matrix.diagonal v := by
  have h:=familyGram_bichange w F G hi (Matrix.diagonal u) (Matrix.diagonal v)
  simpa only [finiteFamilyCombination_diagonal,Matrix.diagonal_transpose] using h

lemma meanResidualRatio_scalars {n : ℕ} (w : ℝ → ℝ) (F G : Fin n → ℝ → ℝ) (H : ℝ → ℝ) (a : ℝ)
    (u v : Fin n → ℝ) (hu : ∀ i,u i≠0) (hv : ∀ i,v i≠0)
    (hi : ∀ i j,IntegrableOn (fun p ↦ F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (hH : ∀ j,IntegrableOn (fun p ↦ H (p^2)*G j (p^2)*w p) (Set.Ioi 0)) :
    meanResidualRatio w (fun i x ↦ u i*F i x) (fun j x ↦ v j*G j x) H a=meanResidualRatio w F G H a := by
  have h:=meanResidualRatio_bichange w F G H a hi hH (Matrix.diagonal u) (Matrix.diagonal v)
    (by rw [Matrix.det_diagonal]; exact prod_ne_zero_iff.mpr (fun i _ ↦ hu i))
    (by rw [Matrix.det_diagonal]; exact prod_ne_zero_iff.mpr (fun i _ ↦ hv i))
  simpa only [finiteFamilyCombination_diagonal] using h

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI
