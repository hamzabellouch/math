import OAI.Combinatorics.HoneycombChords.ClosedRows
import OAI.Combinatorics.HoneycombChords.BoundarySystems
import OAI.Combinatorics.HoneycombChords.BulkFusionEquation

namespace OAI

/-! Reflection equations, boundary fusion and bulk fusion.

This development follows the finite strip transfer calculation for critical honeycomb
walks in the companion paper on uniform marked polygon estimates. -/

section
namespace CriticalHoneycomb.Transfer.Reflection
noncomputable def root : ℂ := Complex.exp (((Real.pi/16:ℝ):ℂ)*Complex.I)
noncomputable def point (t : ℝ) : ℂ := Complex.exp ((t:ℂ)*Complex.I)
lemma root_ne_zero : root≠0 := Complex.exp_ne_zero _
lemma point_ne_zero (t : ℝ) : point t≠0 := Complex.exp_ne_zero _
lemma point_add (t u : ℝ) : point (t+u)=point t*point u := by
  simp [point,Complex.ofReal_add,add_mul,Complex.exp_add]
lemma point_sub (t u : ℝ) : point (t-u)=point t/point u := by
  simp [point,Complex.ofReal_sub,sub_mul,Complex.exp_sub]
lemma root_pow (n : ℕ) : root^n=point ((n:ℝ)*(Real.pi/16)) := by
  unfold root point
  rw [←Complex.exp_nat_mul]
  congr 1
  push_cast
  ring
lemma root_sixteen : root^16=-1 := by
  rw [root_pow]
  norm_num [point,show (16:ℝ)*(Real.pi/16)=Real.pi by ring,Complex.exp_pi_mul_I]
lemma root_constraint : root^16+1=0 := by rw [root_sixteen];ring
lemma point_nat_angle (n : ℕ) : point ((n:ℝ)*(Real.pi/16))=root^n := (root_pow n).symm
lemma root_eight : root^8=Complex.I := by
  rw [root_pow]
  convert Complex.exp_pi_div_two_mul_I using 1 ; unfold point ; congr 1 ; push_cast ; ring
lemma root_complement (n : ℕ) (hn : n≤16) : root^n*(-root^(16-n))=1 := by
  rw [mul_neg,←pow_add,Nat.add_sub_of_le hn,root_sixteen]
  ring
lemma point_neg_angle (n : ℕ) (hn : n≤16) : point (-((n:ℝ)*(Real.pi/16)))=-root^(16-n) := by
  apply (mul_left_cancel₀ (pow_ne_zero n root_ne_zero))
  rw [←point_nat_angle,←point_add,add_neg_cancel]
  rw [point_nat_angle,root_complement n hn]
  simp [point]
lemma sine_exp (t : ℝ) : 2*Complex.I*(Real.sin t:ℂ)=point t-point (-t) := by
  have hh:=Complex.two_sin (t:ℂ)
  rw [←Complex.ofReal_sin] at hh
  have hI : Complex.I^2+1=0 := by simp
  simp only [point,Complex.ofReal_neg] at *
  linear_combination Complex.I*hh + (Complex.exp (-(t:ℂ)*Complex.I)-Complex.exp ((t:ℂ)*Complex.I))*hI
lemma sine_positive_shift (n : ℕ) (hn : n≤16) (t : ℝ) :
    (2*Complex.I*point t)*(Real.sin ((n:ℝ)*(Real.pi/16)+t):ℂ)=
      root^n*(point t)^2+root^(16-n) := by
  calc
    _=point t*(point ((n:ℝ)*(Real.pi/16)+t)-point (-((n:ℝ)*(Real.pi/16)+t))) := by
      rw [←sine_exp];ring
    _=root^n*(point t)^2+root^(16-n) := by
      rw [neg_add,point_add,point_add,point_nat_angle,point_neg_angle n hn]
      have hp : point t*point (-t)=1 := by rw [←point_add,add_neg_cancel];simp [point]
      linear_combination root^(16-n)*hp
lemma sine_negative_shift (n : ℕ) (hn : n≤16) (t : ℝ) :
    (2*Complex.I*point t)*(Real.sin ((n:ℝ)*(Real.pi/16)-t):ℂ)=
      root^n+root^(16-n)*(point t)^2 := by
  calc
    _=point t*(point ((n:ℝ)*(Real.pi/16)-t)-point (-((n:ℝ)*(Real.pi/16)-t))) := by
      rw [←sine_exp];ring
    _=root^n+root^(16-n)*(point t)^2 := by
      simp only [sub_eq_add_neg,neg_add,neg_neg,point_add,point_nat_angle,point_neg_angle n hn]
      have hp : point t*point (-t)=1 := by rw [←point_add,add_neg_cancel];simp [point]
      linear_combination root^n*hp
lemma sine_zero_shift (t : ℝ) :
    (2*Complex.I*point t)*(Real.sin t:ℂ)=(point t)^2-1 := by
  have hh:=sine_positive_shift 0 (by omega) t
  simpa [root_sixteen,sub_eq_add_neg] using hh
end CriticalHoneycomb.Transfer.Reflection

end

section
namespace CriticalHoneycomb.Transfer.Reflection
noncomputable def sine (t : ℝ) : ℂ := (Real.sin t:ℂ)
noncomputable def tau (t : ℝ) : ℂ := 2*Complex.I*point t
noncomputable def S : ℂ := sine (Real.pi/4)
noncomputable def gamma : ℝ := 3*Real.pi/16
noncomputable def b : ℝ := 3*Real.pi/8
noncomputable def L : ℝ := Real.pi/8
noncomputable def phase : ℂ := point (Real.pi/4)
noncomputable def Q (u : ℝ) : ℂ := sine (Real.pi/4+u)*sine (b+u)
noncomputable def coeffA (u : ℝ) : ℂ := S*sine (b-u)
noncomputable def coeffH (u : ℝ) : ℂ := S*sine u
noncomputable def coeffV (u : ℝ) : ℂ := sine (b-u)*sine u
noncomputable def coeffC (u : ℝ) : ℂ := sine (b-u)*sine (Real.pi/4-u)
noncomputable def coeffD (u : ℝ) : ℂ := sine u*sine (u-L)
noncomputable def bulkNumerator (u : ℝ) : Matrix Pair Pair ℂ := fun p q=>
  match p.1.val,p.2.val,q.1.val,q.2.val with
  | 0,0,0,0 => coeffC u
  | 2,2,2,2 => coeffC u
  | 0,1,0,1 => coeffV u
  | 1,0,1,0 => coeffV u
  | 2,1,2,1 => coeffV u
  | 1,2,1,2 => coeffV u
  | 0,1,1,0 => coeffA u
  | 1,0,0,1 => coeffA u
  | 2,1,1,2 => coeffA u
  | 1,2,2,1 => coeffA u
  | 0,2,0,2 => coeffD u
  | 0,2,1,1 => coeffH u/phase
  | 0,2,2,0 => coeffC u+coeffD u/phase^2
  | 1,1,0,2 => coeffH u*phase
  | 1,1,1,1 => Q u
  | 1,1,2,0 => coeffH u/phase
  | 2,0,0,2 => coeffC u+coeffD u*phase^2
  | 2,0,1,1 => coeffH u*phase
  | 2,0,2,0 => coeffD u
  | _,_,_,_ => 0

noncomputable def spectralR (u : ℝ) : Matrix Pair Pair ℂ := (Q u)⁻¹ • bulkNumerator u
noncomputable def boundary0 (t : ℝ) : Matrix (Fin 3) (Fin 3) ℂ := fun p q=>
  if p=q then if p=1 then 1 else sine (gamma-t)/sine (gamma+t) else 0
noncomputable def boundary1 (t : ℝ) : Matrix (Fin 3) (Fin 3) ℂ := fun p q=>
  if p=0 ∧ q=1 then sine (2*t)/sine (gamma+t) else
  if p=1 ∧ q=2 then phase*(sine (2*t)/sine (gamma+t)) else 0
lemma tau_ne_zero (t : ℝ) : tau t≠0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (point_ne_zero t)
lemma phase_eq : phase=root^4 := by
  convert point_nat_angle 4 using 1 ; unfold phase ; congr 1 ; ring
lemma phase_inv : phase⁻¹=-root^12 := by
  apply (mul_left_cancel₀ (point_ne_zero (Real.pi/4)))
  change phase*phase⁻¹=phase*(-root^12)
  have hn : phase≠0 := point_ne_zero _
  rw [mul_inv_cancel₀ hn,phase_eq]
  exact (root_complement 4 (by omega)).symm
lemma phase_inv_sq : (phase^2)⁻¹=-root^8 := by
  rw [←inv_pow,phase_inv,neg_sq,←pow_mul]
  have hh : root^24=root^16*root^8 := by rw [←pow_add]
  rw [hh,root_sixteen];ring
lemma sin_b_minus (u : ℝ) : tau u*sine (b-u)=root^6+root^10*(point u)^2 := by
  convert sine_negative_shift 6 (by omega) u using 1 ; unfold tau sine b ; congr 2 ; ring_nf
lemma sin_quarter_minus (u : ℝ) : tau u*sine (Real.pi/4-u)=root^4+root^12*(point u)^2 := by
  convert sine_negative_shift 4 (by omega) u using 1 ; unfold tau sine ; congr 2 ; ring_nf
lemma sin_b_plus (u : ℝ) : tau u*sine (b+u)=root^6*(point u)^2+root^10 := by
  convert sine_positive_shift 6 (by omega) u using 1 ; unfold tau sine b ; congr 2 ; ring_nf
lemma sin_quarter_plus (u : ℝ) : tau u*sine (Real.pi/4+u)=root^4*(point u)^2+root^12 := by
  convert sine_positive_shift 4 (by omega) u using 1 ; unfold tau sine ; congr 2 ; ring_nf
lemma sin_minus_L (u : ℝ) : tau u*sine (u-L)=-root^2-root^14*(point u)^2 := by
  have hh:=sine_negative_shift 2 (by omega) u
  have he : u-L=-(2*(Real.pi/16)-u) := by unfold L;ring
  rw [he]; simp only [sine,Real.sin_neg,Complex.ofReal_neg,mul_neg]
  rw [show 2*(Real.pi/16)=((2:ℕ):ℝ)*(Real.pi/16) by norm_num]
  change -(tau u*sine (((2:ℕ):ℝ)*(Real.pi/16)-u))=_
  change tau u*sine (((2:ℕ):ℝ)*(Real.pi/16)-u)=_ at hh
  rw [hh];ring
lemma sin_zero (u : ℝ) : tau u*sine u=(point u)^2-1 := sine_zero_shift u
lemma sin_S (u : ℝ) : tau u*S=(root^4+root^12)*point u := by
  have hh:=sine_positive_shift 4 (by omega) 0
  have h0 : point 0=1 := by simp [point]
  rw [h0] at hh
  have ht : tau u=(2*Complex.I)*point u := rfl
  change tau u*sine (Real.pi/4)=_
  have hs : 2*Complex.I*sine (Real.pi/4)=root^4+root^12 := by
    simpa only [sine,Nat.cast_ofNat,show (4:ℝ)*(Real.pi/16)+0=Real.pi/4 by ring,
      one_pow,mul_one,Nat.reduceSub] using hh
  rw [ht,mul_assoc,mul_comm (point u),←mul_assoc,hs]
lemma coeffA_scaled (u : ℝ) : (tau u)^2*coeffA u=(root^4+root^12)*(point u)*(root^6+root^10*(point u)^2) := by
  rw [coeffA,show (tau u)^2*(S*sine (b-u))=(tau u*S)*(tau u*sine (b-u)) by ring,sin_S,sin_b_minus]
lemma coeffH_scaled (u : ℝ) : (tau u)^2*coeffH u=(root^4+root^12)*(point u)*((point u)^2-1) := by
  rw [coeffH,show (tau u)^2*(S*sine u)=(tau u*S)*(tau u*sine u) by ring,sin_S,sin_zero]
lemma coeffV_scaled (u : ℝ) : (tau u)^2*coeffV u=(root^6+root^10*(point u)^2)*((point u)^2-1) := by
  rw [coeffV,show (tau u)^2*(sine (b-u)*sine u)=(tau u*sine (b-u))*(tau u*sine u) by ring,sin_b_minus,sin_zero]
lemma coeffC_scaled (u : ℝ) : (tau u)^2*coeffC u=(root^6+root^10*(point u)^2)*(root^4+root^12*(point u)^2) := by
  rw [coeffC,show (tau u)^2*(sine (b-u)*sine (Real.pi/4-u))=(tau u*sine (b-u))*(tau u*sine (Real.pi/4-u)) by ring,sin_b_minus,sin_quarter_minus]
lemma coeffD_scaled (u : ℝ) : (tau u)^2*coeffD u=((point u)^2-1)*(-root^2-root^14*(point u)^2) := by
  rw [coeffD,show (tau u)^2*(sine u*sine (u-L))=(tau u*sine u)*(tau u*sine (u-L)) by ring,sin_zero,sin_minus_L]
lemma Q_scaled (u : ℝ) : (tau u)^2*Q u=(root^4*(point u)^2+root^12)*(root^6*(point u)^2+root^10) := by
  rw [Q,show (tau u)^2*(sine (Real.pi/4+u)*sine (b+u))=(tau u*sine (Real.pi/4+u))*(tau u*sine (b+u)) by ring,sin_quarter_plus,sin_b_plus]
lemma bulk_scaled (u : ℝ) : (tau u)^2 • bulkNumerator u=rNumerator root (point u) 1 := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp only [Matrix.smul_apply,smul_eq_mul,bulkNumerator,rNumerator,one_pow,mul_one,div_eq_mul_inv]
  all_goals try simp only [phase_inv,phase_inv_sq]
  all_goals try simp only [phase_eq,mul_add,←mul_assoc,
      coeffA_scaled,coeffH_scaled,coeffV_scaled,coeffC_scaled,coeffD_scaled,Q_scaled]
  all_goals ring
lemma r_homogeneous (r z w v : ℂ) : rNumerator r (z*v) (w*v)=v^4 • rNumerator r z w := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp only [Matrix.smul_apply,smul_eq_mul,rNumerator] <;> ring
lemma spectralR_scaled (u : ℝ) (hQ : Q u≠0) :
    ((tau u)^2*Q u) • spectralR u=rNumerator root (point u) 1 := by
  rw [spectralR,smul_smul,mul_assoc,mul_inv_cancel₀ hQ,mul_one,bulk_scaled]

lemma sin_gamma_minus (t : ℝ) : tau t*sine (gamma-t)=root^3+root^13*(point t)^2 := by
  convert sine_negative_shift 3 (by omega) t using 1 ; unfold tau sine gamma ; congr 2 ; ring_nf
lemma sin_gamma_plus (t : ℝ) : tau t*sine (gamma+t)=root^3*(point t)^2+root^13 := by
  convert sine_positive_shift 3 (by omega) t using 1 ; unfold tau sine gamma ; congr 2 ; ring_nf
noncomputable def beta (t : ℝ) : ℂ := point t*tau t*sine (gamma+t)
lemma beta_ne_zero (t : ℝ) (ht : sine (gamma+t)≠0) : beta t≠0 :=
  mul_ne_zero (mul_ne_zero (point_ne_zero t) (tau_ne_zero t)) ht
lemma beta_polynomial (t : ℝ) : beta t=point t*(root^3*(point t)^2+root^13) := by
  rw [beta,mul_assoc,sin_gamma_plus]
lemma beta_k (t : ℝ) (ht : sine (gamma+t)≠0) :
    beta t*(sine (gamma-t)/sine (gamma+t))=point t*(root^3+root^13*(point t)^2) := by
  calc
    _=point t*(tau t*sine (gamma-t)) := by unfold beta;field_simp [ht] 
    _=_ := by rw [sin_gamma_minus]
lemma point_twice (t : ℝ) : point (2*t)=(point t)^2 := by
  rw [two_mul,point_add,pow_two]
lemma beta_l (t : ℝ) (ht : sine (gamma+t)≠0) :
    beta t*(sine (2*t)/sine (gamma+t))=(point t)^4-1 := by
  calc
    _=tau (2*t)*sine (2*t) := by unfold beta tau;rw [point_twice];field_simp [ht] 
    _=_ := by rw [sin_zero,point_twice];ring
lemma boundary0_scaled (t : ℝ) (ht : sine (gamma+t)≠0) :
    beta t • boundary0 t=dConstant root (point t) := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [Matrix.smul_apply,smul_eq_mul,boundary0,dConstant,beta_k t ht]
  all_goals exact beta_polynomial t
lemma boundary1_scaled (t : ℝ) (ht : sine (gamma+t)≠0) :
    beta t • boundary1 t=dLinear root (point t) := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [Matrix.smul_apply,smul_eq_mul,boundary1,dLinear,phase_eq,
      show beta t*(root^4*(sine (2*t)/sine (gamma+t)))=
        root^4*(beta t*(sine (2*t)/sine (gamma+t))) by ring,beta_l t ht]
end CriticalHoneycomb.Transfer.Reflection

end

section
namespace CriticalHoneycomb.Transfer.Reflection
open scoped Matrix
noncomputable def alphaMinus (t y : ℝ) : ℂ := (point y)^4*((tau (t-y))^2*Q (t-y))
noncomputable def alphaPlus (t y : ℝ) : ℂ := (tau (t+y))^2*Q (t+y)
lemma alphaMinus_ne_zero (t y : ℝ) (h : Q (t-y)≠0) : alphaMinus t y≠0 :=
  mul_ne_zero (pow_ne_zero 4 (point_ne_zero y)) (mul_ne_zero (pow_ne_zero 2 (tau_ne_zero _)) h)
lemma alphaPlus_ne_zero (t y : ℝ) (h : Q (t+y)≠0) : alphaPlus t y≠0 :=
  mul_ne_zero (pow_ne_zero 2 (tau_ne_zero _)) h
lemma rminus_scaled (t y : ℝ) (h : Q (t-y)≠0) :
    alphaMinus t y • spectralR (t-y)=rNumerator root (point t) (point y) := by
  rw [alphaMinus,mul_smul,spectralR_scaled _ h]
  have hh:=r_homogeneous root (point (t-y)) 1 (point y)
  rw [one_mul,←point_add,sub_add_cancel] at hh
  exact hh.symm
lemma rplus_scaled (t y : ℝ) (h : Q (t+y)≠0) :
    alphaPlus t y • spectralR (t+y)=rNumerator root (point t*point y) 1 := by
  simpa only [alphaPlus,point_add] using spectralR_scaled (t+y) h
lemma slot1_smul (c : ℂ) (M : Matrix (Fin 3) (Fin 3) ℂ) : slot1 (c•M)=c•slot1 M := by
  ext p q
  by_cases h : p.2=q.2 <;> simp [slot1,h]
lemma slot2_smul (c : ℂ) (M : Matrix (Fin 3) (Fin 3) ℂ) : slot2 (c•M)=c•slot2 M := by
  ext p q
  by_cases h : p.1=q.1 <;> simp [slot2,h]
lemma scale_four (a b c d : ℂ) (A B C D : Matrix Pair Pair ℂ) :
    (a•A)*(b•B)*(c•C)*(d•D)=(a*b*c*d)•(A*B*C*D) := by
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,mul_assoc]
  congr 1
  ring
lemma scalar_cancel {A B : Matrix Pair Pair ℂ} (c : ℂ) (hc : c≠0) (h : c•A=c•B) : A=B := by
  ext p q
  have hh:=congrFun (congrFun h p) q
  exact mul_left_cancel₀ hc hh

theorem source_reflection_constant (t y : ℝ)
    (hm : Q (t-y)≠0) (hp : Q (t+y)≠0)
    (ht : sine (gamma+t)≠0) (hy : sine (gamma+y)≠0) :
    spectralR (t-y)*slot1 (boundary0 t)*(spectralR (t+y))ᵀ*slot2 (boundary0 y)=
    slot2 (boundary0 y)*spectralR (t+y)*slot1 (boundary0 t)*(spectralR (t-y))ᵀ := by
  have hh:=reflection_constant root (point t) (point y) root_constraint
  unfold reflectionLeft0 reflectionRight0 at hh
  rw [←rminus_scaled t y hm,←rplus_scaled t y hp,
    ←boundary0_scaled t ht,←boundary0_scaled y hy,slot1_smul,slot2_smul] at hh
  simp only [Matrix.transpose_smul,←Matrix.mul_assoc,scale_four] at hh
  have he : beta y*alphaPlus t y*beta t*alphaMinus t y=
      alphaMinus t y*beta t*alphaPlus t y*beta y := by ring
  rw [he] at hh
  exact scalar_cancel _ (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (alphaMinus_ne_zero t y hm) (beta_ne_zero t ht))
    (alphaPlus_ne_zero t y hp)) (beta_ne_zero y hy)) hh

theorem source_reflection_linear (t y : ℝ)
    (hm : Q (t-y)≠0) (hp : Q (t+y)≠0)
    (ht : sine (gamma+t)≠0) (hy : sine (gamma+y)≠0) :
    spectralR (t-y)*slot1 (boundary1 t)*(spectralR (t+y))ᵀ*slot2 (boundary0 y)+
      spectralR (t-y)*slot1 (boundary0 t)*(spectralR (t+y))ᵀ*slot2 (boundary1 y)=
    slot2 (boundary0 y)*spectralR (t+y)*slot1 (boundary1 t)*(spectralR (t-y))ᵀ+
      slot2 (boundary1 y)*spectralR (t+y)*slot1 (boundary0 t)*(spectralR (t-y))ᵀ := by
  have hh:=reflection_linear root (point t) (point y) root_constraint
  unfold reflectionLeft1 reflectionRight1 at hh
  rw [←rminus_scaled t y hm,←rplus_scaled t y hp,
    ←boundary0_scaled t ht,←boundary0_scaled y hy,
    ←boundary1_scaled t ht,←boundary1_scaled y hy] at hh
  simp only [slot1_smul,slot2_smul,Matrix.transpose_smul,←Matrix.mul_assoc,scale_four] at hh
  have he : beta y*alphaPlus t y*beta t*alphaMinus t y=
      alphaMinus t y*beta t*alphaPlus t y*beta y := by ring
  rw [he,←smul_add,←smul_add] at hh
  exact scalar_cancel _ (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (alphaMinus_ne_zero t y hm) (beta_ne_zero t ht))
    (alphaPlus_ne_zero t y hp)) (beta_ne_zero y hy)) hh
end CriticalHoneycomb.Transfer.Reflection

end

section
namespace CriticalHoneycomb.Transfer.Reflection
lemma swap_constant_algebra (r z w : ℂ) (hr : r^16+1=0) (hzw : z*w-r^6=0) :
    (w*(r^3*w^2+r^13))* (((r^6*w^2+r^10*z^2)*(r^4*w^2+r^12*z^2))*(z*(r^3+r^13*z^2)) + ((r^4+r^12)*z*w*(z^2-w^2))*(z*(r^3*z^2+r^13))) = ((r^4*z^2+r^12*w^2)*(r^6*z^2+r^10*w^2))*(z*(r^3*z^2+r^13))*(w*(r^3+r^13*w^2)) := by
  linear_combination (z^7*w^3*r^22 - 1*z^7*w^3*r^10 - 1*z^7*w^3*r^6 + z^7*w*r^32 - 1*z^7*w*r^16 + z^6*w^4*r^2 + z^6*w^2*r^12 + z^6*w^2*r^4 + z^6*w^2 + z^5*w^3*r^28 + z^5*w^3*r^24 - 1*z^5*w^3*r^20 - 2*z^5*w^3*r^8 + z^5*w^3 + z^5*w*r^22 - 1*z^5*w*r^10 - 1*z^5*w*r^6 - 1*z^4*w^6*r^2 + z^4*w^2*r^22 + z^4*w^2*r^14 - 1*z^4*w^2*r^6 - 1*z^3*w^7*r^22 + z^3*w^7*r^10 + z^3*w^7*r^6 - 1*z^3*w^5*r^28 - 1*z^3*w^5*r^24 + z^3*w^5*r^20 + 2*z^3*w^5*r^8 - 1*z^3*w^5 - 1*z^2*w^6*r^12 - 1*z^2*w^6*r^4 - 1*z^2*w^6 - 1*z^2*w^4*r^22 - 1*z^2*w^4*r^14 + z^2*w^4*r^6 - 1*z*w^7*r^32 + z*w^7*r^16 - 1*z*w^5*r^22 + z*w^5*r^10 + z*w^5*r^6)*hr + (z^6*w^2*r^10 + z^6*w^2*r^6 + z^5*w^3*r^10 - 1*z^5*w^3*r^2 - 1*z^5*w*r^4 - 1*z^5*w + z^4*w^2*r^8 - 1*z^4*w^2 - 1*z^3*w^5*r^10 + z^3*w^5*r^2 - 1*z^2*w^6*r^10 - 1*z^2*w^6*r^6 - 1*z^2*w^4*r^8 + z^2*w^4 + z*w^5*r^4 + z*w^5)*hzw
lemma swap_linear_algebra (r z w : ℂ) (hr : r^16+1=0) (hzw : z*w-r^6=0) :
    (w*(r^3*w^2+r^13))*(((r^6*w^2+r^10*z^2)*(z^2-w^2)) + ((r^4+r^12)*z*w*(r^6*w^2+r^10*z^2)))*(z^4-1) = ((r^4*z^2+r^12*w^2)*(r^6*z^2+r^10*w^2))*(z*(r^3*z^2+r^13))*(w^4-1) := by
  linear_combination (z^8*w*r^7 + z^7*w^4*r^9 + z^7*w^4*r + z^7*w^2*r^19 + z^7*w^2*r^11 - 1*z^6*w^3*r^7 - 1*z^6*w*r - 1*z^5*w^6*r + z^5*w^4*r^15 - 1*z^5*w^4*r^3 + z^5*w^2*r + z^5*r^7 - 1*z^4*w*r^7 - 1*z^3*w^8*r^9 - 1*z^3*w^6*r^15 - 1*z^3*w^6*r^11 - 1*z^3*w^4*r - 1*z^3*w^2*r^19 + z^3*w^2*r^15 + z^2*w^5*r + z^2*w^3*r^7 - 1*z*w^8*r^19 + z*w^8*r^3 + z*w^4*r^19 - 1*z*w^4*r^15 - 1*z*w^4*r^7)*hr + (z^7*w^2*r^13 - 1*z^7*r^7 - 1*z^6*w^3*r^13 - 1*z^6*w^3*r^9 - 1*z^6*w^3*r - 1*z^6*w*r^11 - 1*z^5*w^4*r^13 + z^5*w^4*r^9 - 1*z^5*w^2*r^15 + z^5*r + z^4*w^5*r^13 + z^4*w^5*r + z^4*w^3*r^3 - 1*z^4*w*r - 1*z^3*w^6*r^9 + z^3*w^4*r^7 - 1*z^3*w^2*r^13 + z^3*w^2*r^9 + z^2*w^7*r^9 + z^2*w^5*r^11 + z^2*w^3*r^13 + z^2*w^3*r + z*w^6*r^15 + z*w^4*r^13 - 1*z*w^4*r^9 - 1*z*w^4*r - 1*w^7*r^3 - 1*w^5*r^13)*hzw
end CriticalHoneycomb.Transfer.Reflection

end

section
namespace CriticalHoneycomb.Transfer.Reflection.Fusion
open scoped Matrix
noncomputable def twoCos : ℂ := 2*(Real.cos L:ℂ)
noncomputable def sourceKappa : ℂ := twoCos⁻¹
noncomputable def sourceW : Matrix Pair (Fin 3) ℂ := fun p j=>
  match p.1.val,p.2.val,j.val with
  | 0,1,0 => sourceKappa
  | 1,0,0 => sourceKappa
  | 2,1,2 => sourceKappa
  | 1,2,2 => sourceKappa
  | 1,1,1 => 1
  | 0,2,1 => sourceKappa/phase
  | 2,0,1 => sourceKappa*phase
  | _,_,_ => 0
noncomputable def sourceWbar : Matrix Pair (Fin 3) ℂ := fun p j=>
  match p.1.val,p.2.val,j.val with
  | 0,1,0 => sourceKappa
  | 1,0,0 => sourceKappa
  | 2,1,2 => sourceKappa
  | 1,2,2 => sourceKappa
  | 1,1,1 => 1
  | 0,2,1 => sourceKappa*phase
  | 2,0,1 => sourceKappa/phase
  | _,_,_ => 0
lemma point_L : point L=root^2 := by
  convert point_nat_angle 2 using 1 ; unfold L ; congr 1 ; ring
lemma point_neg_L : point (-L)=-root^14 := by
  convert point_neg_angle 2 (by omega) using 1 ; unfold L ; congr 1 ; ring
lemma point_add_L (t : ℝ) : point (t+L)=point t*root^2 := by rw [point_add,point_L]
lemma point_sub_L (t : ℝ) : point (t-L)=-point t*root^14 := by
  rw [sub_eq_add_neg,point_add,point_neg_L];ring
lemma twoCos_polynomial : twoCos=root^2-root^14 := by
  have hh:=Complex.two_cos (L:ℂ)
  rw [←Complex.ofReal_cos] at hh
  simpa only [twoCos,point,Complex.ofReal_neg,neg_mul] using hh.trans
    (show Complex.exp ((L:ℂ)*Complex.I)+Complex.exp (-(L:ℂ)*Complex.I)=root^2-root^14 by
      have hz : point L+point (-L)=root^2-root^14 := by rw [point_L,point_neg_L];ring
      simpa only [point,Complex.ofReal_neg,neg_mul] using hz)
lemma twoCos_ne_zero : twoCos≠0 := by
  have hp : 0<Real.cos L := Real.cos_pos_of_mem_Ioo ⟨by unfold L; linarith [Real.pi_pos],by unfold L; linarith [Real.pi_pos]⟩
  exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (ne_of_gt hp))
lemma kappa_normalization : twoCos*sourceKappa=1 := mul_inv_cancel₀ twoCos_ne_zero
lemma sourceW_scaled : twoCos • sourceW=wNum root := by
  ext ⟨a,b⟩ j
  fin_cases a <;> fin_cases b <;> fin_cases j <;>
    simp [Matrix.smul_apply,smul_eq_mul,sourceW,wNum,div_eq_mul_inv,
      ←mul_assoc,kappa_normalization,phase_inv]
  all_goals simp only [phase_eq,twoCos_polynomial]
lemma sourceWbar_scaled : twoCos • sourceWbar=wBarNum root := by
  ext ⟨a,b⟩ j
  fin_cases a <;> fin_cases b <;> fin_cases j <;>
    simp [Matrix.smul_apply,smul_eq_mul,sourceWbar,wBarNum,div_eq_mul_inv,
      ←mul_assoc,kappa_normalization,phase_inv]
  all_goals simp only [phase_eq,twoCos_polynomial]
lemma star_point (t : ℝ) : star (point t)=point (-t) := by
  simp only [point,Complex.star_def,←Complex.exp_conj,map_mul,
    Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_neg]
  congr 1
  ring
lemma phase_star : star phase=phase⁻¹ := by
  rw [phase_inv]
  unfold phase
  rw [star_point]
  convert point_neg_angle 4 (by omega) using 1 ; congr 1 ; ring
lemma sourceKappa_star : star sourceKappa=sourceKappa := by
  simp only [sourceKappa,twoCos,Complex.star_def,map_inv₀,map_mul,map_ofNat,Complex.conj_ofReal]
lemma sourceWbar_eq_conj (p : Pair) (j : Fin 3) : sourceWbar p j=star (sourceW p j) := by
  rcases p with ⟨a,b⟩
  fin_cases a <;> fin_cases b <;> fin_cases j <;>
    simp [sourceWbar,sourceW,sourceKappa_star,phase_star,div_eq_mul_inv]
lemma bNum_binding (t : ℝ) : bNum root (point t)=beta t := (beta_polynomial t).symm
lemma aNum_binding (t : ℝ) : aNum root (point t)=(tau (2*t))^2*Q (2*t) := by
  rw [Q_scaled,point_twice]
  unfold aNum
  ring
lemma bNum_plus_binding (t : ℝ) : bNum root (point t*root^2)=beta (t+L) := by rw [←point_add_L,bNum_binding]
lemma bNum_minus_binding (t : ℝ) : bNum root (-point t*root^14)=beta (t-L) := by rw [←point_sub_L,bNum_binding]
lemma constant_plus_binding (t : ℝ) (ht : sine (gamma+(t+L))≠0) :
    dConstant root (point t*root^2)=beta (t+L) • boundary0 (t+L) := by
  rw [←point_add_L,←boundary0_scaled _ ht]
lemma constant_minus_binding (t : ℝ) (ht : sine (gamma+(t-L))≠0) :
    dConstant root (-point t*root^14)=beta (t-L) • boundary0 (t-L) := by
  rw [←point_sub_L,←boundary0_scaled _ ht]
lemma linear_plus_binding (t : ℝ) (ht : sine (gamma+(t+L))≠0) :
    dLinear root (point t*root^2)=beta (t+L) • boundary1 (t+L) := by
  rw [←point_add_L,←boundary1_scaled _ ht]
lemma linear_minus_binding (t : ℝ) (ht : sine (gamma+(t-L))≠0) :
    dLinear root (-point t*root^14)=beta (t-L) • boundary1 (t-L) := by
  rw [←point_sub_L,←boundary1_scaled _ ht]
lemma bulk_twice_binding (t : ℝ) (hQ : Q (2*t)≠0) :
    rNumerator root ((point t)^2) 1=((tau (2*t))^2*Q (2*t)) • spectralR (2*t) := by
  rw [←point_twice,←spectralR_scaled _ hQ]
end CriticalHoneycomb.Transfer.Reflection.Fusion

end

section
namespace CriticalHoneycomb.Transfer.Reflection.Fusion
open scoped Matrix BigOperators

lemma sourceKappa_eq_critical : sourceKappa =
    (((2 + Real.sqrt 2) ^ (-(1:ℝ)/2) : ℝ) : ℂ) := by
  unfold sourceKappa twoCos L
  rw [Real.cos_pi_div_eight]
  have hc : (2:ℂ)*((Real.sqrt (2+Real.sqrt 2)/2:ℝ):ℂ)=
      (Real.sqrt (2+Real.sqrt 2):ℂ) := by push_cast;ring
  rw [hc,←Complex.ofReal_inv]
  congr 1
  rw [show -(1:ℝ)/2=-(1/2) by ring,Real.rpow_neg (by positivity),←Real.sqrt_eq_rpow]
noncomputable def fusionProduct (A B : Matrix Pair Pair ℂ) (W : Matrix Pair (Fin 3) ℂ)
    (a b c j k : Fin 3) : ℂ :=
  ∑ u : Fin 3,∑ v : Fin 3,∑ m : Fin 3,A (b,c) (v,m)*B (a,m) (u,k)*W (u,v) j
noncomputable def fusionLift (W : Matrix Pair (Fin 3) ℂ) (A : Matrix Pair Pair ℂ)
    (a b c j k : Fin 3) : ℂ :=
  ∑ f : Fin 3,W (a,b) f*A (f,c) (j,k)
lemma fusionProduct_smul (x y z : ℂ) (A B : Matrix Pair Pair ℂ)
    (W : Matrix Pair (Fin 3) ℂ) (a b c j k : Fin 3) :
    fusionProduct (x•A) (y•B) (z•W) a b c j k=
      (x*y*z)*fusionProduct A B W a b c j k := by
  simp only [fusionProduct,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro u hu
  apply Finset.sum_congr rfl;intro v hv
  apply Finset.sum_congr rfl;intro m hm
  ring
lemma fusionLift_smul (x y : ℂ) (W : Matrix Pair (Fin 3) ℂ)
    (A : Matrix Pair Pair ℂ) (a b c j k : Fin 3) :
    fusionLift (x•W) (y•A) a b c j k=x*y*fusionLift W A a b c j k := by
  simp only [fusionLift,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro u hu
  ring
noncomputable def bulkScale (t : ℝ) : ℂ := (tau t)^2*Q t
lemma bulkScale_ne_zero (t : ℝ) (ht : Q t≠0) : bulkScale t≠0 :=
  mul_ne_zero (pow_ne_zero 2 (tau_ne_zero t)) ht
end CriticalHoneycomb.Transfer.Reflection.Fusion

end

section
namespace CriticalHoneycomb.Transfer.Reflection.Fusion
open scoped Matrix BigOperators
lemma qNumerator_binding (t : ℝ) : qNumerator root (point t)=bulkScale t :=
  (Q_scaled t).symm
lemma plusNumerator_binding (t : ℝ) (ht : Q (t+L)≠0) :
    rNumerator root (point t*root^2) 1=bulkScale (t+L)•spectralR (t+L) := by
  rw [←point_add_L]
  exact (spectralR_scaled _ ht).symm
lemma minusNumerator_binding (t : ℝ) (ht : Q (t-L)≠0) :
    rNumerator root (-point t*root^14) 1=bulkScale (t-L)•spectralR (t-L) := by
  rw [←point_sub_L]
  exact (spectralR_scaled _ ht).symm

theorem source_bulk_fusion (t : ℝ) (hm : Q (t-L)≠0) (ht : Q t≠0) (hp : Q (t+L)≠0)
    (a b c j k : Fin 3) :
    fusionProduct (spectralR (t-L)) (spectralR (t+L)) sourceW a b c j k=
      fusionLift sourceW (spectralR t) a b c j k := by
  have hh:=bulk_fusion_numerator root (point t) root_constraint a b c j k
  change qNumerator root (point t)*fusionProduct
      (rNumerator root (-point t*root^14) 1) (rNumerator root (point t*root^2) 1)
      (wNum root) a b c j k=
    qNumerator root (point t*root^2)*qNumerator root (-point t*root^14)*
      fusionLift (wNum root) (rNumerator root (point t) 1) a b c j k at hh
  rw [qNumerator_binding,minusNumerator_binding t hm,plusNumerator_binding t hp,
    ←sourceW_scaled,←spectralR_scaled t ht,←point_add_L,←point_sub_L,
    qNumerator_binding,qNumerator_binding,fusionProduct_smul,fusionLift_smul] at hh
  have hn : bulkScale t*bulkScale (t-L)*bulkScale (t+L)*twoCos≠0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (bulkScale_ne_zero t ht)
      (bulkScale_ne_zero (t-L) hm)) (bulkScale_ne_zero (t+L) hp)) twoCos_ne_zero
  apply mul_left_cancel₀ hn
  dsimp only [bulkScale] at *
  linear_combination hh
end CriticalHoneycomb.Transfer.Reflection.Fusion

end

section
namespace CriticalHoneycomb.Transfer.Reflection.Fusion
open scoped Matrix
noncomputable def fusionScalar (t : ℝ) : ℂ :=
  beta t*beta (t-L)*((tau (2*t))^2*Q (2*t))*beta (t+L)*twoCos
lemma fusionScalar_ne_zero (t : ℝ) (hQ : Q (2*t)≠0)
    (ht : sine (gamma+t)≠0) (hm : sine (gamma+(t-L))≠0) (hp : sine (gamma+(t+L))≠0) :
    fusionScalar t≠0 := by
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (beta_ne_zero t ht) (beta_ne_zero (t-L) hm))
    (mul_ne_zero (pow_ne_zero 2 (tau_ne_zero _)) hQ))
    (beta_ne_zero (t+L) hp)) twoCos_ne_zero
lemma scalar_cancel_rect {A B : Matrix Pair (Fin 3) ℂ} (c : ℂ) (hc : c≠0)
    (hh : c•A=c•B) : A=B := by
  funext p j
  exact mul_left_cancel₀ hc (congrFun (congrFun hh p) j)

theorem boundary_fusion_constant (t : ℝ) (hQ : Q (2*t)≠0)
    (ht : sine (gamma+t)≠0) (hm : sine (gamma+(t-L))≠0) (hp : sine (gamma+(t+L))≠0) :
    slot2 (boundary0 (t-L))*spectralR (2*t)*slot1 (boundary0 (t+L))*sourceWbar=
      sourceW*boundary0 t := by
  have hh:=source_numerator0 root (point t) root_constraint
  unfold fusionL0 fusionR0 at hh
  rw [bNum_binding,aNum_binding,bNum_plus_binding,bNum_minus_binding,
    constant_minus_binding t hm,constant_plus_binding t hp,bulk_twice_binding t hQ,
    ←sourceWbar_scaled,←sourceW_scaled,←boundary0_scaled t ht] at hh
  simp only [slot1_smul,slot2_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
    ←Matrix.mul_assoc] at hh
  have hscaled : fusionScalar t •
      (slot2 (boundary0 (t-L))*spectralR (2*t)*slot1 (boundary0 (t+L))*sourceWbar)=
      fusionScalar t • (sourceW*boundary0 t) := by
    convert hh using 1 <;> congr 1 <;> unfold fusionScalar <;> ring
  exact scalar_cancel_rect _ (fusionScalar_ne_zero t hQ ht hm hp) hscaled

theorem boundary_fusion_linear (t : ℝ) (hQ : Q (2*t)≠0)
    (ht : sine (gamma+t)≠0) (hm : sine (gamma+(t-L))≠0) (hp : sine (gamma+(t+L))≠0) :
    slot2 (boundary1 (t-L))*spectralR (2*t)*slot1 (boundary0 (t+L))*sourceWbar+
      slot2 (boundary0 (t-L))*spectralR (2*t)*slot1 (boundary1 (t+L))*sourceWbar=
      sourceW*boundary1 t := by
  have hh:=source_numerator1 root (point t) root_constraint
  unfold fusionL1 fusionR1 at hh
  rw [bNum_binding,aNum_binding,bNum_plus_binding,bNum_minus_binding,
    constant_minus_binding t hm,constant_plus_binding t hp,
    linear_minus_binding t hm,linear_plus_binding t hp,bulk_twice_binding t hQ,
    ←sourceWbar_scaled,←sourceW_scaled,←boundary1_scaled t ht] at hh
  simp only [slot1_smul,slot2_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
    ←Matrix.mul_assoc] at hh
  simp only [←smul_add,smul_smul] at hh
  have hscaled : fusionScalar t •
      (slot2 (boundary1 (t-L))*spectralR (2*t)*slot1 (boundary0 (t+L))*sourceWbar+
        slot2 (boundary0 (t-L))*spectralR (2*t)*slot1 (boundary1 (t+L))*sourceWbar)=
      fusionScalar t • (sourceW*boundary1 t) := by
    convert hh using 1 <;> congr 1 <;> try { unfold fusionScalar;ring }
  exact scalar_cancel_rect _ (fusionScalar_ne_zero t hQ ht hm hp) hscaled
end CriticalHoneycomb.Transfer.Reflection.Fusion

end

section
namespace CriticalHoneycomb.Transfer.Reflection.Fusion
open scoped Matrix
noncomputable def mirror {m n : Type*} (f : m ≃ m) (g : n ≃ n)
    (A : Matrix m n ℂ) : Matrix n m ℂ := A.conjTranspose.submatrix g f
lemma mirror_mul {m n p : Type*} [Fintype n] (f : m ≃ m) (g : n ≃ n) (h : p ≃ p)
    (A : Matrix m n ℂ) (B : Matrix n p ℂ) :
    mirror f h (A*B)=mirror g h B*mirror f g A := by
  unfold mirror
  rw [Matrix.conjTranspose_mul]
  exact (Matrix.submatrix_mul_equiv B.conjTranspose A.conjTranspose h g f).symm
lemma mirror_add {m n : Type*} (f : m ≃ m) (g : n ≃ n) (A B : Matrix m n ℂ) :
    mirror f g (A+B)=mirror f g A+mirror f g B := by
  ext i j
  simp [mirror]
def spinFlip : Fin 3 ≃ Fin 3 where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv := Fin.rev_involutive
  right_inv := Fin.rev_involutive
@[simp] lemma spinFlip_apply (a : Fin 3) : spinFlip a = a.rev := rfl
noncomputable def pairFlip : Pair ≃ Pair :=
  (Equiv.prodCongr spinFlip spinFlip).trans (Equiv.prodComm _ _)
lemma sine_star (t : ℝ) : star (sine t)=sine t := by
  simp only [sine,Complex.star_def,Complex.conj_ofReal]
lemma mirror_boundary0 (t : ℝ) : mirror spinFlip spinFlip (boundary0 t)=boundary0 t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mirror,spinFlip_apply,Fin.rev,boundary0,sine_star]
lemma mirror_boundary1 (t : ℝ) : mirror spinFlip spinFlip (boundary1 t)=phase⁻¹ • boundary1 t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mirror,spinFlip_apply,Fin.rev,boundary1,sine_star,phase_star]
  all_goals field_simp [phase,point_ne_zero]
lemma mirror_slot1 (M : Matrix (Fin 3) (Fin 3) ℂ) :
    mirror pairFlip pairFlip (slot1 M)=slot2 (mirror spinFlip spinFlip M) := by
  ext ⟨a,b⟩ ⟨c,d⟩
  by_cases h : a=c <;> simp [mirror,pairFlip,slot1,slot2,h,eq_comm]
lemma mirror_slot2 (M : Matrix (Fin 3) (Fin 3) ℂ) :
    mirror pairFlip pairFlip (slot2 M)=slot1 (mirror spinFlip spinFlip M) := by
  ext ⟨a,b⟩ ⟨c,d⟩
  by_cases h : b=d <;> simp [mirror,pairFlip,slot1,slot2,h,eq_comm]
lemma mirror_W : mirror pairFlip spinFlip sourceW=sourceWbarᵀ := by
  ext j ⟨a,b⟩
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [mirror,pairFlip,spinFlip_apply,Fin.rev,sourceW,sourceWbar,
      sourceKappa_star,phase_star,div_eq_mul_inv]
lemma mirror_Wbar : mirror pairFlip spinFlip sourceWbar=sourceWᵀ := by
  ext j ⟨a,b⟩
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [mirror,pairFlip,spinFlip_apply,Fin.rev,sourceW,sourceWbar,
      sourceKappa_star,phase_star,div_eq_mul_inv]
lemma mirror_bulk_00 (u : ℝ) (c d : Fin 3) :
    mirror pairFlip pairFlip (spectralR u) (0,0) (c,d)=spectralR u (0,0) (c,d) := by
  fin_cases c <;> fin_cases d <;>
    simp [mirror,pairFlip,spinFlip_apply,Fin.rev,spectralR,bulkNumerator,Q,coeffC,sine_star,div_eq_mul_inv]
lemma mirror_bulk_01 (u : ℝ) (c d : Fin 3) :
    mirror pairFlip pairFlip (spectralR u) (0,1) (c,d)=spectralR u (0,1) (c,d) := by
  fin_cases c <;> fin_cases d <;>
    simp [mirror,pairFlip,spinFlip_apply,Fin.rev,spectralR,bulkNumerator,Q,coeffA,coeffV,S,sine_star,div_eq_mul_inv]
lemma mirror_bulk_02 (u : ℝ) (c d : Fin 3) :
    mirror pairFlip pairFlip (spectralR u) (0,2) (c,d)=spectralR u (0,2) (c,d) := by
  fin_cases c <;> fin_cases d <;>
    simp [mirror,pairFlip,spinFlip_apply,Fin.rev,spectralR,bulkNumerator,Q,coeffH,coeffC,coeffD,S,sine_star,phase_star,div_eq_mul_inv]
lemma mirror_bulk_10 (u : ℝ) (c d : Fin 3) :
    mirror pairFlip pairFlip (spectralR u) (1,0) (c,d)=spectralR u (1,0) (c,d) := by
  fin_cases c <;> fin_cases d <;>
    simp [mirror,pairFlip,spinFlip_apply,Fin.rev,spectralR,bulkNumerator,Q,coeffA,coeffV,S,sine_star,div_eq_mul_inv]
lemma mirror_bulk_11 (u : ℝ) (c d : Fin 3) :
    mirror pairFlip pairFlip (spectralR u) (1,1) (c,d)=spectralR u (1,1) (c,d) := by
  fin_cases c <;> fin_cases d <;>
    simp [mirror,pairFlip,spinFlip_apply,Fin.rev,spectralR,bulkNumerator,Q,coeffH,S,sine_star,phase_star,div_eq_mul_inv]
lemma mirror_bulk_12 (u : ℝ) (c d : Fin 3) :
    mirror pairFlip pairFlip (spectralR u) (1,2) (c,d)=spectralR u (1,2) (c,d) := by
  fin_cases c <;> fin_cases d <;>
    simp [mirror,pairFlip,spinFlip_apply,Fin.rev,spectralR,bulkNumerator,Q,coeffA,coeffV,S,sine_star,div_eq_mul_inv]
lemma mirror_bulk_20 (u : ℝ) (c d : Fin 3) :
    mirror pairFlip pairFlip (spectralR u) (2,0) (c,d)=spectralR u (2,0) (c,d) := by
  fin_cases c <;> fin_cases d <;>
    simp [mirror,pairFlip,spinFlip_apply,Fin.rev,spectralR,bulkNumerator,Q,coeffH,coeffC,coeffD,S,sine_star,phase_star,div_eq_mul_inv]
lemma mirror_bulk_21 (u : ℝ) (c d : Fin 3) :
    mirror pairFlip pairFlip (spectralR u) (2,1) (c,d)=spectralR u (2,1) (c,d) := by
  fin_cases c <;> fin_cases d <;>
    simp [mirror,pairFlip,spinFlip_apply,Fin.rev,spectralR,bulkNumerator,Q,coeffA,coeffV,S,sine_star,div_eq_mul_inv]
lemma mirror_bulk_22 (u : ℝ) (c d : Fin 3) :
    mirror pairFlip pairFlip (spectralR u) (2,2) (c,d)=spectralR u (2,2) (c,d) := by
  fin_cases c <;> fin_cases d <;>
    simp [mirror,pairFlip,spinFlip_apply,Fin.rev,spectralR,bulkNumerator,Q,coeffC,sine_star,div_eq_mul_inv]
lemma mirror_bulk (u : ℝ) : mirror pairFlip pairFlip (spectralR u)=spectralR u := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b
  · exact mirror_bulk_00 u c d
  · exact mirror_bulk_01 u c d
  · exact mirror_bulk_02 u c d
  · exact mirror_bulk_10 u c d
  · exact mirror_bulk_11 u c d
  · exact mirror_bulk_12 u c d
  · exact mirror_bulk_20 u c d
  · exact mirror_bulk_21 u c d
  · exact mirror_bulk_22 u c d

theorem boundary_fusion_dual_constant (t : ℝ) (hQ : Q (2*t)≠0)
    (ht : sine (gamma+t)≠0) (hm : sine (gamma+(t-L))≠0) (hp : sine (gamma+(t+L))≠0) :
    sourceWᵀ*slot2 (boundary0 (t+L))*spectralR (2*t)*slot1 (boundary0 (t-L))=
      boundary0 t*sourceWbarᵀ := by
  have hh:=congrArg (mirror pairFlip spinFlip) (boundary_fusion_constant t hQ ht hm hp)
  simpa only [mirror_mul pairFlip pairFlip spinFlip,mirror_mul pairFlip spinFlip spinFlip,mirror_W,mirror_Wbar,mirror_slot1,mirror_slot2,
    mirror_boundary0,mirror_bulk,Matrix.mul_assoc] using hh

theorem boundary_fusion_dual_linear (t : ℝ) (hQ : Q (2*t)≠0)
    (ht : sine (gamma+t)≠0) (hm : sine (gamma+(t-L))≠0) (hp : sine (gamma+(t+L))≠0) :
    sourceWᵀ*slot2 (boundary0 (t+L))*spectralR (2*t)*slot1 (boundary1 (t-L))+
      sourceWᵀ*slot2 (boundary1 (t+L))*spectralR (2*t)*slot1 (boundary0 (t-L))=
      boundary1 t*sourceWbarᵀ := by
  have hh:=congrArg (mirror pairFlip spinFlip) (boundary_fusion_linear t hQ ht hm hp)
  simp only [mirror_add,mirror_mul pairFlip pairFlip spinFlip,mirror_mul pairFlip spinFlip spinFlip,mirror_W,mirror_Wbar,mirror_slot1,mirror_slot2,
    mirror_boundary0,mirror_boundary1,mirror_bulk,Matrix.mul_assoc,
    slot1_smul,slot2_smul,Matrix.smul_mul,Matrix.mul_smul,←smul_add] at hh
  have hn : phase⁻¹≠0 := inv_ne_zero (by exact point_ne_zero _)
  funext j p
  apply mul_left_cancel₀ hn
  simpa only [Matrix.mul_assoc, Matrix.smul_apply, smul_eq_mul] using congrFun (congrFun hh j) p
end CriticalHoneycomb.Transfer.Reflection.Fusion

end

section
namespace CriticalHoneycomb.Transfer.Reflection.Fusion
open scoped Matrix
private lemma hermitianHermitianBulk00 (u : ℝ) (c d : Fin 3) :
    (spectralR u).conjTranspose (0,0) (c,d)=spectralR u (0,0) (c,d) := by
  fin_cases c <;> fin_cases d <;>
    simp [Matrix.conjTranspose_apply,spectralR,bulkNumerator,Q,coeffC,sine_star,div_eq_mul_inv]
private lemma hermitianHermitianBulk01 (u : ℝ) (c d : Fin 3) :
    (spectralR u).conjTranspose (0,1) (c,d)=spectralR u (0,1) (c,d) := by
  fin_cases c <;> fin_cases d <;>
    simp [Matrix.conjTranspose_apply,spectralR,bulkNumerator,Q,coeffA,coeffV,S,sine_star,div_eq_mul_inv]
private lemma hermitianHermitianBulk02 (u : ℝ) (c d : Fin 3) :
    (spectralR u).conjTranspose (0,2) (c,d)=spectralR u (0,2) (c,d) := by
  fin_cases c <;> fin_cases d <;>
    simp [Matrix.conjTranspose_apply,spectralR,bulkNumerator,Q,coeffH,coeffC,coeffD,S,sine_star,phase_star,div_eq_mul_inv]
private lemma hermitianHermitianBulk10 (u : ℝ) (c d : Fin 3) :
    (spectralR u).conjTranspose (1,0) (c,d)=spectralR u (1,0) (c,d) := by
  fin_cases c <;> fin_cases d <;>
    simp [Matrix.conjTranspose_apply,spectralR,bulkNumerator,Q,coeffA,coeffV,S,sine_star,div_eq_mul_inv]
private lemma hermitianHermitianBulk11 (u : ℝ) (c d : Fin 3) :
    (spectralR u).conjTranspose (1,1) (c,d)=spectralR u (1,1) (c,d) := by
  fin_cases c <;> fin_cases d <;>
    simp [Matrix.conjTranspose_apply,spectralR,bulkNumerator,Q,coeffH,S,sine_star,phase_star,div_eq_mul_inv]
private lemma hermitianHermitianBulk12 (u : ℝ) (c d : Fin 3) :
    (spectralR u).conjTranspose (1,2) (c,d)=spectralR u (1,2) (c,d) := by
  fin_cases c <;> fin_cases d <;>
    simp [Matrix.conjTranspose_apply,spectralR,bulkNumerator,Q,coeffA,coeffV,S,sine_star,div_eq_mul_inv]
private lemma hermitianHermitianBulk20 (u : ℝ) (c d : Fin 3) :
    (spectralR u).conjTranspose (2,0) (c,d)=spectralR u (2,0) (c,d) := by
  fin_cases c <;> fin_cases d <;>
    simp [Matrix.conjTranspose_apply,spectralR,bulkNumerator,Q,coeffH,coeffC,coeffD,S,sine_star,phase_star,div_eq_mul_inv]
private lemma hermitianHermitianBulk21 (u : ℝ) (c d : Fin 3) :
    (spectralR u).conjTranspose (2,1) (c,d)=spectralR u (2,1) (c,d) := by
  fin_cases c <;> fin_cases d <;>
    simp [Matrix.conjTranspose_apply,spectralR,bulkNumerator,Q,coeffA,coeffV,S,sine_star,div_eq_mul_inv]
private lemma hermitianHermitianBulk22 (u : ℝ) (c d : Fin 3) :
    (spectralR u).conjTranspose (2,2) (c,d)=spectralR u (2,2) (c,d) := by
  fin_cases c <;> fin_cases d <;>
    simp [Matrix.conjTranspose_apply,spectralR,bulkNumerator,Q,coeffC,sine_star,div_eq_mul_inv]

theorem spectralR_hermitian (u : ℝ) : (spectralR u).conjTranspose=spectralR u := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b
  · exact hermitianHermitianBulk00 u c d
  · exact hermitianHermitianBulk01 u c d
  · exact hermitianHermitianBulk02 u c d
  · exact hermitianHermitianBulk10 u c d
  · exact hermitianHermitianBulk11 u c d
  · exact hermitianHermitianBulk12 u c d
  · exact hermitianHermitianBulk20 u c d
  · exact hermitianHermitianBulk21 u c d
  · exact hermitianHermitianBulk22 u c d
lemma sourceW_conjTranspose : sourceW.conjTranspose=sourceWbarᵀ := by
  ext j p
  exact (sourceWbar_eq_conj p j).symm
end CriticalHoneycomb.Transfer.Reflection.Fusion

end

end OAI
