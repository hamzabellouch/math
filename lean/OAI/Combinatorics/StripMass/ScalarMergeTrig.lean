import Mathlib
import OAI.Combinatorics.StripMass.ScalarDeleteContinuation

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section

abbrev fcos {n:ℕ} (i:Fin n) (k:ℤ) := shiftedCosine i (phase^k)

lemma fcos_eq {n:ℕ} (i:Fin n) (k:ℤ) : fcos i k=
    torusCos (constF n (phase^k)*variableF i^2) :=
  shiftedCosine_eq _ _ (zpow_ne_zero _ phase_ne_zero)

lemma fcos_shift {n:ℕ} (i:Fin n) (k l:ℤ) :
    fcos i (k+l)=torusCos ((constF n (phase^k)*variableF i^2)*constF n (phase^l)) := by
  rw [fcos_eq,zpow_add₀ phase_ne_zero]
  simp only [constF,map_mul]
  congr 1; ring

lemma fcos_eight {n:ℕ} (i:Fin n) (k:ℤ) : fcos i (k+8)= - fcos i k := by
  rw [fcos_shift]
  simp only [zpow_ofNat,phase_eight,constF,map_neg,map_one,mul_neg,mul_one,torusCos_neg]
  rw [fcos_eq]
  rfl

lemma fcos_sub_eight {n:ℕ} (i:Fin n) (k:ℤ) : fcos i (k-8)= - fcos i k := by
  have h:=fcos_eight i (k-8)
  rw [sub_add_cancel] at h
  linear_combination h

lemma constF_d_sq (n:ℕ) : (constF n d)^2=(1/2:SpectralField n) := by
  have h:=congrArg (fun x:ℝ =>constF n (x:ℂ)) d_sq
  simpa only [Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,
    constF,map_pow,map_div₀,map_one,map_ofNat] using h

lemma fcos_sum_product {n:ℕ} (i:Fin n) (k:ℤ) :
    fcos i (k-2)+fcos i (k+2)=2*constF n d*fcos i k ∧
    fcos i (k-2)*fcos i (k+2)=(fcos i k)^2-(constF n d)^2 := by
  let z:=constF n (phase^k)*variableF i^2
  let w:=constF n phase^2
  have hz:z≠0:=mul_ne_zero (by simpa [constF] using (algebraMap ℂ (SpectralField n)).injective.ne (zpow_ne_zero k phase_ne_zero)) (pow_ne_zero _ (variableF_ne_zero i))
  have hw:w≠0:=pow_ne_zero _ (constF_phase_ne_zero n)
  have he₁:fcos i (k-2)=torusCos (z/w) := by
    rw [fcos_eq,zpow_sub₀ phase_ne_zero]
    simp only [zpow_ofNat,constF,map_div₀,map_pow]
    congr 1; dsimp [z,w,constF]; ring
  have he₂:fcos i (k+2)=torusCos (z*w) := by
    rw [fcos_shift]; simp [z,w,constF]
  have he₀:fcos i k=torusCos z:=shiftedCosine_eq _ _ (zpow_ne_zero _ phase_ne_zero)
  have hew:torusCos w=constF n d:=torusCos_phase_pow n 2
  rw [he₁,he₂,he₀,torusCos_sum z w hz hw,torusCos_product z w hz hw,hew]
  constructor
  · ring
  · linear_combination 2*constF_d_sq n

lemma fcos_six_ne {n:ℕ} (i:Fin n) (k:ℤ) : fcos i k≠fcos i (k+6) := by
  intro h
  have hh:=shiftedCosine_parameter i _ _ h
  rw [zpow_add₀ phase_ne_zero] at hh
  have he:phase^(6:ℤ)=1 := (mul_left_cancel₀ (zpow_ne_zero k phase_ne_zero) (by simpa using hh.symm))
  exact phase_six_ne_one (by simpa using he)

lemma fcos_ne_const {n:ℕ} (i:Fin n) (k:ℤ) (z:ℂ) : fcos i k≠constF n z := by
  intro h
  have he:(2:ℤ) • variableExponent i≠0 := by
    intro h; have hh:=congrFun h i; simp [variableExponent] at hh
  have hl:cosineL ((2:ℤ) • variableExponent i) (phase^k)=constantL n z :=
    IsFractionRing.injective (SpectralRing n) (SpectralField n) h
  change cosineL ((2:ℤ) • variableExponent i) (phase^k)=monomialL 0 z at hl
  have hc:=congrArg (fun P:Laurent n =>P.coeff ((2:ℤ) • variableExponent i)) hl
  simp only [cosineL,monomialL,AddMonoidAlgebra.coeff_add,
    AddMonoidAlgebra.coeff_single,Finsupp.add_apply,Finsupp.single_apply] at hc
  simp only [ite_eq_right (twice_variableExponent_ne_neg i i).symm,
    ite_eq_right he.symm,add_zero] at hc
  exact (zpow_ne_zero k phase_ne_zero) ((div_eq_zero_iff).mp hc |>.resolve_right (by norm_num))

lemma scalar_merge_flat_constants :
    2*(d:ℂ)*(C:ℂ)=(c:ℂ)+(C:ℂ) ∧ (C:ℂ)^2-(d:ℂ)^2=(c:ℂ)*(C:ℂ) := by
  have hd:(d:ℂ)^2=1/2:=by
    have h:=congrArg (fun x:ℝ =>(x:ℂ)) d_sq
    push_cast at h
    exact h
  have hl:=flat_scalar_linear
  have hc:=flat_scalar_constant
  constructor
  · linear_combination (1-2*(d:ℂ))*hl+4*(c:ℂ)*hd
  · linear_combination -((C:ℂ)-(c:ℂ)+2*(d:ℂ)*(c:ℂ))*hl+4*(c:ℂ)^2*hd+hc

lemma fcos_flat_factor {n:ℕ} (i:Fin n) (k:ℤ) :
    (constF n C+fcos i (k-2))*(constF n C+fcos i (k+2))=
      (constF n c+fcos i k)*(constF n C+fcos i k) := by
  obtain ⟨hs,hp⟩:=fcos_sum_product i k
  obtain ⟨hl,hc⟩:=scalar_merge_flat_constants
  have hl':=congrArg (constF n) hl
  have hc':=congrArg (constF n) hc
  simp only [constF,map_mul,map_ofNat,map_add,map_sub,map_pow] at hl' hc'
  dsimp only [constF] at hs hp ⊢
  linear_combination (algebraMap ℂ (SpectralField n)) (C:ℂ)*hs+hp+fcos i k*hl'+hc'

 
lemma scalar_merge_delete_factor_algebra {K:Type*} [Field K] [CharZero K]
    (dd t x y g h:K) (hd:dd^2=1/2)
    (hs:x+y=2*dd*t) (hp:x*y=t^2-dd^2)
    (hg:g^2+h^2+2*dd*g*h-dd^2=0) :
    (x-(-2*dd*g-h))*(x-(-2*dd*h-g))*(y-(-2*dd*g-h))*(y-(-2*dd*h-g))=
      (t+g)*(t+h)*(t-(-2*dd*g-h))*(t-(-2*dd*h-g)) := by
  have he: (x-(-2*dd*g-h))*(x-(-2*dd*h-g))*(y-(-2*dd*g-h))*(y-(-2*dd*h-g))=
      (x*y-(-2*dd*g-h)*(x+y)+(-2*dd*g-h)^2)*
      (x*y-(-2*dd*h-g)*(x+y)+(-2*dd*h-g)^2) := by ring
  rw [he,hs,hp]
  grind

lemma fcos_sixteen {n:ℕ} (i:Fin n) (k:ℤ) : fcos i (k+16)=fcos i k := by
  rw [show k+16=(k+8)+8 by ring,fcos_eight,fcos_eight,neg_neg]

lemma fcos_roots {n:ℕ} (i:Fin n) (k:ℤ) (z:SpectralField n) :
    discriminant (constF n d) (fcos i k) z=(z-fcos i (k-6))*(z-fcos i (k+6)) :=
  shiftedCosine_roots i k z

lemma roots_sum {K:Type*} [Field K] (dd x y z:K)
    (h:∀t,discriminant dd x t=(t-y)*(t-z)) : y+z= -2*dd*x := by
  have h0:=h 0
  have h1:=h 1
  simp only [discriminant] at h0 h1
  linear_combination h1-h0

lemma fcos_delete_factor {n:ℕ} (i j:Fin n) (k l:ℤ) :
    (fcos i (k-2)-fcos j (l-6))*(fcos i (k-2)-fcos j (l+12))*
      (fcos i (k+2)-fcos j (l-6))*(fcos i (k+2)-fcos j (l+12))=
      (fcos i k+fcos j l)*(fcos i k+fcos j (l+6))*
      (fcos i k-fcos j (l-6))*(fcos i k-fcos j (l+12)) := by
  have hs:=roots_sum (constF n d) (fcos j l) (fcos j (l-6)) (fcos j (l+6)) (fcos_roots j l)
  have ht:=roots_sum (constF n d) (fcos j (l+6)) (fcos j l) (fcos j (l+12)) (by
    intro z; simpa only [add_sub_cancel_right, show l+6+6=l+12 by omega] using fcos_roots j (l+6) z)
  have hγ:fcos j (l-6)= -2*constF n d*fcos j l-fcos j (l+6) := by linear_combination hs
  have hσ:fcos j (l+12)= -2*constF n d*fcos j (l+6)-fcos j l := by linear_combination ht
  rw [hγ,hσ]
  have hd:=fcos_roots j l (fcos j (l+6))
  simp only [sub_self,mul_zero,discriminant] at hd
  exact scalar_merge_delete_factor_algebra _ _ _ _ _ _ (constF_d_sq n)
    (fcos_sum_product i k).1 (fcos_sum_product i k).2 hd


 

 

open scoped Classical

lemma scalarValue_fcos_delete {m n:ℕ} (i:Fin m) (k:ℤ) (a:Fin n → SpectralField m) :
    scalarValue (algebraMap ℂ (SpectralField m)) (Fin.cons (fcos i k) (Fin.cons (fcos i (k+6)) a))=
      (fcos i k+fcos i (k+6)+constF m rho)*
        (∏j,(a j-fcos i (k-6))*(a j-fcos i (k+12)))*
        scalarValue (algebraMap ℂ (SpectralField m)) a := by
  apply scalarValue_delete _ _ _ _ _ (fcos_six_ne i k)
  · intro z
    change discriminant (constF m d) (fcos i k) z=_
    rw [fcos_roots,mul_comm]
  · intro z; simpa only [constF,add_sub_cancel_right,show k+6+6=k+12 by omega] using fcos_roots i (k+6) z

lemma scalarMergeDiff_eval_neg {m n:ℕ} (i:Fin m) (k:ℤ) (a:Fin n → SpectralField m) :
    (scalarMergeDiff (algebraMap ℂ (SpectralField m)) (fcos i (k-2)) (fcos i (k+2)) (fcos i k) a).eval (-fcos i k)=0 := by
  rw [scalarMergeDiff_eval,neg_add_cancel,mul_zero,zero_mul,sub_zero]
  rw [←fcos_sub_eight]
  have hh:=scalarValue_fcos_delete i (k-8) (Fin.cons (fcos i (k+2)) a)
  have hp:fcos i (k-8-6)=fcos i (k+2) := by
    rw [←fcos_sixteen i (k-8-6)]
    congr 1; omega
  simp only [show k-8+6=k-2 by omega,hp,Fin.prod_univ_succ,Fin.cons_zero,
    Fin.cons_succ,sub_self,zero_mul,mul_zero] at hh
  exact hh

lemma scalarMergeDiff_eval_flat {m n:ℕ} (i:Fin m) (k:ℤ) (a:Fin n → SpectralField m)
    (h:scalarValue (algebraMap ℂ (SpectralField m)) (Fin.cons (fcos i (k-2)) (Fin.cons (fcos i (k+2)) a))=
      (fcos i (k-2)+fcos i (k+2)+constF m rho)*(∏j,(a j+fcos i k))*
        scalarValue (algebraMap ℂ (SpectralField m)) (Fin.cons (fcos i k) a)) :
    (scalarMergeDiff (algebraMap ℂ (SpectralField m)) (fcos i (k-2)) (fcos i (k+2)) (fcos i k) a).eval (constF m c)=0 := by
  rw [scalarMergeDiff_eval]
  simp only [constF] at h ⊢
  rw [scalarValue_flat,scalarValue_flat,h]
  simp only [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  have he:=fcos_flat_factor i k
  change (constF m C+fcos i (k-2))*(constF m C+fcos i (k+2))=_ at he
  have hring:
      (fcos i (k-2) + (algebraMap ℂ (SpectralField m)) (C:ℂ)) *
        ((fcos i (k+2) + (algebraMap ℂ (SpectralField m)) (C:ℂ)) * (∏j,(a j+(algebraMap ℂ (SpectralField m)) (C:ℂ))))=
      (constF m c+fcos i k)*(fcos i k+constF m C)*(∏j,(a j+constF m C)) := by
    calc
      _ = ((constF m C+fcos i (k-2))*(constF m C+fcos i (k+2)))*(∏j,(a j+constF m C)) := by dsimp only [constF]; ring
      _ = _ := by rw [he]; ring
  rw [hring]
  dsimp only [constF]
  ring

lemma scalarMergeDiff_eval_deletion {m n:ℕ} (i:Fin m) (k:ℤ)
    (a:Fin (n+1) → SpectralField m) (j:Fin (n+1)) (g:Fin m) (l:ℤ)
    (ha:a j=fcos g l)
    (h:scalarValue (algebraMap ℂ (SpectralField m))
        (Fin.cons (fcos i (k-2)) (Fin.cons (fcos i (k+2)) (fun v =>a (j.succAbove v))))=
      (fcos i (k-2)+fcos i (k+2)+constF m rho)*(∏v,(a (j.succAbove v)+fcos i k))*
        scalarValue (algebraMap ℂ (SpectralField m)) (Fin.cons (fcos i k) (fun v =>a (j.succAbove v)))) :
    (scalarMergeDiff (algebraMap ℂ (SpectralField m)) (fcos i (k-2)) (fcos i (k+2)) (fcos i k) a).eval (fcos g (l+6))=0 := by
  rw [scalarMergeDiff_eval,scalarValue_two_middle_extract _ _ _ _ a j,
    scalarValue_one_middle_extract _ _ _ a j,ha,
    scalarValue_swap_head _ (fcos g (l+6)) (fcos g l),
    scalarValue_swap_head _ (fcos g (l+6)) (fcos g l),
    scalarValue_fcos_delete,scalarValue_fcos_delete,h]
  rw [Fin.prod_univ_succAbove (fun v =>a v+fcos i k) j,ha]
  simp only [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  have he:=fcos_delete_factor i g k l
  
  have hp:
      (fcos i (k-2)-fcos g (l-6))*(fcos i (k-2)-fcos g (l+12))*
        ((fcos i (k+2)-fcos g (l-6))*(fcos i (k+2)-fcos g (l+12))*
        (∏v,(a (j.succAbove v)-fcos g (l-6))*(a (j.succAbove v)-fcos g (l+12))))=
      ((fcos i k+fcos g l)*(fcos i k+fcos g (l+6))*
        (fcos i k-fcos g (l-6))*(fcos i k-fcos g (l+12)))*
        (∏v,(a (j.succAbove v)-fcos g (l-6))*(a (j.succAbove v)-fcos g (l+12))) := by
    rw [←he]; ring
  rw [hp]
  dsimp only [constF]
  ring

end

 

 

noncomputable section

lemma fcos_tuple_injective {m n:ℕ} (j:Fin n → Fin m) (hj:Function.Injective j) (l:Fin n → ℤ) :
    Function.Injective (fun v => fcos (j v) (l v)) := by
  intro v w h
  by_contra hvw
  exact shiftedCosine_ne (j v) (j w) (hj.ne hvw) _ _ (zpow_ne_zero _ phase_ne_zero) h

lemma scalarMerge_nodes_injective {m n:ℕ} (i:Fin m) (k:ℤ)
    (j:Fin n → Fin m) (hj:Function.Injective j) (hi:∀v,j v≠i) (l:Fin n → ℤ) :
    Function.Injective (Fin.cons (constF m c) (Fin.cons (fcos i (k+8)) (fun v =>fcos (j v) (l v+6)))) := by
  apply Fin.cons_injective_of_injective
  · rintro ⟨v,hv⟩
    induction v using Fin.cases with
    | zero => exact fcos_ne_const i (k+8) c hv
    | succ v => exact fcos_ne_const (j v) (l v+6) c hv
  · apply Fin.cons_injective_of_injective
    · rintro ⟨v,hv⟩
      exact shiftedCosine_ne (j v) i (hi v) _ _ (zpow_ne_zero _ phase_ne_zero) hv
    · exact fcos_tuple_injective j hj (fun v =>l v+6)


 

 

open scoped Classical

lemma scalarValue_rotate3 {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ}
    (x y z:K) (a:Fin n → K) :
    scalarValue f (Fin.cons x (Fin.cons y (Fin.cons z a)))=
      scalarValue f (Fin.cons z (Fin.cons x (Fin.cons y a))) := by
  rw [scalarValue_cons_extract f x (Fin.cons y (Fin.cons z a)) (1:Fin (n+2))]
  have hv:(fun j:Fin (n+1) =>(Fin.cons y (Fin.cons z a):Fin (n+2) → K) ((1:Fin (n+2)).succAbove j))=Fin.cons y a := by
    funext j
    induction j using Fin.cases with
    | zero => rfl
    | succ j => simp [Fin.succAbove,Fin.lt_def]
  rw [hv]
  simpa only [show (1:Fin (n+2))=(0:Fin (n+1)).succ from rfl,Fin.cons_succ,Fin.cons_zero] using scalarValue_swap_head f x z (Fin.cons y a)

 
lemma scalarValue_fcos_merge {m r:ℕ} (i:Fin m) (k:ℤ)
    (s:Fin r → Fin m) (hs:Function.Injective s) (hi:∀j,s j≠i) (l:Fin r → ℤ) :
    scalarValue (algebraMap ℂ (SpectralField m))
      (Fin.cons (fcos i (k-2)) (Fin.cons (fcos i (k+2)) (fun j =>fcos (s j) (l j))))=
      (fcos i (k-2)+fcos i (k+2)+constF m rho)*
        (∏j,(fcos (s j) (l j)+fcos i k))*
          scalarValue (algebraMap ℂ (SpectralField m)) (Fin.cons (fcos i k) (fun j =>fcos (s j) (l j))) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero =>
      have he:(Fin.cons (fcos i (k+2)) (fun j:Fin 0 =>fcos (s j) (l j)):Fin 1 → SpectralField m)=fun _ =>fcos i (k+2) := by ext j; fin_cases j; rfl
      have ht:(Fin.cons (fcos i k) (fun j:Fin 0 =>fcos (s j) (l j)):Fin 1 → SpectralField m)=fun _ =>fcos i k := by ext j; fin_cases j; rfl
      rw [he,ht,scalarValue_two,scalarValue_one]
      simp [constF]
    | succ n =>
      let a:Fin n → SpectralField m:=fun j =>fcos (s j.succ) (l j.succ)
      have htail:=ih n (by omega) (fun j =>s j.succ) (hs.comp (Fin.succ_injective _)) (fun j =>hi j.succ) (fun j =>l j.succ)
      change scalarValue _ (Fin.cons (fcos i (k-2)) (Fin.cons (fcos i (k+2)) a))=_ at htail
      let P:=scalarMergeDiff (algebraMap ℂ (SpectralField m)) (fcos i (k-2)) (fcos i (k+2)) (fcos i k) a
      have hd:P.natDegree≤n+1:=scalarMergeDiff_degree_reduced _ _ _ _ a htail
      let roots:Fin (n+2) → SpectralField m:=Fin.cons (constF m c) (Fin.cons (fcos i (k+8)) (fun j =>fcos (s j.succ) (l j.succ+6)))
      have hinj:Function.Injective roots:=scalarMerge_nodes_injective i k _ (hs.comp (Fin.succ_injective _)) (fun j =>hi j.succ) _
      have hr:∀j,P.eval (roots j)=0 := by
        intro j
        induction j using Fin.cases with
        | zero => exact scalarMergeDiff_eval_flat i k a htail
        | succ j =>
          induction j using Fin.cases with
          | zero => simpa only [roots,Fin.cons_succ,Fin.cons_zero,fcos_eight] using scalarMergeDiff_eval_neg i k a
          | succ j =>
            cases n with
            | zero => exact Fin.elim0 j
            | succ v =>
              have hdel:=ih v (by omega) (fun t =>s (j.succAbove t).succ)
                (hs.comp ((Fin.succ_injective _).comp (Fin.succAbove_right_injective)))
                (fun t =>hi (j.succAbove t).succ) (fun t =>l (j.succAbove t).succ)
              exact scalarMergeDiff_eval_deletion i k a j (s j.succ) (l j.succ) rfl hdel
      have hp:P=0:=Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hinj hr (by simp only [Fintype.card_fin]; omega)
      have he:=congrArg (fun Q:Polynomial (SpectralField m) =>Q.eval (fcos (s 0) (l 0))) hp
      simp only [Polynomial.eval_zero] at he
      rw [scalarMergeDiff_eval] at he
      have ha:(fun j =>fcos (s j) (l j))=Fin.cons (fcos (s 0) (l 0)) a:= by ext j; induction j using Fin.cases <;> rfl
      rw [ha,scalarValue_rotate3,scalarValue_swap_head _ (fcos i k) (fcos (s 0) (l 0))]
      simp only [Fin.prod_univ_succ]
      dsimp only [constF] at *
      linear_combination he

end

 

 

noncomputable section
open scoped Classical

lemma rationalAt_scalarValue {m n r:ℕ} (φ:Laurent m →ₐ[ℂ] SpectralField n)
    (a:Fin r → SpectralField m) (b:Fin r → SpectralField n)
    (ha:∀j,RationalAt φ.toRingHom (a j) (b j)) :
    RationalAt φ.toRingHom (scalarValue (algebraMap ℂ (SpectralField m)) a)
      (scalarValue (algebraMap ℂ (SpectralField n)) b) :=
  RationalAt.mv_eval _ _ a b (rationalAt_const φ) ha _

lemma rationalAt_copy_fcos {m n:ℕ} (v:Fin m → Fin n) (i:Fin m) (k:ℤ) :
    RationalAt (copyEvaluation v).toRingHom (fcos i k) (fcos (v i) k) := by
  rw [fcos_eq,fcos_eq]
  apply rationalAt_torusCos
  · exact (rationalAt_const (copyEvaluation v) (phase^k)).mul ((rationalAt_copy_variable v i).pow 2)
  · exact mul_ne_zero (by simpa [constF] using (algebraMap ℂ (SpectralField n)).injective.ne (zpow_ne_zero k phase_ne_zero)) (pow_ne_zero _ (variableF_ne_zero _))

 

theorem scalarValue_fcos_merge_all {m r:ℕ} (i:Fin m) (k:ℤ)
    (s:Fin r → Fin m) (l:Fin r → ℤ) :
    scalarValue (algebraMap ℂ (SpectralField m))
      (Fin.cons (fcos i (k-2)) (Fin.cons (fcos i (k+2)) (fun j =>fcos (s j) (l j))))=
      (fcos i (k-2)+fcos i (k+2)+constF m rho)*
        (∏j,(fcos (s j) (l j)+fcos i k))*
          scalarValue (algebraMap ℂ (SpectralField m)) (Fin.cons (fcos i k) (fun j =>fcos (s j) (l j))) := by
  let v:Fin (r+1) → Fin m:=Fin.cons i s
  let φ:=copyEvaluation v
  have h:=scalarValue_fcos_merge (0:Fin (r+1)) k Fin.succ (Fin.succ_injective _) (fun j =>Fin.succ_ne_zero j) l
  have ht:RationalAt φ.toRingHom
      (scalarValue (algebraMap ℂ (SpectralField (r+1))) (Fin.cons (fcos 0 (k-2)) (Fin.cons (fcos 0 (k+2)) (fun j =>fcos j.succ (l j)))))
      (scalarValue (algebraMap ℂ (SpectralField m)) (Fin.cons (fcos i (k-2)) (Fin.cons (fcos i (k+2)) (fun j =>fcos (s j) (l j))))) := by
    apply rationalAt_scalarValue
    intro j
    induction j using Fin.cases with
    | zero => exact rationalAt_copy_fcos v 0 (k-2)
    | succ j => induction j using Fin.cases with
      | zero => exact rationalAt_copy_fcos v 0 (k+2)
      | succ j => exact rationalAt_copy_fcos v j.succ (l j)
  have hv:RationalAt φ.toRingHom
      (scalarValue (algebraMap ℂ (SpectralField (r+1))) (Fin.cons (fcos 0 k) (fun j =>fcos j.succ (l j))))
      (scalarValue (algebraMap ℂ (SpectralField m)) (Fin.cons (fcos i k) (fun j =>fcos (s j) (l j)))) := by
    apply rationalAt_scalarValue
    intro j
    induction j using Fin.cases with
    | zero => exact rationalAt_copy_fcos v 0 k
    | succ j => exact rationalAt_copy_fcos v j.succ (l j)
  have hp:=RationalAt.prod Finset.univ
    (fun j:Fin r =>fcos j.succ (l j)+fcos (0:Fin (r+1)) k)
    (fun j:Fin r =>fcos (s j) (l j)+fcos i k)
    (fun j _ => (rationalAt_copy_fcos v j.succ (l j)).add (rationalAt_copy_fcos v 0 k))
  have hq:=((rationalAt_copy_fcos v 0 (k-2)).add (rationalAt_copy_fcos v 0 (k+2))).add (rationalAt_const φ rho)
  rw [h] at ht
  exact ht.unique ((hq.mul hp).mul hv)


 

 


lemma torusEvaluation_lift {n m:ℕ} (z:Fin n → SpectralField m) (hz:∀i,z i≠0)
    (y:SpectralField m) (hy:y≠0) (P:Laurent n) :
    torusEvaluation (Fin.snoc z y) (fun i =>Fin.lastCases (by simpa using hy) (fun j =>by simpa using hz j) i)
      (liftLaurent P)=torusEvaluation z hz P := by
  have he:(torusEvaluation (Fin.snoc z y) (fun i =>Fin.lastCases (by simpa using hy) (fun j =>by simpa using hz j) i)).toRingHom.comp (liftLaurentHom n)=
      (torusEvaluation z hz).toRingHom := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change torusEvaluation _ _ (liftLaurent (monomialL _ _))=torusEvaluation _ _ (monomialL _ _)
    all_goals rw [liftLaurent_monomial]
    all_goals simp only [torusEvaluation_monomial,Fin.prod_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last,zpow_zero,mul_one]
  exact DFunLike.congr_fun he P

lemma torusEvaluation_lastCosine {n m:ℕ} (z:Fin (n+1) → SpectralField m) (hz:∀i,z i≠0) :
    torusEvaluation z hz (lastCosine n)=torusCos (z (Fin.last n)^2/constF m phase^3) := by
  have h:=RationalAt.algebraMap (φ:=(torusEvaluation z hz).toRingHom) (F:=SpectralField (n+1)) (lastCosine n)
  change RationalAt _ (evalLaurent (lastCosine n)) _ at h
  rw [lastCosine_map] at h
  apply h.unique
  exact rationalAt_torusCos _ (((rationalAt_variable z hz (Fin.last n)).pow 2).div
    ((rationalAt_const _ phase).pow 3) (pow_ne_zero _ (constF_phase_ne_zero m)))
    (div_ne_zero (pow_ne_zero _ (hz _)) (pow_ne_zero _ (constF_phase_ne_zero m)))

lemma torusEvaluation_lastSine {n m:ℕ} (z:Fin (n+1) → SpectralField m) (hz:∀i,z i≠0) :
    torusEvaluation z hz (lastSine n)=torusSin (z (Fin.last n)) := by
  have h:=RationalAt.algebraMap (φ:=(torusEvaluation z hz).toRingHom) (F:=SpectralField (n+1)) (lastSine n)
  change RationalAt _ (evalLaurent (lastSine n)) _ at h
  rw [evalLaurent_lastSine] at h
  exact h.unique (rationalAt_torusSin _ (rationalAt_variable z hz (Fin.last n)) (hz _))

lemma torusEvaluation_lastLaurent {n m:ℕ} (z:Fin n → SpectralField m) (hz:∀i,z i≠0)
    (y:SpectralField m) (hy:y≠0) (p:Pairing (n+1)) (P:Polynomial (Laurent n)) :
    torusEvaluation (Fin.snoc z y) (fun i =>Fin.lastCases (by simpa using hy) (fun j =>by simpa using hz j) i)
      (lastLaurent p P)=
      (if p.Occupied (Fin.last n) then torusSin y else 1)*
        (P.map (torusEvaluation z hz).toRingHom).eval (torusCos (y^2/constF m phase^3)) := by
  unfold lastLaurent
  rw [map_mul]
  change _ * (torusEvaluation (Fin.snoc z y) (fun i =>Fin.lastCases (by simpa using hy) (fun j =>by simpa using hz j) i)).toRingHom (P.eval₂ _ _) = _
  rw [Polynomial.hom_eval₂]
  have he:(torusEvaluation (Fin.snoc z y) (fun i =>Fin.lastCases (by simpa using hy) (fun j =>by simpa using hz j) i)).toRingHom.comp (liftLaurentHom n)=(torusEvaluation z hz).toRingHom :=
    RingHom.ext (torusEvaluation_lift z hz y hy)
  change _ * P.eval₂ _ _=_
  rw [he]
  change _ * P.eval₂ _ (torusEvaluation _ _ (lastCosine n))=_
  rw [torusEvaluation_lastCosine]
  simp only [Fin.snoc_last,Polynomial.eval_map]
  congr 1
  split_ifs
  · simpa only [Fin.snoc_last] using torusEvaluation_lastSine (Fin.snoc z y) (fun i =>Fin.lastCases (by simpa using hy) (fun j =>by simpa using hz j) i)
  · exact map_one _

 

lemma lastLaurent_regular_value {n m:ℕ} (P:Pairing (n+1) → Polynomial (Laurent n))
    (hP:∀p,evalLaurent (lastLaurent p (P p))=rationalVacuum (n+1) p)
    (z:Fin n → SpectralField m) (hz:∀i,z i≠0) (y:SpectralField m) (hy:y≠0)
    (hL:∀i,torusL (constF m phase^3/(Fin.snoc z y : Fin (n+1) → SpectralField m) i)≠0)
    (hreg:VacuumRegular (fun i =>torusWeights (constF m phase^3/(Fin.snoc z y : Fin (n+1) → SpectralField m) i)))
    (p:Pairing (n+1)) :
    (if p.Occupied (Fin.last n) then torusSin y else 1)*
      ((P p).map (torusEvaluation z hz).toRingHom).eval (torusCos (y^2/constF m phase^3))=
      scalarValue (algebraMap ℂ (SpectralField m)) (fun i =>torusCos (((Fin.snoc z y : Fin (n+1) → SpectralField m) i)^2/constF m phase^3))*
        normalizedVacuum (fun i =>torusWeights (constF m phase^3/(Fin.snoc z y : Fin (n+1) → SpectralField m) i)) p := by
  let x:Fin (n+1) → SpectralField m:=Fin.snoc z y
  have hx:∀i:Fin (n+1),x i≠0:=fun i =>Fin.lastCases (by simpa [x] using hy) (fun j =>by simpa [x] using hz j) i
  let φ:=torusEvaluation x hx
  have hv:=RationalAt.algebraMap (φ:=φ.toRingHom) (F:=SpectralField (n+1)) (lastLaurent p (P p))
  change RationalAt _ (evalLaurent (lastLaurent p (P p))) _ at hv
  rw [hP p] at hv
  have hs:RationalAt φ.toRingHom (spectralNormalization (n+1))
      (scalarValue (algebraMap ℂ (SpectralField m)) (fun i =>torusCos ((x i)^2/constF m phase^3))) := by
    rw [←scalarPolynomial_eval_spectral]
    apply rationalAt_scalarValue
    intro i
    exact rationalAt_torusCos φ (((rationalAt_variable x hx i).pow 2).div
      ((rationalAt_const φ phase).pow 3) (pow_ne_zero _ (constF_phase_ne_zero m)))
      (div_ne_zero (pow_ne_zero _ (hx i)) (pow_ne_zero _ (constF_phase_ne_zero m)))
  have hw (i:Fin (n+1)) (t:Tile):RationalAt φ.toRingHom ((spectralWeights (n+1) i).tile t)
      ((torusWeights (constF m phase^3/x i)).tile t) := by
    apply rationalAt_torusWeights
    · exact ((rationalAt_const φ phase).pow 3).div (rationalAt_variable x hx i) (hx i)
    · exact div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero m)) (hx i)
    · exact hL i
  have hn:=rationalAt_normalizedVacuum _ _ hw hreg p
  have he:=hv.unique (hs.mul hn)
  dsimp only [φ,x] at he
  change torusEvaluation _ _ (lastLaurent p (P p))=_ at he
  rw [torusEvaluation_lastLaurent z hz y hy] at he
  exact he


 

 


lemma rationalAt_torusVacuum {n m:ℕ} (z:Fin n → SpectralField m) (hz:∀i,z i≠0)
    (hL:∀i,torusL (constF m phase^3/z i)≠0)
    (hreg:VacuumRegular (fun i =>torusWeights (constF m phase^3/z i)))
    (p:Pairing n) :
    RationalAt (torusEvaluation z hz).toRingHom (rationalVacuum n p)
      (scalarValue (algebraMap ℂ (SpectralField m)) (fun i =>torusCos ((z i)^2/constF m phase^3))*
        normalizedVacuum (fun i =>torusWeights (constF m phase^3/z i)) p) := by
  let φ:=torusEvaluation z hz
  have hs:RationalAt φ.toRingHom (spectralNormalization n)
      (scalarValue (algebraMap ℂ (SpectralField m)) (fun i =>torusCos ((z i)^2/constF m phase^3))) := by
    rw [←scalarPolynomial_eval_spectral]
    apply rationalAt_scalarValue
    intro i
    exact rationalAt_torusCos φ (((rationalAt_variable z hz i).pow 2).div
      ((rationalAt_const φ phase).pow 3) (pow_ne_zero _ (constF_phase_ne_zero m)))
      (div_ne_zero (pow_ne_zero _ (hz i)) (pow_ne_zero _ (constF_phase_ne_zero m)))
  have hw (i:Fin n) (t:Tile):RationalAt φ.toRingHom ((spectralWeights n i).tile t)
      ((torusWeights (constF m phase^3/z i)).tile t) := by
    apply rationalAt_torusWeights
    · exact ((rationalAt_const φ phase).pow 3).div (rationalAt_variable z hz i) (hz i)
    · exact div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero m)) (hz i)
    · exact hL i
  exact hs.mul (rationalAt_normalizedVacuum _ _ hw hreg p)

lemma torusEvaluation_vacuum {n m:ℕ} (W:Pairing n → Laurent n)
    (hW:∀p,evalLaurent (W p)=rationalVacuum n p)
    (z:Fin n → SpectralField m) (hz:∀i,z i≠0)
    (hL:∀i,torusL (constF m phase^3/z i)≠0)
    (hreg:VacuumRegular (fun i =>torusWeights (constF m phase^3/z i)))
    (p:Pairing n) :
    torusEvaluation z hz (W p)=
      scalarValue (algebraMap ℂ (SpectralField m)) (fun i =>torusCos ((z i)^2/constF m phase^3))*
        normalizedVacuum (fun i =>torusWeights (constF m phase^3/z i)) p := by
  have h:=RationalAt.algebraMap (φ:=(torusEvaluation z hz).toRingHom) (F:=SpectralField n) (W p)
  change RationalAt _ (evalLaurent (W p)) _ at h
  rw [hW] at h
  exact h.unique (rationalAt_torusVacuum z hz hL hreg p)

end
end CriticalStrip.Diagram

end OAI
