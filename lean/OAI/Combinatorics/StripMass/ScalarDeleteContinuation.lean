import Mathlib
import OAI.Combinatorics.StripMass.ScalarDegree

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

section Generic
variable {K:Type*} [Field K] {n:ℕ}
abbrev PolynomialField (K:Type*) [Field K] (n:ℕ) := FractionRing (MvPolynomial (Fin n) K)
def genericConst (n:ℕ) : K →+* PolynomialField K n :=
  (algebraMap (MvPolynomial (Fin n) K) (PolynomialField K n)).comp MvPolynomial.C
def genericVar (i:Fin n) : PolynomialField K n :=
  algebraMap (MvPolynomial (Fin n) K) (PolynomialField K n) (MvPolynomial.X i)

lemma genericVar_ne_const (i:Fin n) (z:K) : genericVar i≠genericConst n z := by
  intro h
  have hh:=IsFractionRing.injective (MvPolynomial (Fin n) K) (PolynomialField K n) h
  have he:=congrArg (MvPolynomial.eval (fun _ => z+1)) hh
  simp at he

lemma genericVar_inj (n:ℕ) : Function.Injective (@genericVar K _ n) :=
  (IsFractionRing.injective _ _).comp MvPolynomial.X_injective

lemma discriminant_genericVar_ne (dd:K) (hdd:dd≠0) (i j:Fin n) :
    discriminant (genericConst n dd) (genericVar i) (genericVar j)≠0 := by
  have he:discriminant (genericConst n dd) (genericVar i) (genericVar j)=
      algebraMap (MvPolynomial (Fin n) K) (PolynomialField K n)
        (discriminant (MvPolynomial.C dd) (MvPolynomial.X i) (MvPolynomial.X j)) := by
    simp [genericConst,genericVar,discriminant,map_ofNat]
  rw [he]
  apply (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
  intro h
  have hh:=congrArg (MvPolynomial.eval (fun _ => (0:K))) h
  simp [discriminant,hdd] at hh

lemma discriminant_const_genericVar_ne (dd x:K) (i:Fin n) :
    discriminant (genericConst n dd) (genericConst n x) (genericVar i)≠0 := by
  have he:discriminant (genericConst n dd) (genericConst n x) (genericVar i)=
      algebraMap (MvPolynomial (Fin n) K) (PolynomialField K n)
        (discriminant (MvPolynomial.C dd) (MvPolynomial.C x) (MvPolynomial.X i)) := by
    simp [genericConst,genericVar,discriminant,map_ofNat]
  rw [he]
  apply (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
  intro h
  have hh:=congrArg (fun P:MvPolynomial (Fin n) K =>
      (MvPolynomial.eval₂Hom Polynomial.C (fun _ => Polynomial.X) P).coeff 2) h
  simp only [discriminant,map_sub,map_add,map_mul,map_pow,map_ofNat,
    MvPolynomial.eval₂Hom_C,MvPolynomial.eval₂Hom_X',map_zero] at hh
  have hid:(Polynomial.C x)^2+Polynomial.X^2+2*Polynomial.C dd*Polynomial.C x*Polynomial.X-
      (Polynomial.C dd)^2=(Polynomial.X^2 : Polynomial K)+
        Polynomial.C (2*dd*x)*Polynomial.X+Polynomial.C (x^2-dd^2) := by
    simp only [map_mul,map_pow,map_sub,map_ofNat]; ring
  rw [hid] at hh
  have hc (z:K):((Polynomial.C z)^2).coeff 2=0 := by rw [←map_pow,Polynomial.coeff_C]; norm_num
  simp [hc] at hh

lemma generic_twoCons_inj (x y:K) (hxy:x≠y) :
    Function.Injective (twoCons (genericConst n x) (genericConst n y) (@genericVar K _ n)) := by
  have hc:genericConst n x≠genericConst n y := (genericConst n).injective.ne hxy
  intro i j h
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => rfl
    | succ j =>
      induction j using Fin.cases with
      | zero => exact (hc h).elim
      | succ j => exact (genericVar_ne_const j x h.symm).elim
  | succ i =>
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (hc h.symm).elim
      | succ j =>
        induction j using Fin.cases with
        | zero => rfl
        | succ j => exact (genericVar_ne_const j y h.symm).elim
    | succ i =>
      induction j using Fin.cases with
      | zero => exact (genericVar_ne_const i x h).elim
      | succ j =>
        induction j using Fin.cases with
        | zero => exact (genericVar_ne_const i y h).elim
        | succ j => exact congrArg (fun k:Fin n => k.succ.succ) (genericVar_inj n h)

lemma generic_twoCons_discriminant (dd x y:K) (hdd:dd≠0)
    (i j:Fin (n+2)) (hij:i≠j)
    (hp:¬((i=0 ∧ j=1) ∨ (i=1 ∧ j=0))) :
    discriminant (genericConst n dd)
      (twoCons (genericConst n x) (genericConst n y) genericVar i)
      (twoCons (genericConst n x) (genericConst n y) genericVar j)≠0 := by
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact (hij rfl).elim
    | succ j =>
      induction j using Fin.cases with
      | zero => exact (hp (Or.inl ⟨rfl,by simp⟩)).elim
      | succ j => exact discriminant_const_genericVar_ne dd x j
  | succ i =>
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (hp (Or.inr ⟨by simp,rfl⟩)).elim
      | succ j =>
        induction j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j => exact discriminant_const_genericVar_ne dd y j
    | succ i =>
      induction j using Fin.cases with
      | zero => rw [discriminant_symm]; exact discriminant_const_genericVar_ne dd x i
      | succ j =>
        induction j using Fin.cases with
        | zero => rw [discriminant_symm]; exact discriminant_const_genericVar_ne dd y i
        | succ j => exact discriminant_genericVar_ne dd hdd i j
end Generic

 

theorem scalarPolynomial_delete_continuation {K:Type*} [Field K] [CharZero K]
    (f:ℂ →+* K) (n:ℕ) (dd rr:ℂ) (hdd:dd≠0) (x y γ σ:K) (hxy:x≠y)
    (hxroot:∀z,discriminant (f dd) x z=(z-y)*(z-γ))
    (hyroot:∀z,discriminant (f dd) y z=(z-x)*(z-σ)) (a:Fin n → K) :
    MvPolynomial.eval₂Hom f (twoCons x y a) (scalarPolynomial (n+2) dd rr hdd)=
      (x+y+f rr)*(∏i:Fin n,(a i-γ)*(a i-σ))*
        MvPolynomial.eval₂Hom f a (scalarPolynomial n dd rr hdd) := by
  let g:K →+* PolynomialField K n:=genericConst n
  have rootsMap (v u w:K) (h:∀z,discriminant (f dd) v z=(z-u)*(z-w))
      (z:PolynomialField K n) :
      discriminant (g (f dd)) (g v) z=(z-g u)*(z-g w) := by
    have h0:=h 0
    have h1:=h 1
    have hc:v^2-(f dd)^2=u*w := by simpa [discriminant] using h0
    have hl:2*f dd*v= -(u+w) := by
      simp only [discriminant] at h1
      linear_combination h1-hc
    have hcm:=congrArg g hc
    have hlm:=congrArg g hl
    simp only [map_sub,map_pow,map_mul,map_ofNat,map_neg,map_add] at hcm hlm
    unfold discriminant
    linear_combination hcm+z*hlm
  have hh:=scalarPolynomial_delete_roots (g.comp f) n dd rr hdd
    (g x) (g y) (g γ) (g σ) genericVar
    (generic_twoCons_inj x y hxy) (rootsMap x y γ hxroot) (rootsMap y x σ hyroot)
    (generic_twoCons_discriminant (f dd) x y (by simpa using f.injective.ne hdd))
  have hp:
      MvPolynomial.eval₂Hom (MvPolynomial.C.comp f) (twoCons (MvPolynomial.C x) (MvPolynomial.C y) MvPolynomial.X)
          (scalarPolynomial (n+2) dd rr hdd)=
        (MvPolynomial.C x+MvPolynomial.C y+MvPolynomial.C (f rr)) *
          (∏i:Fin n,(MvPolynomial.X i-MvPolynomial.C γ)*(MvPolynomial.X i-MvPolynomial.C σ))*
          MvPolynomial.eval₂Hom (MvPolynomial.C.comp f) MvPolynomial.X (scalarPolynomial n dd rr hdd) := by
    apply IsFractionRing.injective (MvPolynomial (Fin n) K) (PolynomialField K n)
    simp only [MvPolynomial.map_eval₂Hom,map_mul,map_prod,map_sub,map_add] 
    convert hh using 1
    · apply congrArg (fun v:Fin (n+2) → PolynomialField K n =>
        MvPolynomial.eval₂Hom (g.comp f) v (scalarPolynomial (n+2) dd rr hdd))
      funext i
      induction i using Fin.cases with
      | zero => rfl
      | succ i => induction i using Fin.cases <;> rfl
    · rfl
  have hh':=congrArg (MvPolynomial.eval a) hp
  simp only [MvPolynomial.map_eval₂Hom,map_mul,map_prod,map_sub,map_add,MvPolynomial.eval_X,
    MvPolynomial.eval_C] at hh'
  have hc: (MvPolynomial.eval a).comp (MvPolynomial.C.comp f)=f := by
    ext z; simp
  have hx:(fun i => (MvPolynomial.eval a)
      (twoCons (MvPolynomial.C x) (MvPolynomial.C y) MvPolynomial.X i))=twoCons x y a := by
    funext i
    induction i using Fin.cases with
    | zero => simp [twoCons]
    | succ i => induction i using Fin.cases <;> simp [twoCons]
  simpa only [hc,hx] using hh'


 

 


lemma map_firstScalarHom {K L:Type*} [CommRing K] [CommRing L] (g:K →+* L)
    (f:ℂ →+* K) {n:ℕ} (a:Fin n → K) (P:CosineRing (n+1)) :
    (firstScalarHom f a P).map g=firstScalarHom (g.comp f) (fun i => g (a i)) P := by
  have he:(Polynomial.mapRingHom g).comp (firstScalarHom f a)=
      firstScalarHom (g.comp f) (fun i =>g (a i)) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp only [RingHom.comp_apply,firstScalarHom_C,Polynomial.map_C,Polynomial.coe_mapRingHom]
    · intro z
      simp only [RingHom.comp_apply,firstScalarHom_X,Polynomial.coe_mapRingHom]
      induction z using Fin.cases <;> simp
  exact congrArg (fun h => h P) he

 

theorem scalarPolynomial_first_top_continuation {K:Type*} [CommRing K]
    (f:ℂ →+* K) (n:ℕ) (dd rr:ℂ) (hdd:dd≠0) (a:Fin n → K) :
    (firstScalarHom f a (scalarPolynomial (n+1) dd rr hdd)).coeff n=
      MvPolynomial.eval₂Hom f a (scalarPolynomial n dd rr hdd) := by
  have hi:
      (firstScalarHom MvPolynomial.C (MvPolynomial.X:Fin n → CosineRing n)
        (scalarPolynomial (n+1) dd rr hdd)).coeff n=scalarPolynomial n dd rr hdd := by
    apply IsFractionRing.injective (CosineRing n) (CosineField n)
    rw [←Polynomial.coeff_map,map_firstScalarHom]
    have hh:=scalarPolynomial_first_top (genericConst n) n dd rr hdd genericVar
      (genericVar_inj n) (fun i j _ => discriminant_genericVar_ne dd hdd i j)
    have hv: MvPolynomial.eval₂Hom (genericConst n) genericVar=
        algebraMap (CosineRing n) (CosineField n) := by
      apply MvPolynomial.ringHom_ext
      · intro z; simp [genericConst, RingHom.comp_apply]
      · intro z; simp [genericVar]
    rw [hv] at hh
    exact hh
  have he:=congrArg (MvPolynomial.eval₂Hom f a) hi
  rw [←Polynomial.coeff_map,map_firstScalarHom] at he
  have hc:(MvPolynomial.eval₂Hom f a).comp MvPolynomial.C=f := by ext z; simp
  simp only [hc,MvPolynomial.eval₂Hom_X'] at he
  exact he


 

 


 
def scalarValue {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ} (a:Fin n → K) : K :=
  MvPolynomial.eval₂Hom f a (scalarPolynomial n d rho (by exact_mod_cast d_ne_zero))

lemma scalarValue_permute {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ}
    (a:Fin n → K) (σ:Equiv.Perm (Fin n)) : scalarValue f (a ∘ σ)=scalarValue f a := by
  unfold scalarValue
  have h:=congrArg (MvPolynomial.eval₂Hom f a) (scalarPolynomial_rename (d:ℂ) rho
    (by exact_mod_cast d_ne_zero) σ)
  simpa [MvPolynomial.eval₂Hom_rename] using h

lemma scalarValue_extract {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ}
    (a:Fin (n+1) → K) (i:Fin (n+1)) :
    scalarValue f a=scalarValue f (Fin.cons (a i) (fun j => a (i.succAbove j))) := by
  have h:=scalarValue_permute f a i.cycleRange.symm
  rw [←h]
  congr 1
  funext j
  induction j using Fin.cases <;> simp

lemma scalarValue_swap_head {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ}
    (x y:K) (a:Fin n → K) :
    scalarValue f (Fin.cons x (Fin.cons y a))=scalarValue f (Fin.cons y (Fin.cons x a)) := by
  have h:=scalarValue_extract f (Fin.cons x (Fin.cons y a)) (1:Fin (n+2))
  apply h.trans
  congr 1
  funext j
  induction j using Fin.cases with
  | zero => rfl
  | succ j =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j => simp [Fin.succAbove,Fin.lt_def]

lemma eval_firstScalarHom {K:Type*} [CommRing K] (f:ℂ →+* K)
    {n:ℕ} (a:Fin n → K) (P:CosineRing (n+1)) (z:K) :
    (firstScalarHom f a P).eval z=MvPolynomial.eval₂Hom f (Fin.cons z a) P := by
  have he:(Polynomial.evalRingHom z).comp (firstScalarHom f a)=MvPolynomial.eval₂Hom f (Fin.cons z a) := by
    ext t
    · simp only [RingHom.comp_apply,firstScalarHom_C,Polynomial.coe_evalRingHom,Polynomial.eval_C,MvPolynomial.eval₂Hom_C]
    · simp only [RingHom.comp_apply,firstScalarHom_X,MvPolynomial.eval₂Hom_X',Polynomial.coe_evalRingHom]
      induction t using Fin.cases <;> simp
  exact congrArg (fun h =>h P) he

lemma scalarValue_zero {K:Type*} [CommRing K] (f:ℂ →+* K) (a:Fin 0 → K) : scalarValue f a=1 := by
  have hp:=scalarNumerator_eq_vandermonde 0 (d:ℂ) rho (by exact_mod_cast d_ne_zero)
  have h0:scalarPolynomial 0 d rho (by exact_mod_cast d_ne_zero)=1 := by
    simp [scalarNumerator,sourceVandermonde,clearedPfaffian,clearedPfaffianTerm] at hp
    rw [Finset.prod_eq_one (fun e _ => Fin.elim0 e.val.1)] at hp
    exact hp.symm
  simp [scalarValue,h0]

lemma scalarValue_one {K:Type*} [CommRing K] (f:ℂ →+* K) (x:K) :
    scalarValue f (fun _:Fin 1 =>x)=1 := by
  let a:Fin 0 → K := Fin.elim0
  have h:=Polynomial.eq_C_of_natDegree_le_zero
    (scalarPolynomial_first_degree f 0 d rho (by exact_mod_cast d_ne_zero) a)
  rw [scalarPolynomial_first_top_continuation] at h
  change firstScalarHom f a _=Polynomial.C (scalarValue f a) at h
  rw [scalarValue_zero] at h
  have he:=congrArg (fun P:Polynomial K =>P.eval x) h
  rw [eval_firstScalarHom] at he
  convert he using 1
  · apply congrArg (scalarValue f)
    funext i
    induction i using Fin.cases with
    | zero => rfl
    | succ i => exact Fin.elim0 i
  · simp

lemma scalarValue_two {K:Type*} [CommRing K] (f:ℂ →+* K) (x y:K) :
    scalarValue f (Fin.cons x (fun _:Fin 1 =>y))=x+y+f (rho:ℂ) := by
  let a:Fin 1 → K := fun _ =>y
  let P:=firstScalarHom f a (scalarPolynomial 2 d rho (by exact_mod_cast d_ne_zero))
  have hp:P=Polynomial.X+Polynomial.C (P.coeff 0) := by
    have h:=Polynomial.eq_X_add_C_of_natDegree_le_one
      (scalarPolynomial_first_degree f 1 d rho (by exact_mod_cast d_ne_zero) a)
    rw [scalarPolynomial_first_top_continuation] at h
    change P=Polynomial.C (scalarValue f a)*Polynomial.X+Polynomial.C (P.coeff 0) at h
    rw [scalarValue_one] at h
    simpa using h
  have hf:=source_scalarPolynomial_flat f 1 a
  have hc:P.eval (f (c:ℂ))=y+f (C:ℂ) := by
    change (firstScalarHom f a _).eval _ = _
    rw [eval_firstScalarHom,hf]
    change _ * scalarValue f a=_
    rw [scalarValue_one]
    simp [a]
  rw [hp] at hc
  simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C] at hc
  have hconst:f (c:ℂ)+f (rho:ℂ)=f (C:ℂ) := by
    rw [←map_add]; congr 1; exact_mod_cast c_add_rho_eq_C
  have he:=congrArg (fun Q:Polynomial K =>Q.eval x) hp
  change (firstScalarHom f a _).eval x = _ at he
  rw [eval_firstScalarHom] at he
  change scalarValue f (Fin.cons x a)= _ at he
  rw [he]
  simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
  linear_combination hc-hconst


 

 


lemma scalarValue_cons_extract {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ}
    (z:K) (a:Fin (n+1) → K) (i:Fin (n+1)) :
    scalarValue f (Fin.cons z a)=
      scalarValue f (Fin.cons z (Fin.cons (a i) (fun j =>a (i.succAbove j)))) := by
  have h:=scalarValue_extract f (Fin.cons z a) i.succ
  have hv:(fun j:Fin (n+1) => (Fin.cons z a : Fin (n+2) → K) (i.succ.succAbove j))=
      Fin.cons z (fun j =>a (i.succAbove j)) := by
    funext j
    induction j using Fin.cases <;> simp
  simp only [Fin.cons_succ,hv] at h
  exact h.trans (scalarValue_swap_head f (a i) z _)

lemma scalarValue_one_middle_extract {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ}
    (z x:K) (a:Fin (n+1) → K) (i:Fin (n+1)) :
    scalarValue f (Fin.cons z (Fin.cons x a))=
      scalarValue f (Fin.cons z (Fin.cons (a i) (Fin.cons x (fun j =>a (i.succAbove j))))) := by
  have h:=scalarValue_cons_extract f z (Fin.cons x a) i.succ
  have hv:(fun j:Fin (n+1) => (Fin.cons x a : Fin (n+2) → K) (i.succ.succAbove j))=
      Fin.cons x (fun j =>a (i.succAbove j)) := by
    funext j
    induction j using Fin.cases <;> simp
  simpa only [Fin.cons_succ,hv] using h

lemma scalarValue_two_middle_extract {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ}
    (z x y:K) (a:Fin (n+1) → K) (i:Fin (n+1)) :
    scalarValue f (Fin.cons z (Fin.cons x (Fin.cons y a)))=
      scalarValue f (Fin.cons z (Fin.cons (a i) (Fin.cons x (Fin.cons y (fun j =>a (i.succAbove j)))))) := by
  have h:=scalarValue_cons_extract f z (Fin.cons x (Fin.cons y a)) i.succ.succ
  have hv:(fun j:Fin (n+2) => (Fin.cons x (Fin.cons y a) : Fin (n+3) → K) (i.succ.succ.succAbove j))=
      Fin.cons x (Fin.cons y (fun j =>a (i.succAbove j))) := by
    funext j
    induction j using Fin.cases with
    | zero => simp
    | succ j => induction j using Fin.cases <;> simp
  simpa only [Fin.cons_succ,hv] using h

lemma scalarValue_delete {K:Type*} [Field K] [CharZero K] (f:ℂ →+* K) {n:ℕ}
    (x y γ σ:K) (hxy:x≠y)
    (hx:∀z,discriminant (f (d:ℂ)) x z=(z-y)*(z-γ))
    (hy:∀z,discriminant (f (d:ℂ)) y z=(z-x)*(z-σ)) (a:Fin n → K) :
    scalarValue f (Fin.cons x (Fin.cons y a))=
      (x+y+f (rho:ℂ))*(∏i,(a i-γ)*(a i-σ))*scalarValue f a := by
  exact scalarPolynomial_delete_continuation f n d rho _ x y γ σ hxy hx hy a

lemma scalarValue_flat {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ} (a:Fin n → K) :
    scalarValue f (Fin.cons (f (c:ℂ)) a)=(∏i,(a i+f (C:ℂ)))*scalarValue f a :=
  source_scalarPolynomial_flat f n a


 

 


 
def scalarMergeDiff {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ}
    (x y t:K) (a:Fin n → K) : Polynomial K :=
  firstScalarHom f (Fin.cons x (Fin.cons y a)) (scalarPolynomial (n+3) d rho (by exact_mod_cast d_ne_zero)) -
    Polynomial.C ((x+y+f (rho:ℂ))*(∏i,(a i+t))) *
      ((Polynomial.X+Polynomial.C t)*
        firstScalarHom f (Fin.cons t a) (scalarPolynomial (n+2) d rho (by exact_mod_cast d_ne_zero)))

lemma scalarMergeDiff_eval {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ}
    (x y t:K) (a:Fin n → K) (z:K) :
    (scalarMergeDiff f x y t a).eval z=
      scalarValue f (Fin.cons z (Fin.cons x (Fin.cons y a)))-
        (x+y+f (rho:ℂ))*(∏i,(a i+t))*(z+t)*scalarValue f (Fin.cons z (Fin.cons t a)) := by
  simp only [scalarMergeDiff,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_add,Polynomial.eval_X,eval_firstScalarHom,scalarValue]
  ring

lemma scalarMergeDiff_degree {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ}
    (x y t:K) (a:Fin n → K) : (scalarMergeDiff f x y t a).natDegree≤n+2 := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact scalarPolynomial_first_degree f (n+2) d rho _ _
  · apply (Polynomial.natDegree_C_mul_le _ _).trans
    apply (Polynomial.natDegree_mul_le).trans
    have hp:=scalarPolynomial_first_degree f (n+1) d rho (by exact_mod_cast d_ne_zero) (Fin.cons t a)
    change ((firstScalarHom f (Fin.cons t a)) (scalarPolynomial (n+2) d rho _)).natDegree≤n+1 at hp
    have hl:(Polynomial.X+Polynomial.C t).natDegree≤1:=
      (Polynomial.natDegree_add_le _ _).trans (max_le Polynomial.natDegree_X_le (by simp))
    omega

lemma scalarMergeDiff_top {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ}
    (x y t:K) (a:Fin n → K)
    (h:scalarValue f (Fin.cons x (Fin.cons y a))=
      (x+y+f (rho:ℂ))*(∏i,(a i+t))*scalarValue f (Fin.cons t a)) :
    (scalarMergeDiff f x y t a).coeff (n+2)=0 := by
  unfold scalarMergeDiff
  rw [Polynomial.coeff_sub,Polynomial.coeff_C_mul,add_mul (Polynomial.X) (Polynomial.C t),Polynomial.coeff_add,
    Polynomial.coeff_X_mul,Polynomial.coeff_C_mul]
  rw [scalarPolynomial_first_top_continuation,scalarPolynomial_first_top_continuation]
  have hp:=scalarPolynomial_first_degree f (n+1) d rho (by exact_mod_cast d_ne_zero) (Fin.cons t a)
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp (by omega)),mul_zero,add_zero]
  exact sub_eq_zero.mpr h

lemma scalarMergeDiff_degree_reduced {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ}
    (x y t:K) (a:Fin n → K)
    (h:scalarValue f (Fin.cons x (Fin.cons y a))=
      (x+y+f (rho:ℂ))*(∏i,(a i+t))*scalarValue f (Fin.cons t a)) :
    (scalarMergeDiff f x y t a).natDegree≤n+1 := by
  simpa using Polynomial.natDegree_le_pred (scalarMergeDiff_degree f x y t a)
    (scalarMergeDiff_top f x y t a h)

end
end CriticalStrip.Diagram

end OAI
