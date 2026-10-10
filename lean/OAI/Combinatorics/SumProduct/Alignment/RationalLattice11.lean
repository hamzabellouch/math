import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalTriangular01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
noncomputable section
open scoped BigOperators
end
 
end

section
 

 

noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
namespace RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
variable (c : RealCoordinates G n)

lemma natpow_prefix_eq (g h : G) (i : Fin n)
    (he : ∀ j : Fin n,j < i → c.coord g j=c.coord h j) (m : ℕ) :
    ∀ j : Fin n,j < i → c.coord (g^m) j=c.coord (h^m) j := by
  induction m with
  | zero => intro j hj; simp
  | succ m ih =>
    intro j hj
    rw [pow_succ,pow_succ,c.mul_coord,c.mul_coord,ih j hj,he j hj]
    congr 1
    apply congrArg (fun a=>MvPolynomial.eval₂ (algebraMap ℚ ℝ) a (c.correction j))
    funext a
    cases a with
    | inl k => exact ih _ (lt_trans k.isLt hj)
    | inr k => exact he _ (lt_trans k.isLt hj)

lemma powerPolynomial_sub_of_prefix_eq (g h : G) (i : Fin n)
    (he : ∀ j : Fin n,j < i → c.coord g j=c.coord h j) :
    powerPolynomial c g i-powerPolynomial c h i=X*C (c.coord g i-c.coord h i) := by
  apply Polynomial.eq_of_eval_nat_eq
  intro m
  simp only [eval_sub,powerPolynomial_nat,eval_mul,eval_X,eval_C]
  induction m with
  | zero => simp [c.one_coord]
  | succ m ih =>
    rw [pow_succ,pow_succ,c.mul_coord,c.mul_coord]
    have hh : (Sum.elim (fun j : Fin i.val=>c.coord (g^m) ⟨j.val,lt_trans j.isLt i.isLt⟩)
        (fun j : Fin i.val=>c.coord g ⟨j.val,lt_trans j.isLt i.isLt⟩))=
        (Sum.elim (fun j : Fin i.val=>c.coord (h^m) ⟨j.val,lt_trans j.isLt i.isLt⟩)
        (fun j : Fin i.val=>c.coord h ⟨j.val,lt_trans j.isLt i.isLt⟩)) := by
      funext a
      cases a with
      | inl j => exact natpow_prefix_eq c g h i he m _ j.isLt
      | inr j => exact he _ j.isLt
    rw [hh]
    push_cast
    linarith

def canonicalLog (g : G) (i : Fin n) : ℝ := (powerPolynomial c g i).coeff 1

lemma canonicalLog_sub_of_prefix_eq (g h : G) (i : Fin n)
    (he : ∀ j : Fin n,j < i → c.coord g j=c.coord h j) :
    canonicalLog c g i-canonicalLog c h i=c.coord g i-c.coord h i := by
  have hh:=congrArg (fun p : ℝ[X]=>p.coeff 1) (powerPolynomial_sub_of_prefix_eq c g h i he)
  simpa [canonicalLog,Polynomial.coeff_X_mul] using hh

lemma canonicalLog_polynomial (i : Fin n) : RationalPolynomialMap.IsPolynomial
    (fun x=>canonicalLog c (c.coord.symm x) i) := by
  refine ⟨(universalPowerPolynomial c i).coeff 1,?_⟩
  intro x
  simp only [canonicalLog,powerPolynomial_eq_universal,Polynomial.coeff_map,
    Homeomorph.apply_symm_apply]
  rfl

def prefixSection (i : Fin n) (x : Fin i.val → ℝ) (j : Fin n) : ℝ :=
  if h : j < i then x ⟨j.val,h⟩ else 0

lemma prefixSection_polynomial (i j : Fin n) : RationalPolynomialMap.IsPolynomial
    (fun x=>prefixSection i x j) := by
  unfold prefixSection
  split_ifs with h
  · exact RationalPolynomialMap.coordinate _
  · exact RationalPolynomialMap.zero

lemma logCorrection_exists (i : Fin n) : ∃ p : MvPolynomial (Fin i.val) ℚ,
    ∀ x,canonicalLog c (c.coord.symm (prefixSection i x)) i=
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) x p :=
  RationalPolynomialMap.comp (canonicalLog_polynomial c i) (prefixSection_polynomial i)

def logCorrection (i : Fin n) : MvPolynomial (Fin i.val) ℚ := (logCorrection_exists c i).choose

lemma logCorrection_eval (i : Fin n) (x : Fin i.val → ℝ) :
    canonicalLog c (c.coord.symm (prefixSection i x)) i=
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (logCorrection c i) :=
  (logCorrection_exists c i).choose_spec x

lemma canonicalLog_eq_forward (g : G) : canonicalLog c g=
    RationalTriangularChange.forward (logCorrection c) (c.coord g) := by
  funext i
  let x : Fin i.val → ℝ := fun j=>c.coord g ⟨j.val,lt_trans j.isLt i.isLt⟩
  let h:=c.coord.symm (prefixSection i x)
  have hp : ∀ j : Fin n,j < i → c.coord g j=c.coord h j := by
    intro j hj
    simp only [h,Homeomorph.apply_symm_apply,prefixSection,dite_eq_left hj]
    rfl
  have hh:=canonicalLog_sub_of_prefix_eq c g h i hp
  have hz : c.coord h i=0 := by simp [h,prefixSection]
  rw [hz,sub_zero,logCorrection_eval] at hh
  exact (sub_eq_iff_eq_add.mp hh).trans (by rfl)

def logHomeomorph : G ≃ₜ (Fin n → ℝ) :=
  c.coord.trans (RationalTriangularChange.homeomorph (logCorrection c))

lemma logHomeomorph_apply (g : G) : logHomeomorph c g=canonicalLog c g :=
  (canonicalLog_eq_forward c g).symm

def canonicalExp (x : Fin n → ℝ) : G := (logHomeomorph c).symm x

@[simp] lemma canonicalLog_exp (x : Fin n → ℝ) : canonicalLog c (canonicalExp c x)=x := by
  rw [← logHomeomorph_apply]
  exact (logHomeomorph c).apply_symm_apply x

@[simp] lemma canonicalExp_log (g : G) : canonicalExp c (canonicalLog c g)=g := by
  rw [← logHomeomorph_apply]
  exact (logHomeomorph c).symm_apply_apply g

lemma canonicalExp_polynomial : IsPolynomialMap c (canonicalExp c) := by
  intro i
  have he (x : Fin n → ℝ) : c.coord (canonicalExp c x)=
      RationalTriangularChange.inverse (logCorrection c) x := by
    change c.coord (c.coord.symm (RationalTriangularChange.inverse (logCorrection c) x))=_
    exact c.coord.apply_symm_apply _
  simpa only [he] using RationalTriangularChange.inverse_polynomial (logCorrection c) i

lemma canonicalLog_continuous : Continuous (canonicalLog c) := by
  have he : canonicalLog c=(logHomeomorph c) := funext (fun x=>(logHomeomorph_apply c x).symm)
  rw [he]
  exact (logHomeomorph c).continuous

lemma canonicalExp_continuous : Continuous (canonicalExp c) := (logHomeomorph c).symm.continuous

lemma realPower_nat_mul (g : G) (t : ℝ) (m : ℕ) :
    realPower c g (t*m)=(realPower c g t)^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.cast_succ,mul_add,mul_one,realPower_add,ih,pow_succ]

lemma powerPolynomial_realPower (g : G) (t : ℝ) (i : Fin n) :
    powerPolynomial c (realPower c g t) i=(powerPolynomial c g i).comp (C t*X) := by
  apply Polynomial.eq_of_eval_nat_eq
  intro m
  rw [powerPolynomial_nat,eval_comp,eval_mul,eval_C,eval_X,← realPower_coord,realPower_nat_mul]

lemma canonicalLog_realPower (g : G) (t : ℝ) :
    canonicalLog c (realPower c g t)=t • canonicalLog c g := by
  funext i
  simp only [canonicalLog,powerPolynomial_realPower,comp_C_mul_X_coeff,pow_one,
    Pi.smul_apply,smul_eq_mul]
  exact mul_comm _ _

@[simp] lemma canonicalLog_one : canonicalLog c (1:G)=0 := by
  simpa using canonicalLog_realPower c (1:G) 0

@[simp] lemma canonicalExp_zero : canonicalExp c 0=(1:G) := by
  apply (logHomeomorph c).injective
  simp only [logHomeomorph_apply,canonicalLog_exp,canonicalLog_one]

lemma canonicalExp_smul (x : Fin n → ℝ) (t : ℝ) :
    canonicalExp c (t • x)=realPower c (canonicalExp c x) t := by
  apply (logHomeomorph c).injective
  simp only [logHomeomorph_apply,canonicalLog_exp,canonicalLog_realPower]

lemma canonicalLog_prefix_zero (g : G) (k : ℕ)
    (hg : ∀ i : Fin n,i.val<k → c.coord g i=0) :
    ∀ i : Fin n,i.val<k → canonicalLog c g i=0 := by
  intro i hi
  have he : powerPolynomial c g i=0 := by
    apply Polynomial.eq_of_eval_nat_eq
    intro m
    rw [powerPolynomial_nat,eval_zero]
    induction m with
    | zero => simp [c.one_coord]
    | succ m ih =>
      rw [pow_succ,coord_mul_of_right_zero c _ _ i (fun j hj=>hg j (lt_trans hj hi)),ih,hg i hi]
      exact zero_add 0
  simp only [canonicalLog,he,coeff_zero]

lemma coord_prefix_zero_of_log (g : G) (k : ℕ)
    (hg : ∀ i : Fin n,i.val<k → canonicalLog c g i=0) :
    ∀ i : Fin n,i.val<k → c.coord g i=0 := by
  have h : ∀ j,∀ hj : j<n,j<k → c.coord g ⟨j,hj⟩=0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj hk
      have hh:=canonicalLog_sub_of_prefix_eq c g 1 ⟨j,hj⟩ (by
        intro l hl
        rw [ih l.val hl l.isLt (lt_trans hl hk),c.one_coord])
      simpa only [hg ⟨j,hj⟩ hk,canonicalLog_one,Pi.zero_apply,sub_self,c.one_coord,sub_zero] using hh.symm
  exact fun i hi=>h i.val i.isLt hi

lemma canonicalLog_prefix_zero_iff (g : G) (k : ℕ) :
    (∀ i : Fin n,i.val<k → canonicalLog c g i=0) ↔
    (∀ i : Fin n,i.val<k → c.coord g i=0) :=
  ⟨coord_prefix_zero_of_log c g k,canonicalLog_prefix_zero c g k⟩

end RationalLattice
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RealPolynomialMap
variable {σ τ : Type*}

def IsPolynomial (f : (σ → ℝ) → ℝ) : Prop :=
  ∃ p : MvPolynomial σ ℝ,∀ x,f x=MvPolynomial.eval x p
lemma const (a : ℝ) : IsPolynomial (fun _ : σ → ℝ=>a) := ⟨MvPolynomial.C a,by simp⟩
lemma coordinate (i : σ) : IsPolynomial (fun x : σ → ℝ=>x i) := ⟨MvPolynomial.X i,by simp⟩
lemma add {f g : (σ → ℝ) → ℝ} (hf : IsPolynomial f) (hg : IsPolynomial g) :
    IsPolynomial (fun x=>f x+g x) := by
  obtain ⟨p,hp⟩:=hf
  obtain ⟨q,hq⟩:=hg
  exact ⟨p+q,by simp [hp,hq]⟩
lemma mul {f g : (σ → ℝ) → ℝ} (hf : IsPolynomial f) (hg : IsPolynomial g) :
    IsPolynomial (fun x=>f x*g x) := by
  obtain ⟨p,hp⟩:=hf
  obtain ⟨q,hq⟩:=hg
  exact ⟨p*q,by simp [hp,hq]⟩
lemma neg {f : (σ → ℝ) → ℝ} (hf : IsPolynomial f) : IsPolynomial (fun x=>-f x) := by
  obtain ⟨p,hp⟩:=hf
  exact ⟨-p,by simp [hp]⟩
lemma eval {f : τ → (σ → ℝ) → ℝ} (hf : ∀ i,IsPolynomial (f i)) (p : MvPolynomial τ ℝ) :
    IsPolynomial (fun x=>MvPolynomial.eval (fun i=>f i x) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using const (σ:=σ) a
  | add p q hp hq => simpa using add hp hq
  | mul_X p i hp => simpa using mul hp (hf i)
lemma rational_eval {f : τ → (σ → ℝ) → ℝ} (hf : ∀ i,IsPolynomial (f i))
    (p : MvPolynomial τ ℚ) :
    IsPolynomial (fun x=>MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun i=>f i x) p) := by
  simpa only [MvPolynomial.eval_map] using eval hf (MvPolynomial.map (algebraMap ℚ ℝ) p)
lemma of_rational {f : (σ → ℝ) → ℝ} (hf : RationalPolynomialMap.IsPolynomial f) :
    IsPolynomial f := by
  obtain ⟨p,hp⟩:=hf
  exact ⟨MvPolynomial.map (algebraMap ℚ ℝ) p,by simp only [MvPolynomial.eval_map,← hp]; simp⟩
lemma comp {f : (τ → ℝ) → ℝ} (hf : IsPolynomial f) {g : (σ → ℝ) → (τ → ℝ)}
    (hg : ∀ i,IsPolynomial (fun x=>g x i)) : IsPolynomial (fun x=>f (g x)) := by
  obtain ⟨p,hp⟩:=hf
  simpa only [hp] using eval hg p
lemma polynomial_eval (p : Polynomial ℝ) {f : (σ → ℝ) → ℝ} (hf : IsPolynomial f) :
    IsPolynomial (fun x=>p.eval (f x)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using add hp hq
  | monomial i a =>
    have hpow : IsPolynomial (fun x=>(f x)^i) := by
      induction i with
      | zero => simpa using const (σ:=σ) 1
      | succ i ih => simpa [pow_succ] using mul ih hf
    simpa using mul (const a) hpow

lemma contDiff_eval [Fintype σ] (p : MvPolynomial σ ℝ) :
    ContDiff ℝ ⊤ (fun x : σ → ℝ=>MvPolynomial.eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const : ContDiff ℝ ⊤ (fun _ : σ → ℝ=>a))
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (contDiff_apply ℝ ℝ i)

lemma contDiff [Fintype σ] {f : (σ → ℝ) → ℝ} (hf : IsPolynomial f) : ContDiff ℝ ⊤ f := by
  obtain ⟨p,hp⟩:=hf
  have he : f=(fun x=>MvPolynomial.eval x p) := funext hp
  rw [he]
  exact contDiff_eval p

lemma homogeneous_eq_fderiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : DifferentiableAt ℝ f 0) (hh : ∀ t : ℝ,∀ x,f (t • x)=t • f x) (x : E) :
    (fderiv ℝ f 0) x=f x := by
  have hr : HasDerivAt (fun t : ℝ=>t • x) x 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const x
  have h₁ : HasDerivAt (fun t : ℝ=>f (t • x)) ((fderiv ℝ f 0) x) 0 := by
    have hf' : HasFDerivAt f (fderiv ℝ f 0) ((0:ℝ) • x) := by simpa using hf.hasFDerivAt
    exact hf'.comp_hasDerivAt 0 hr
  have h₂ : HasDerivAt (fun t : ℝ=>f (t • x)) (f x) 0 := by
    simpa only [hh,one_smul,id_eq] using (hasDerivAt_id (0:ℝ)).smul_const (f x)
  exact h₁.unique h₂

end RealPolynomialMap

end
end
end
end

end OAI
