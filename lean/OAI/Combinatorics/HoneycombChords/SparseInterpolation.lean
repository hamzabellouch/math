import OAI.Combinatorics.HoneycombChords.LaplaceProducts

namespace OAI

/-! Sparse Newton interpolation and positive reciprocal product comparisons.

The development follows OpenAI, *Uniform marked-polygon estimates and sharp finite bridge moments*
(2026), Sections 6 and 7. -/

section


namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Finset Matrix

noncomputable def newtonEvaluation (m : ℕ) (v : ℕ → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => (newtonBasis v i).eval (v j)

lemma newtonEvaluation_det_pos {m : ℕ} {v : ℕ → ℝ}
    (hv : StrictMono (fun i : Fin m=>v i)) : 0<(newtonEvaluation m v).det := by
  have he : newtonEvaluation m v=newtonJetMatrix m v := by
    ext i j
    rw [newtonJetMatrix,nodalOrder_eq_zero_strict hv,polynomialJet_zero]
    rfl
  rw [he]
  exact newtonJetMatrix_det_pos v hv.monotone

noncomputable def sparseCofactorMatrix {n : ℕ} (v : ℕ → ℝ) (e : Fin n → ℕ)
    (k : Fin (n+1)) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  Fin.cases (fun j=>if j=k then (-1)^k.val else 0) (fun i j=>powerNewton v (e i) j)

lemma sparseCofactorMatrix_det_nonneg {n : ℕ} (v : ℕ → ℝ) (hv : ∀ i,0≤v i)
    (e : Fin n → ℕ) (he : StrictMono e) (k : Fin (n+1)) :
    0≤(sparseCofactorMatrix v e k).det := by
  classical
  have hm : (sparseCofactorMatrix v e k).submatrix Fin.succ k.succAbove=
      fun i j=>powerNewton v (e i) (k.succAbove j).val := rfl
  rw [Matrix.det_succ_row_zero]
  have hs : (∑ j : Fin (n+1),(-1:ℝ)^j.val*sparseCofactorMatrix v e k 0 j*
      ((sparseCofactorMatrix v e k).submatrix Fin.succ j.succAbove).det)=
      (-1)^(k.val+k.val)*((sparseCofactorMatrix v e k).submatrix Fin.succ k.succAbove).det := by
    rw [sum_eq_single k]
    · simp [sparseCofactorMatrix,pow_add,mul_assoc]
    · intro j _ hj
      simp only [sparseCofactorMatrix,Fin.cases_zero,ite_eq_right hj,mul_zero,zero_mul]
    · simp
  rw [hs,hm,show (-1:ℝ)^(k.val+k.val)=1 by rw [←two_mul,Even.neg_one_pow (even_two_mul k.val)],one_mul]
  apply powerNewton_det_nonneg v hv e (fun j=>(k.succAbove j).val) he
  exact k.strictMono_succAbove

noncomputable def sparseTestMatrix {n : ℕ} (v : ℕ → ℝ) (e : Fin n → ℕ)
    (k : Fin (n+1)) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  Fin.cases (fun j=>(-1)^k.val*(newtonBasis v k).eval (v j)) (fun i j=>(v j)^(e i))

lemma sparseTestMatrix_factor {n : ℕ} (v : ℕ → ℝ) (e : Fin n → ℕ) (k : Fin (n+1)) :
    sparseTestMatrix v e k=sparseCofactorMatrix v e k*newtonEvaluation (n+1) v := by
  classical
  ext i j
  refine Fin.cases ?_ (fun i=>?_) i
  · simp only [sparseTestMatrix,Fin.cases_zero,Matrix.mul_apply,sparseCofactorMatrix]
    rw [sum_eq_single k]
    · simp [newtonEvaluation]
    · intro a _ ha;simp [ha]
    · simp
  · change (v j)^e i=∑ a : Fin (n+1),powerNewton v (e i) a*(newtonBasis v a).eval (v j)
    exact powerNewton_evaluation v (e i) j

lemma sparseTestMatrix_det_nonneg {n : ℕ} (v : ℕ → ℝ) (hv : ∀ i,0≤v i)
    (hord : StrictMono (fun i : Fin (n+1)=>v i))
    (e : Fin n → ℕ) (he : StrictMono e) (k : Fin (n+1)) :
    0≤(sparseTestMatrix v e k).det := by
  rw [sparseTestMatrix_factor,Matrix.det_mul]
  exact mul_nonneg (sparseCofactorMatrix_det_nonneg v hv e he k) (newtonEvaluation_det_pos hord).le

/-- The alternating-Newton polynomial divided-difference numerator is
nonnegative against the sparse interpolation weights at the origin. -/
lemma sparse_newton_numerator_nonneg {n : ℕ} (v : ℕ → ℝ) (hv : ∀ i,0≤v i)
    (hord : StrictMono (fun i : Fin (n+1)=>v i))
    (e : Fin n → ℕ) (he : StrictMono e) (k : Fin (n+1)) :
    0≤Matrix.det (Fin.cases (fun j : Fin (n+1)=>v j*((-1)^k.val*(newtonBasis v k).eval (v j)))
      (fun i j=>(v j)^(e i+1))) := by
  have hm : (Fin.cases (fun j : Fin (n+1)=>v j*((-1)^k.val*(newtonBasis v k).eval (v j)))
      (fun i j=>(v j)^(e i+1)))=fun (i j : Fin (n+1))=>v j*sparseTestMatrix v e k i j := by
    ext i j
    refine Fin.cases ?_ (fun i=>?_) i
    · rfl
    · simp [sparseTestMatrix,pow_succ']
  rw [hm]
  calc
    0≤(∏ i : Fin (n+1),v i)*(sparseTestMatrix v e k).det :=
      mul_nonneg (prod_nonneg (fun i _=>hv i)) (sparseTestMatrix_det_nonneg v hv hord e he k)
    _=Matrix.det (fun i j : Fin (n+1)=>v j*sparseTestMatrix v e k i j) :=
      (Matrix.det_mul_row (fun j : Fin (n+1)=>v j) (sparseTestMatrix v e k)).symm

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Finset Matrix

noncomputable def sparseExponent {n : ℕ} (e : Fin n → ℕ) : Fin (n+1) → ℕ :=
  Fin.cons 0 (fun i=>e i+1)

lemma sparseExponent_strictMono {n : ℕ} {e : Fin n → ℕ} (he : StrictMono e) :
    StrictMono (sparseExponent e) := by
  apply Fin.strictMono_cons.mpr
  exact ⟨fun i=>Nat.zero_lt_succ _,fun i j hij=>Nat.add_lt_add_right (he hij) 1⟩

noncomputable def sparseMatrix {n : ℕ} (v : ℕ → ℝ) (e : Fin n → ℕ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ := fun i j=>(v j)^sparseExponent e i

lemma sparseMatrix_eq {n : ℕ} (v : ℕ → ℝ) (e : Fin n → ℕ) :
    sparseMatrix v e=Fin.cases (fun _=>1) (fun i j=>(v j)^(e i+1)) := by
  ext i j
  refine Fin.cases ?_ (fun i=>?_) i <;> simp [sparseMatrix,sparseExponent]

lemma sparseMatrix_det_pos {n : ℕ} {v : ℕ → ℝ} {e : Fin n → ℕ}
    (hv : ∀ i : Fin (n+1),0<v i) (hord : StrictMono (fun i : Fin (n+1)=>v i))
    (he : StrictMono e) : 0<(sparseMatrix v e).det :=
  power_det_pos _ _ (sparseExponent_strictMono he) hord hv

noncomputable def sparseWeight {n : ℕ} (v : ℕ → ℝ) (e : Fin n → ℕ) (j : Fin (n+1)) : ℝ :=
  (-1)^j.val*((sparseMatrix v e).submatrix Fin.succ j.succAbove).det/(sparseMatrix v e).det

lemma sparseWeight_eval {n : ℕ} (v : ℕ → ℝ) (e : Fin n → ℕ) (f : Fin (n+1) → ℝ) :
    (∑ j,sparseWeight v e j*f j)=
      Matrix.det (Fin.cases f (fun i j=>(v j)^(e i+1)))/(sparseMatrix v e).det := by
  classical
  simp only [sparseWeight,div_mul_eq_mul_div,←sum_div]
  congr 1
  erw [Matrix.det_succ_row_zero]
  apply sum_congr rfl
  intro j hj
  have hm : Matrix.submatrix (Fin.cases f (fun i j=>(v j)^(e i+1)) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
      Fin.succ j.succAbove=(sparseMatrix v e).submatrix Fin.succ j.succAbove := by
    ext i k
    change (v (j.succAbove k))^(e i+1)=(v (j.succAbove k))^(e i+1)
    rfl
  rw [hm]
  simp only [Fin.cases_zero]
  ring

lemma sparseWeight_sum {n : ℕ} {v : ℕ → ℝ} {e : Fin n → ℕ}
    (hv : ∀ i : Fin (n+1),0<v i) (hord : StrictMono (fun i : Fin (n+1)=>v i))
    (he : StrictMono e) : ∑ j,sparseWeight v e j=1 := by
  simpa only [mul_one,←sparseMatrix_eq,div_self (ne_of_gt (sparseMatrix_det_pos hv hord he))] using
    sparseWeight_eval v e (fun _=>1)

lemma sparseWeight_power {n : ℕ} (v : ℕ → ℝ) (e : Fin n → ℕ) (i : Fin n) :
    ∑ j,sparseWeight v e j*(v j)^(e i+1)=0 := by
  rw [sparseWeight_eval]
  have hz : Matrix.det (Fin.cases (fun j : Fin (n+1)=>(v j)^(e i+1))
      (fun i j=>(v j)^(e i+1)))=0 := by
    apply Matrix.det_zero_of_row_eq (Fin.succ_ne_zero i).symm
    funext j
    simp
  rw [hz,zero_div]

noncomputable def backwardNewton (v : ℕ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ∏ i ∈ range k,(v i-x)
noncomputable def nodeProd (v : ℕ → ℝ) (k : ℕ) : ℝ := ∏ i ∈ range k,v i

lemma backwardNewton_eval (v : ℕ → ℝ) (k : ℕ) (x : ℝ) :
    backwardNewton v k x=(-1)^k*(newtonBasis v k).eval x := by
  simp only [backwardNewton,newtonBasis,Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
  calc
    (∏ i ∈ range k,(v i-x))=∏ i ∈ range k,-(x-v i) := by congr 1;ext i;ring
    _=_ := by rw [Finset.prod_neg];simp only [card_range]

lemma nodeProd_pos (v : ℕ → ℝ) (hv : ∀ i,0<v i) (k : ℕ) : 0<nodeProd v k :=
  prod_pos (fun i _=>hv i)

noncomputable def coxianWeight {n : ℕ} (v : ℕ → ℝ) (e : Fin n → ℕ) (k : Fin (n+1)) : ℝ :=
  (∑ j,sparseWeight v e j*(v j*backwardNewton v k (v j)))/nodeProd v (k+1)

lemma coxianWeight_nonneg {n : ℕ} (v : ℕ → ℝ) (hv : ∀ i,0<v i)
    (hord : StrictMono (fun i : Fin (n+1)=>v i)) (e : Fin n → ℕ) (he : StrictMono e)
    (k : Fin (n+1)) : 0≤coxianWeight v e k := by
  unfold coxianWeight
  apply div_nonneg _ (nodeProd_pos v hv _).le
  rw [sparseWeight_eval]
  apply div_nonneg _ (sparseMatrix_det_pos (fun i=>hv i) hord he).le
  simp only [backwardNewton_eval]
  exact sparse_newton_numerator_nonneg v (fun i=>(hv i).le) hord e he k

lemma backwardNewton_telescope (v : ℕ → ℝ) (hv : ∀ i,v i≠0) (x : ℝ) (m : ℕ) :
    (∑ k ∈ range m,x*backwardNewton v k x/nodeProd v (k+1))=
      1-backwardNewton v m x/nodeProd v m := by
  induction m with
  | zero => simp [backwardNewton,nodeProd]
  | succ m ih =>
    have hp : nodeProd v m≠0 := prod_ne_zero_iff.mpr (fun i _=>hv i)
    rw [sum_range_succ,ih]
    simp only [backwardNewton,nodeProd,prod_range_succ]
    change 1-backwardNewton v m x/nodeProd v m+x*backwardNewton v m x/(nodeProd v m*v m)=
      1-backwardNewton v m x*(v m-x)/(nodeProd v m*v m)
    field_simp [hp,hv m]
    ; ring

lemma backwardNewton_node {m : ℕ} (v : ℕ → ℝ) (j : Fin m) : backwardNewton v m (v j)=0 := by
  apply prod_eq_zero (s:=range m) (i:=j.val) (mem_range.mpr j.isLt)
  simp

lemma coxianWeight_sum {n : ℕ} (v : ℕ → ℝ) (hv : ∀ i,0<v i)
    (hord : StrictMono (fun i : Fin (n+1)=>v i)) (e : Fin n → ℕ) (he : StrictMono e) :
    ∑ k,coxianWeight v e k=1 := by
  have ht (j : Fin (n+1)) :
      (∑ k : Fin (n+1),v j*backwardNewton v k (v j)/nodeProd v (k+1))=1 := by
    rw [Fin.sum_univ_eq_sum_range (fun k=>v j*backwardNewton v k (v j)/nodeProd v (k+1)) (n+1),
      backwardNewton_telescope v (fun i=>(hv i).ne'),backwardNewton_node,zero_div,sub_zero]
  simp only [coxianWeight,sum_div]
  rw [sum_comm]
  calc
    _ = ∑ j : Fin (n+1),sparseWeight v e j*(∑ k : Fin (n+1),v j*backwardNewton v k (v j)/nodeProd v (k+1)) := by
      apply sum_congr rfl
      intro j hj
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      ring
    _=∑ j : Fin (n+1),sparseWeight v e j := by simp only [ht,mul_one]
    _=1 := sparseWeight_sum (fun i=>hv i) hord he

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section


namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Finset

inductive ReciprocalExpr where
  | const : ℝ → ReciprocalExpr
  | add : ReciprocalExpr → ReciprocalExpr → ReciprocalExpr
  | scale : ℝ → ReciprocalExpr → ReciprocalExpr
  | pole : ℝ → ReciprocalExpr → ReciprocalExpr

namespace ReciprocalExpr
noncomputable def eval : ReciprocalExpr → ℝ → ℝ
  | const c,_ => c
  | add A B,x => eval A x+eval B x
  | scale c A,x => c*eval A x
  | pole b A,x => eval A x/(b+x)

def PolesAbove (L : ℝ) : ReciprocalExpr → Prop
  | const _ => True
  | add A B => PolesAbove L A ∧ PolesAbove L B
  | scale _ A => PolesAbove L A
  | pole b A => L<b ∧ PolesAbove L A

def CoeffNonneg : ReciprocalExpr → Prop
  | const c => 0≤c
  | add A B => CoeffNonneg A ∧ CoeffNonneg B
  | scale c A => 0≤c ∧ CoeffNonneg A
  | pole _ A => CoeffNonneg A

lemma eval_nonneg {A : ReciprocalExpr} {L x : ℝ}
    (hA : A.PolesAbove L) (hp : A.CoeffNonneg) (hx : -L≤x) : 0≤A.eval x := by
  induction A with
  | const c => exact hp
  | add A B ihA ihB => exact add_nonneg (ihA hA.1 hp.1) (ihB hA.2 hp.2)
  | scale c A ih => exact mul_nonneg hp.1 (ih hA hp.2)
  | pole b A ih => exact div_nonneg (ih hA.2 hp) (by linarith [hA.1])

noncomputable def difference (v : ℝ) : ReciprocalExpr → ReciprocalExpr
  | const _ => const 0
  | add A B => add (difference v A) (difference v B)
  | scale c A => scale c (difference v A)
  | pole b A => scale ((b+v)⁻¹) (add (difference v A) (pole b A))

lemma difference_poles {A : ReciprocalExpr} {L : ℝ} (v : ℝ) (hA : A.PolesAbove L) :
    (A.difference v).PolesAbove L := by
  induction A with
  | const c => trivial
  | add A B ihA ihB => exact ⟨ihA hA.1,ihB hA.2⟩
  | scale c A ih => exact ih hA
  | pole b A ih => exact ⟨ih hA.2,hA⟩

lemma difference_coeff_nonneg {A : ReciprocalExpr} {L v : ℝ}
    (hA : A.PolesAbove L) (hp : A.CoeffNonneg) (hv : -L≤v) :
    (A.difference v).CoeffNonneg := by
  induction A with
  | const c => exact le_rfl
  | add A B ihA ihB => exact ⟨ihA hA.1 hp.1,ihB hA.2 hp.2⟩
  | scale c A ih => exact ⟨hp.1,ih hA hp.2⟩
  | pole b A ih => exact ⟨inv_nonneg.mpr (by linarith [hA.1]),ih hA.2 hp,hp⟩

lemma difference_identity {A : ReciprocalExpr} {L v x : ℝ}
    (hA : A.PolesAbove L) (hv : -L≤v) (hx : -L≤x) :
    A.eval v-A.eval x=(x-v)*(A.difference v).eval x := by
  induction A with
  | const c => simp [eval,difference]
  | add A B ihA ihB =>
    simp only [eval,difference]
    rw [show A.eval v=A.eval x+(x-v)*(A.difference v).eval x by linarith [ihA hA.1],
      show B.eval v=B.eval x+(x-v)*(B.difference v).eval x by linarith [ihB hA.2]]
    ring
  | scale c A ih =>
    simp only [eval,difference]
    rw [show A.eval v=A.eval x+(x-v)*(A.difference v).eval x by linarith [ih hA]]
    ring
  | pole b A ih =>
    have hV : b+v≠0 := ne_of_gt (by linarith [hA.1])
    have hX : b+x≠0 := ne_of_gt (by linarith [hA.1])
    simp only [eval,difference]
    rw [show A.eval v=A.eval x+(x-v)*(A.difference v).eval x by linarith [ih hA.2]]
    field_simp
    ; ring

noncomputable def newtonExpr (v : ℕ → ℝ) (A : ReciprocalExpr) : ℕ → ReciprocalExpr
  | 0 => A
  | k+1 => (newtonExpr v A k).difference (v k)
noncomputable def newtonCoefficient (v : ℕ → ℝ) (A : ReciprocalExpr) (k : ℕ) : ℝ :=
  (newtonExpr v A k).eval (v k)

lemma newtonExpr_poles {A : ReciprocalExpr} {L : ℝ} (v : ℕ → ℝ) (k : ℕ)
    (hA : A.PolesAbove L) : (newtonExpr v A k).PolesAbove L := by
  induction k with
  | zero => exact hA
  | succ k ih => exact difference_poles _ ih

lemma newtonExpr_coeff_nonneg {A : ReciprocalExpr} {L : ℝ} (v : ℕ → ℝ) (k : ℕ)
    (hA : A.PolesAbove L) (hp : A.CoeffNonneg) (hv : ∀ i,-L≤v i) :
    (newtonExpr v A k).CoeffNonneg := by
  induction k with
  | zero => exact hp
  | succ k ih => exact difference_coeff_nonneg (newtonExpr_poles v k hA) ih (hv k)

lemma newtonCoefficient_nonneg {A : ReciprocalExpr} {L : ℝ} (v : ℕ → ℝ) (k : ℕ)
    (hA : A.PolesAbove L) (hp : A.CoeffNonneg) (hv : ∀ i,-L≤v i) :
    0≤newtonCoefficient v A k :=
  eval_nonneg (newtonExpr_poles v k hA) (newtonExpr_coeff_nonneg v k hA hp hv) (hv k)

lemma newton_expansion {A : ReciprocalExpr} {L x : ℝ} (v : ℕ → ℝ) (m : ℕ)
    (hA : A.PolesAbove L) (hv : ∀ i,-L≤v i) (hx : -L≤x) :
    A.eval x=(∑ k ∈ range m,newtonCoefficient v A k*backwardNewton v k x)+
      backwardNewton v m x*(newtonExpr v A m).eval x := by
  induction m with
  | zero => simp [backwardNewton,newtonExpr]
  | succ m ih =>
    rw [sum_range_succ]
    have hh := difference_identity (newtonExpr_poles v m hA) (hv m) hx
    have he : (newtonExpr v A m).eval x=newtonCoefficient v A m+(v m-x)*(newtonExpr v A (m+1)).eval x := by
      dsimp only [newtonCoefficient,newtonExpr]
      linarith only [hh]
    conv_lhs => rw [ih,he]
    simp only [backwardNewton,prod_range_succ]
    ring

lemma newton_evaluation {A : ReciprocalExpr} {L : ℝ} (v : ℕ → ℝ) {m : ℕ} (j : Fin m)
    (hA : A.PolesAbove L) (hv : ∀ i,-L≤v i) :
    A.eval (v j)=∑ k : Fin m,newtonCoefficient v A k*backwardNewton v k (v j) := by
  rw [newton_expansion v m hA hv (hv j),backwardNewton_node,zero_mul,add_zero]
  exact (Fin.sum_univ_eq_sum_range (fun k=>newtonCoefficient v A k*backwardNewton v k (v j)) m).symm

lemma newtonExpr_add (v : ℕ → ℝ) (A B : ReciprocalExpr) (k : ℕ) :
    newtonExpr v (add A B) k=add (newtonExpr v A k) (newtonExpr v B k) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [newtonExpr,ih,difference]
lemma newtonExpr_scale (v : ℕ → ℝ) (c : ℝ) (A : ReciprocalExpr) (k : ℕ) :
    newtonExpr v (scale c A) k=scale c (newtonExpr v A k) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [newtonExpr,ih,difference]
lemma newtonCoefficient_add (v : ℕ → ℝ) (A B : ReciprocalExpr) (k : ℕ) :
    newtonCoefficient v (add A B) k=newtonCoefficient v A k+newtonCoefficient v B k := by
  simp only [newtonCoefficient,newtonExpr_add,eval]
lemma newtonCoefficient_scale (v : ℕ → ℝ) (c : ℝ) (A : ReciprocalExpr) (k : ℕ) :
    newtonCoefficient v (scale c A) k=c*newtonCoefficient v A k := by
  simp only [newtonCoefficient,newtonExpr_scale,eval]

lemma newtonExpr_eval_congr {m : ℕ} {A B : ReciprocalExpr} {L : ℝ} (v : ℕ → ℝ)
    (hA : A.PolesAbove L) (hB : B.PolesAbove L) (hv : ∀ i,-L≤v i)
    (hord : StrictMono (fun i : Fin m=>v i))
    (he : ∀ j : Fin m,A.eval (v j)=B.eval (v j)) (k : ℕ) (j : Fin m) (hkj : k≤j.val) :
    (newtonExpr v A k).eval (v j)=(newtonExpr v B k).eval (v j) := by
  induction k generalizing j with
  | zero => exact he j
  | succ k ih =>
    let i : Fin m:=⟨k,by omega⟩
    have hi := ih i le_rfl
    have hj := ih j (by omega)
    have hA' := difference_identity (newtonExpr_poles v k hA) (hv k) (hv j)
    have hB' := difference_identity (newtonExpr_poles v k hB) (hv k) (hv j)
    have hn : v j-v k≠0 := sub_ne_zero.mpr (ne_of_gt (hord (show i<j by change k<j.val; omega)))
    apply (mul_left_cancel₀ hn)
    change (v j-v k)*((newtonExpr v A k).difference (v k)).eval (v j)=
      (v j-v k)*((newtonExpr v B k).difference (v k)).eval (v j)
    rw [←hA',←hB',hj]
    exact congrArg (fun z=>z-(newtonExpr v B k).eval (v j)) hi

lemma newtonCoefficient_congr {m : ℕ} {A B : ReciprocalExpr} {L : ℝ} (v : ℕ → ℝ)
    (hA : A.PolesAbove L) (hB : B.PolesAbove L) (hv : ∀ i,-L≤v i)
    (hord : StrictMono (fun i : Fin m=>v i))
    (he : ∀ j : Fin m,A.eval (v j)=B.eval (v j)) (k : Fin m) :
    newtonCoefficient v A k=newtonCoefficient v B k :=
  newtonExpr_eval_congr v hA hB hv hord he k k le_rfl

end ReciprocalExpr
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section


namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Finset Polynomial

noncomputable def sparseEval {n : ℕ} (v : ℕ → ℝ) (e : Fin n → ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑ j : Fin (n+1),sparseWeight v e j*f (v j)

lemma sparseEval_add {n : ℕ} (v : ℕ → ℝ) (e : Fin n → ℕ) (f g : ℝ → ℝ) :
    sparseEval v e (fun x=>f x+g x)=sparseEval v e f+sparseEval v e g := by
  simp [sparseEval,mul_add,sum_add_distrib]
lemma sparseEval_scale {n : ℕ} (v : ℕ → ℝ) (e : Fin n → ℕ) (c : ℝ) (f : ℝ → ℝ) :
    sparseEval v e (fun x=>c*f x)=c*sparseEval v e f := by
  simp only [sparseEval,mul_sum];apply sum_congr rfl;intro i hi;ring

lemma sparseEval_rational {n : ℕ} {A : ReciprocalExpr} {L : ℝ}
    (v : ℕ → ℝ) (e : Fin n → ℕ) (hv : ∀ i,0<v i) (hL : ∀ i,-L≤v i)
    (hA : A.PolesAbove L) :
    sparseEval v e (fun x=>x*A.eval x)=
      ∑ k : Fin (n+1),coxianWeight v e k*nodeProd v (k+1)*ReciprocalExpr.newtonCoefficient v A k := by
  unfold sparseEval
  simp only [ReciprocalExpr.newton_evaluation v _ hA hL,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  rw [coxianWeight,div_mul_cancel₀ _ (ne_of_gt (nodeProd_pos v hv _)),sum_mul]
  apply sum_congr rfl
  intro j hj
  ring

lemma sparseEval_rational_nonneg {n : ℕ} {A : ReciprocalExpr} {L : ℝ}
    (v : ℕ → ℝ) (e : Fin n → ℕ) (hv : ∀ i,0<v i)
    (hord : StrictMono (fun i : Fin (n+1)=>v i)) (he : StrictMono e)
    (hL : ∀ i,-L≤v i) (hA : A.PolesAbove L) (hp : A.CoeffNonneg) :
    0≤ sparseEval v e (fun x=>x*A.eval x) := by
  rw [sparseEval_rational v e hv hL hA]
  exact sum_nonneg fun k _=>mul_nonneg
    (mul_nonneg (coxianWeight_nonneg v hv hord e he k) (nodeProd_pos v hv _).le)
    (ReciprocalExpr.newtonCoefficient_nonneg v k hA hp hL)

lemma sparseEval_polynomial_zero {n q : ℕ} (v : ℕ → ℝ) (e : Fin n → ℕ)
    (hq : ∀ m,1 ≤ m → m ≤ q → ∃ i,e i+1=m) (P : Polynomial ℝ)
    (hd : P.natDegree≤q) (hz : P.coeff 0=0) : sparseEval v e P.eval=0 := by
  unfold sparseEval
  simp_rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hd),mul_sum]
  rw [sum_comm]
  apply sum_eq_zero
  intro m hm
  by_cases hm0 : m=0
  · subst m;simp [hz]
  · obtain ⟨i,hi⟩ := hq m (by omega) (by simpa using Nat.le_of_lt_succ (mem_range.mp hm))
    have hp:=sparseWeight_power v e i
    rw [hi] at hp
    calc
      _=P.coeff m*(∑ j : Fin (n+1),sparseWeight v e j*v j^m) := by
        rw [mul_sum];apply sum_congr rfl;intro j hj;ring
      _=0 := by rw [hp,mul_zero]

lemma coxianWeight_eq_zero {n q : ℕ} (v : ℕ → ℝ) (e : Fin n → ℕ)
    (hq : ∀ m,1 ≤ m → m ≤ q → ∃ i,e i+1=m) (k : Fin (n+1)) (hk : k.val<q) :
    coxianWeight v e k=0 := by
  let P : Polynomial ℝ:=X*∏ i ∈ range k.val,(Polynomial.C (v i)-X)
  have hd : P.natDegree≤q := by
    have hn (i:ℕ) : (Polynomial.C (v i)-(X:Polynomial ℝ)).natDegree=1 := by
      rw [←neg_sub,Polynomial.natDegree_neg,Polynomial.natDegree_X_sub_C]
    have hp : (∏ i ∈ range k.val,(Polynomial.C (v i)-(X:Polynomial ℝ))).natDegree ≤ k.val := by
      simpa only [hn,sum_const,card_range,smul_eq_mul,mul_one] using
        Polynomial.natDegree_prod_le (range k.val) (fun i=>Polynomial.C (v i)-(X:Polynomial ℝ))
    calc
      _ ≤ (X:Polynomial ℝ).natDegree+(∏ i ∈ range k.val,(Polynomial.C (v i)-X)).natDegree := Polynomial.natDegree_mul_le
      _ ≤ 1+k.val := by rw [Polynomial.natDegree_X];exact Nat.add_le_add_left hp 1
      _ ≤ q := by omega
  have hz : P.coeff 0=0 := by simp [P,Polynomial.coeff_zero_eq_eval_zero]
  have heval : P.eval=fun x=>x*backwardNewton v k x := by
    funext x
    simp only [P,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_prod,
      Polynomial.eval_sub,Polynomial.eval_C,backwardNewton]
  have hh:=sparseEval_polynomial_zero v e hq P hd hz
  rw [heval] at hh
  change sparseEval v e (fun x=>x*backwardNewton v k x)/nodeProd v (k+1)=0
  rw [hh,zero_div]

noncomputable def poleProduct (v : ℕ → ℝ) (a : ℝ) (k : ℕ) : ℝ :=
  ∏ i ∈ range k,v i/(a+v i)

lemma poleProduct_pos (v : ℕ → ℝ) (hv : ∀ i,0<v i) {a : ℝ} (ha : 0<a) (k:ℕ) :
    0<poleProduct v a k := prod_pos (fun i _=>div_pos (hv i) (add_pos ha (hv i)))
lemma poleProduct_antitone (v : ℕ → ℝ) (hv : ∀ i,0<v i) {a : ℝ} (ha : 0<a) :
    Antitone (poleProduct v a) := by
  intro k m hkm
  apply prod_le_prod_of_subset_of_le_one₀ (range_mono hkm)
  · intro i hi;exact (div_pos (hv i) (add_pos ha (hv i))).le
  · intro i hi hni;exact (div_le_one (add_pos ha (hv i))).mpr (by linarith)

lemma newtonExpr_head (v : ℕ → ℝ) (A : ReciprocalExpr) (k : ℕ) :
    ReciprocalExpr.newtonExpr v A (k+1)=
      ReciprocalExpr.newtonExpr (fun i=>v (i+1)) (A.difference (v 0)) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (ReciprocalExpr.newtonExpr v A (k+1)).difference (v (k+1)) = _
    rw [ih]
    rfl

lemma newtonExpr_zero (v : ℕ → ℝ) (k : ℕ) :
    ReciprocalExpr.newtonExpr v (.const 0) k=.const 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [ReciprocalExpr.newtonExpr,ih,ReciprocalExpr.difference]

lemma newtonExpr_reciprocal (v : ℕ → ℝ) (a : ℝ) (k : ℕ) (x : ℝ) :
    (ReciprocalExpr.newtonExpr v (.pole a (.const 1)) k).eval x=
      (∏ i ∈ range k,(a+v i))⁻¹/(a+x) := by
  induction k generalizing v with
  | zero => simp [ReciprocalExpr.newtonExpr,ReciprocalExpr.eval]
  | succ k ih =>
    rw [newtonExpr_head]
    simp only [ReciprocalExpr.difference,ReciprocalExpr.newtonExpr_scale,
      ReciprocalExpr.newtonExpr_add,newtonExpr_zero,ReciprocalExpr.eval,zero_add,ih]
    rw [prod_range_succ',mul_inv_rev]
    ring

lemma newtonCoefficient_reciprocal (v : ℕ → ℝ) (a : ℝ) (k : ℕ) :
    ReciprocalExpr.newtonCoefficient v (.pole a (.const 1)) k=
      (∏ i ∈ range (k+1),(a+v i))⁻¹ := by
  unfold ReciprocalExpr.newtonCoefficient
  rw [newtonExpr_reciprocal,prod_range_succ,mul_inv_rev]
  ring

lemma sparseEval_reciprocal {n : ℕ} (v : ℕ → ℝ) (e : Fin n → ℕ)
    (hv : ∀ i,0<v i) {a : ℝ} (ha : 0<a) :
    sparseEval v e (fun x=>x/(a+x))=
      ∑ k : Fin (n+1),coxianWeight v e k*poleProduct v a (k+1) := by
  have heval : (fun x=>x/(a+x))=(fun x=>x*(ReciprocalExpr.pole a (.const 1)).eval x) := by
    funext x;simp [ReciprocalExpr.eval,div_eq_mul_inv]
  rw [heval,sparseEval_rational v e hv (L:=0) (fun i=>by simpa using (hv i).le)
    (show (ReciprocalExpr.pole a (.const 1)).PolesAbove 0 from ⟨ha,trivial⟩)]
  apply sum_congr rfl
  intro k hk
  rw [newtonCoefficient_reciprocal,poleProduct,Finset.prod_div_distrib]
  simp only [nodeProd,div_eq_mul_inv,mul_assoc]

lemma sparseEval_reciprocal_lower {n : ℕ} (v : ℕ → ℝ) (e : Fin n → ℕ)
    (hv : ∀ i,0<v i) (hord : StrictMono (fun i : Fin (n+1)=>v i)) (he : StrictMono e)
    {a : ℝ} (ha : 0<a) :
    poleProduct v a (n+1)≤ sparseEval v e (fun x=>x/(a+x)) := by
  rw [sparseEval_reciprocal v e hv ha]
  calc
    _=(∑ k : Fin (n+1),coxianWeight v e k)*poleProduct v a (n+1) := by
      rw [coxianWeight_sum v hv hord e he,one_mul]
    _=∑ k : Fin (n+1),coxianWeight v e k*poleProduct v a (n+1) := by rw [sum_mul]
    _≤_ := sum_le_sum fun k _=>mul_le_mul_of_nonneg_left
      (poleProduct_antitone v hv ha (by omega)) (coxianWeight_nonneg v hv hord e he k)

lemma sparseEval_reciprocal_upper {n q : ℕ} (v : ℕ → ℝ) (e : Fin n → ℕ)
    (hv : ∀ i,0<v i) (hord : StrictMono (fun i : Fin (n+1)=>v i)) (he : StrictMono e)
    (hq : ∀ m,1 ≤ m → m ≤ q → ∃ i,e i+1=m) {a : ℝ} (ha : 0<a) :
    sparseEval v e (fun x=>x/(a+x))≤poleProduct v a (q+1) := by
  rw [sparseEval_reciprocal v e hv ha]
  calc
    _≤∑ k : Fin (n+1),coxianWeight v e k*poleProduct v a (q+1) := by
      apply sum_le_sum
      intro k hk
      by_cases hqk : q≤k.val
      · exact mul_le_mul_of_nonneg_left (poleProduct_antitone v hv ha (by omega))
          (coxianWeight_nonneg v hv hord e he k)
      · rw [coxianWeight_eq_zero v e hq k (by omega),zero_mul,zero_mul]
    _=(∑ k : Fin (n+1),coxianWeight v e k)*poleProduct v a (q+1) := by rw [sum_mul]
    _=_ := by rw [coxianWeight_sum v hv hord e he,one_mul]

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Finset
namespace ReciprocalExpr

lemma poles_mono {A : ReciprocalExpr} {L K : ℝ} (h : K ≤ L) (hA : A.PolesAbove L) :
    A.PolesAbove K := by
  induction A with
  | const c => trivial
  | add A B ihA ihB => exact ⟨ihA hA.1,ihB hA.2⟩
  | scale c A ih => exact ih hA
  | pole b A ih => exact ⟨lt_of_le_of_lt h hA.1,ih hA.2⟩

noncomputable def mulExpr : ReciprocalExpr → ReciprocalExpr → ReciprocalExpr
  | const c,B => scale c B
  | add A A',B => add (mulExpr A B) (mulExpr A' B)
  | scale c A,B => scale c (mulExpr A B)
  | pole b A,B => pole b (mulExpr A B)

lemma mulExpr_eval (A B : ReciprocalExpr) (x : ℝ) :
    (mulExpr A B).eval x = A.eval x * B.eval x := by
  induction A with
  | const c => rfl
  | add A A' ih ih' => simp only [mulExpr,eval,ih,ih'];ring
  | scale c A ih => simp only [mulExpr,eval,ih];ring
  | pole b A ih => simp only [mulExpr,eval,ih];ring

lemma mulExpr_poles {A B : ReciprocalExpr} {L : ℝ}
    (hA : A.PolesAbove L) (hB : B.PolesAbove L) : (mulExpr A B).PolesAbove L := by
  induction A with
  | const c => exact hB
  | add A A' ih ih' => exact ⟨ih hA.1,ih' hA.2⟩
  | scale c A ih => exact ih hA
  | pole b A ih => exact ⟨hA.1,ih hA.2⟩
lemma mulExpr_coeff {A B : ReciprocalExpr}
    (hA : A.CoeffNonneg) (hB : B.CoeffNonneg) : (mulExpr A B).CoeffNonneg := by
  induction A with
  | const c => exact ⟨hA,hB⟩
  | add A A' ih ih' => exact ⟨ih hA.1,ih' hA.2⟩
  | scale c A ih => exact ⟨hA.1,ih hA.2⟩
  | pole b A ih => exact ih hA

noncomputable def normalizedPole (b : ℝ) : ReciprocalExpr := scale b (pole b (const 1))
lemma normalizedPole_eval (b x : ℝ) : (normalizedPole b).eval x = b/(b+x) := by
  simp [normalizedPole,eval,div_eq_mul_inv]
lemma normalizedPole_poles {b L : ℝ} (hb : L < b) : (normalizedPole b).PolesAbove L := ⟨hb,trivial⟩
lemma normalizedPole_coeff {b : ℝ} (hb : 0 ≤ b) : (normalizedPole b).CoeffNonneg := ⟨hb,zero_le_one⟩

/-- The positive remainder giving the lower complementary-product bound. -/
lemma lower_product_identity {A : ReciprocalExpr} {a x : ℝ}
    (ha : 0 < a) (hA : A.PolesAbove 0) (hz : A.eval 0 = 1) (hx : 0 ≤ x) :
    1-a/(a+x)*A.eval x = x/(a+x)+x*(scale a (pole a (A.difference 0))).eval x := by
  have hd := difference_identity hA (by norm_num : -(0:ℝ) ≤ 0) (by simpa using hx)
  rw [hz] at hd
  simp only [eval]
  have hd' : A.eval x = 1-x*(A.difference 0).eval x := by simpa only [sub_zero] using (eq_sub_iff_add_eq.mpr (by linarith [hd]))
  rw [hd']
  field_simp [ne_of_gt (add_pos_of_pos_of_nonneg ha hx)]
  ; ring

/-- The upper comparison is the double positive divided difference at -a,0. -/
lemma upper_product_identity {A : ReciprocalExpr} {a x : ℝ}
    (ha : 0 < a) (hA : A.PolesAbove a) (hz : A.eval 0 = 1) (hx : 0 ≤ x) :
    A.eval (-a)*(x/(a+x))-(1-a/(a+x)*A.eval x) =
      x*(scale a ((A.difference (-a)).difference 0)).eval x := by
  have h0 : -a ≤ (0:ℝ) := by linarith
  have hax : -a ≤ x := by linarith
  have hd0 := difference_identity hA (le_refl (-a)) h0
  have hdx := difference_identity hA (le_refl (-a)) hax
  have hdd := difference_identity (difference_poles (-a) hA) h0 hax
  rw [hz] at hd0
  simp only [zero_sub,sub_zero] at hd0 hdd
  simp only [sub_neg_eq_add] at hdx
  simp only [eval]
  have hn : a+x ≠ 0 := ne_of_gt (by linarith)
  field_simp [hn]
  linear_combination (x+a)*hd0-a*hdx+a*(a+x)*hdd

lemma complementary_identity {A : ReciprocalExpr} {x : ℝ}
    (hA : A.PolesAbove 0) (hz : A.eval 0 = 1) (hx : 0 ≤ x) :
    1-A.eval x = x*(A.difference 0).eval x := by
  have h := difference_identity hA (by norm_num : -(0:ℝ) ≤ 0) (by simpa using hx)
  simpa [hz] using h

end ReciprocalExpr

lemma sparseEval_congr_nodes {n : ℕ} (v : ℕ → ℝ) (e : Fin n → ℕ) {f g : ℝ → ℝ}
    (h : ∀ j : Fin (n+1),f (v j)=g (v j)) : sparseEval v e f=sparseEval v e g := by
  unfold sparseEval
  apply sum_congr rfl
  intro j hj
  rw [h j]

lemma sparse_complement_nonneg {n : ℕ} {A : ReciprocalExpr}
    (v : ℕ → ℝ) (e : Fin n → ℕ) (hv : ∀ i,0 < v i)
    (hord : StrictMono (fun i : Fin (n+1) => v i)) (he : StrictMono e)
    (hA : A.PolesAbove 0) (hp : A.CoeffNonneg) (hz : A.eval 0=1) :
    0 ≤ sparseEval v e (fun x => 1-A.eval x) := by
  rw [sparseEval_congr_nodes v e (g:=fun x => x*(A.difference 0).eval x)
    (fun j => ReciprocalExpr.complementary_identity hA hz (hv j).le)]
  exact sparseEval_rational_nonneg v e hv hord he (L:=0) (by intro i;simpa using (hv i).le)
    (ReciprocalExpr.difference_poles 0 hA)
    (ReciprocalExpr.difference_coeff_nonneg hA hp (by norm_num))


lemma sparse_product_lower {n : ℕ} {A : ReciprocalExpr}
    (v : ℕ → ℝ) (e : Fin n → ℕ) (hv : ∀ i,0 < v i)
    (hord : StrictMono (fun i : Fin (n+1) => v i)) (he : StrictMono e)
    {a : ℝ} (ha : 0 < a) (hA : A.PolesAbove 0) (hp : A.CoeffNonneg) (hz : A.eval 0=1) :
    poleProduct v a (n+1) ≤ sparseEval v e (fun x => 1-a/(a+x)*A.eval x) := by
  rw [sparseEval_congr_nodes v e
    (g:=fun x => x/(a+x)+x*(ReciprocalExpr.scale a (ReciprocalExpr.pole a (A.difference 0))).eval x)
    (fun j => ReciprocalExpr.lower_product_identity ha hA hz (hv j).le),sparseEval_add]
  apply le_add_of_le_of_nonneg (sparseEval_reciprocal_lower v e hv hord he ha)
  apply sparseEval_rational_nonneg v e hv hord he (L:=0) (by intro i;simpa using (hv i).le)
  · exact ⟨ha,ReciprocalExpr.difference_poles 0 hA⟩
  · exact ⟨ha.le,ReciprocalExpr.difference_coeff_nonneg hA hp (by norm_num)⟩

/-- Exact sparse prefix-node upper product. The harmless constant is the
remaining normalized product evaluated at its slowest pole. -/
lemma sparse_product_upper {n q : ℕ} {A : ReciprocalExpr}
    (v : ℕ → ℝ) (e : Fin n → ℕ) (hv : ∀ i,0 < v i)
    (hord : StrictMono (fun i : Fin (n+1) => v i)) (he : StrictMono e)
    (hq : ∀ m,1 ≤ m → m ≤ q → ∃ i,e i+1=m)
    {a : ℝ} (ha : 0 < a) (hA : A.PolesAbove a) (hp : A.CoeffNonneg) (hz : A.eval 0=1) :
    sparseEval v e (fun x => 1-a/(a+x)*A.eval x) ≤ A.eval (-a)*poleProduct v a (q+1) := by
  have hc : 0 ≤ sparseEval v e
      (fun x => x*(ReciprocalExpr.scale a ((A.difference (-a)).difference 0)).eval x) := by
    apply sparseEval_rational_nonneg v e hv hord he (L:=a) (by intro i;linarith [hv i])
    · exact ReciprocalExpr.difference_poles 0 (ReciprocalExpr.difference_poles (-a) hA)
    · exact ⟨ha.le,ReciprocalExpr.difference_coeff_nonneg
        (ReciprocalExpr.difference_poles (-a) hA)
        (ReciprocalExpr.difference_coeff_nonneg hA hp le_rfl) (by linarith)⟩
  have hi := sparseEval_congr_nodes v e
    (f:=fun x => A.eval (-a)*(x/(a+x))-(1-a/(a+x)*A.eval x))
    (g:=fun x => x*(ReciprocalExpr.scale a ((A.difference (-a)).difference 0)).eval x)
    (fun j => ReciprocalExpr.upper_product_identity ha hA hz (hv j).le)
  have hs : sparseEval v e (fun x => A.eval (-a)*(x/(a+x))-(1-a/(a+x)*A.eval x)) =
      A.eval (-a)*sparseEval v e (fun x => x/(a+x))-sparseEval v e (fun x => 1-a/(a+x)*A.eval x) := by
    simp only [sparseEval,mul_sub,sum_sub_distrib,mul_sum]
    congr 1
    apply sum_congr rfl
    intro j hj
    ring
  rw [←hi,hs] at hc
  exact (le_of_sub_nonneg hc).trans (mul_le_mul_of_nonneg_left
    (sparseEval_reciprocal_upper v e hv hord he hq ha)
    (ReciprocalExpr.eval_nonneg hA hp le_rfl))


lemma sparse_complement_upper {n q : ℕ} {A : ReciprocalExpr}
    (v : ℕ → ℝ) (e : Fin n → ℕ) (hv : ∀ i,0 < v i)
    (hord : StrictMono (fun i : Fin (n+1) => v i)) (he : StrictMono e)
    (hq : ∀ m,1 ≤ m → m ≤ q → ∃ i,e i+1=m)
    {a : ℝ} (ha : 0 < a) (hA : A.PolesAbove a) (hp : A.CoeffNonneg) (hz : A.eval 0=1) :
    sparseEval v e (fun x => 1-A.eval x) ≤ A.eval (-a)*poleProduct v a (q+1) := by
  have hab : (ReciprocalExpr.pole a A).PolesAbove 0 :=
    ⟨ha,ReciprocalExpr.poles_mono ha.le hA⟩
  have hpos := sparseEval_rational_nonneg v e hv hord he
    (L:=0) (by intro i;simpa using (hv i).le) hab hp
  have hf := sparseEval_congr_nodes v e
    (f:=fun x => 1-a/(a+x)*A.eval x)
    (g:=fun x => (1-A.eval x)+x*(ReciprocalExpr.pole a A).eval x)
    (by intro j;simp only [ReciprocalExpr.eval];field_simp [ne_of_gt (add_pos ha (hv j))];ring)
  rw [sparseEval_add] at hf
  apply (le_add_of_nonneg_right hpos).trans
  rw [←hf]
  exact sparse_product_upper v e hv hord he hq ha hA hp hz

lemma sparse_mixture_bounds {n q : ℕ} {A B : ReciprocalExpr}
    (v : ℕ → ℝ) (e : Fin n → ℕ) (hv : ∀ i,0 < v i)
    (hord : StrictMono (fun i : Fin (n+1) => v i)) (he : StrictMono e)
    (hq : ∀ m,1 ≤ m → m ≤ q → ∃ i,e i+1=m)
    {a p C : ℝ} (ha : 0 < a) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hA : A.PolesAbove a) (hAp : A.CoeffNonneg) (hAz : A.eval 0=1)
    (hB : B.PolesAbove a) (hBp : B.CoeffNonneg) (hBz : B.eval 0=1)
    (hAC : A.eval (-a) ≤ C) (hBC : B.eval (-a) ≤ C) :
    p*poleProduct v a (n+1) ≤
      sparseEval v e (fun x => 1-(p*(a/(a+x)*A.eval x)+(1-p)*B.eval x)) ∧
    sparseEval v e (fun x => 1-(p*(a/(a+x)*A.eval x)+(1-p)*B.eval x)) ≤
      C*poleProduct v a (q+1) := by
  have heq : (fun x => 1-(p*(a/(a+x)*A.eval x)+(1-p)*B.eval x)) =
      (fun x => p*(1-a/(a+x)*A.eval x)+(1-p)*(1-B.eval x)) := by funext x;ring
  rw [heq,sparseEval_add,sparseEval_scale,sparseEval_scale]
  have hA0:=ReciprocalExpr.poles_mono ha.le hA
  have hB0:=ReciprocalExpr.poles_mono ha.le hB
  constructor
  · apply le_add_of_le_of_nonneg
      (mul_le_mul_of_nonneg_left (sparse_product_lower v e hv hord he ha hA0 hAp hAz) hp0)
    exact mul_nonneg (sub_nonneg.mpr hp1) (sparse_complement_nonneg v e hv hord he hB0 hBp hBz)
  · have huu:=add_le_add
      (mul_le_mul_of_nonneg_left (sparse_product_upper v e hv hord he hq ha hA hAp hAz) hp0)
      (mul_le_mul_of_nonneg_left (sparse_complement_upper v e hv hord he hq ha hB hBp hBz) (sub_nonneg.mpr hp1))
    apply huu.trans
    have hac:=mul_le_mul_of_nonneg_left hAC hp0
    have hbc:=mul_le_mul_of_nonneg_left hBC (sub_nonneg.mpr hp1)
    nlinarith [(poleProduct_pos v hv ha (q+1)),
      mul_le_mul_of_nonneg_right (add_le_add hac hbc) (poleProduct_pos v hv ha (q+1)).le]

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI
