import OAI.Combinatorics.ContingencyTables.Transport.IntegerPropagation
import OAI.Combinatorics.ContingencyTables.Transport.RationalProducts

namespace OAI

/-! # Integer counts for the finite stages of law tabulation -/

namespace ContingencyTables
open scoped BigOperators

/-- Counts of equally likely slots. The denominator is explicit so that
composition can reserve ignored bits without enumerating them. -/
structure IntegerLaw (A : Type*) [Fintype A] (Q : ℕ) where
  count : A → ℕ
  total : ∑ a,count a=Q

namespace IntegerLaw
open ResidualMixture FirstSuccess
open scoped Classical
noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B] {Q P : ℕ}

def toRational (p : IntegerLaw A Q) (hQ : 0<Q) : RationalLaw A where
  mass a := (p.count a:ℚ)/Q
  nonnegative _ := by positivity
  total := by
    rw [←Finset.sum_div,←Nat.cast_sum,p.total]
    exact div_self (by exact_mod_cast hQ.ne')

def ofMass (p : RationalLaw A) (w : A → ℕ) (hQ : 0<Q)
    (hw : ∀ a,(w a:ℚ)/Q=p.mass a) : IntegerLaw A Q where
  count := w
  total := by
    have ht : ((∑ a,w a:ℕ):ℚ)/Q=1 := by
      rw [Nat.cast_sum,Finset.sum_div]
      simp_rw [hw]
      exact p.total
    have hQt : (Q:ℚ)≠0 := by exact_mod_cast hQ.ne'
    exact_mod_cast (div_eq_one_iff_eq hQt).mp ht

lemma toRational_ofMass (p : RationalLaw A) (w : A → ℕ) (hQ : 0<Q)
    (hw : ∀ a,(w a:ℚ)/Q=p.mass a) :
    (ofMass p w hQ hw).toRational hQ=p := by
  apply RationalLaw.ext
  exact funext hw

def rebase (p : IntegerLaw A Q) (h : Q=P) : IntegerLaw A P :=
  ⟨p.count,p.total.trans h⟩

lemma toRational_rebase (p : IntegerLaw A Q) (h : Q=P) (hQ : 0<Q) (hP : 0<P) :
    (p.rebase h).toRational hP=p.toRational hQ := by subst P; rfl

def scale (p : IntegerLaw A Q) (P : ℕ) : IntegerLaw A (Q*P) where
  count a := p.count a*P
  total := by rw [←Finset.sum_mul,p.total]

theorem toRational_scale (p : IntegerLaw A Q) (hQ : 0<Q) (P : ℕ) (hP : 0<P) :
    (p.scale P).toRational (Nat.mul_pos hQ hP)=p.toRational hQ := by
  apply RationalLaw.ext
  funext a
  change ((p.count a*P:ℕ):ℚ)/((Q*P:ℕ):ℚ)=(p.count a:ℚ)/Q
  push_cast
  exact mul_div_mul_right _ _ (by exact_mod_cast hP.ne' : (P:ℚ)≠0)

def pi {n : ℕ} {A : Fin n → Type*} [∀ i,Fintype (A i)] {Q : Fin n → ℕ}
    (p : ∀ i,IntegerLaw (A i) (Q i)) : IntegerLaw (∀ i,A i) (∏ i,Q i) where
  count x := ∏ i,(p i).count (x i)
  total := by rw [←Fintype.prod_sum]; simp_rw [(p _).total]

theorem toRational_pi {n : ℕ} {A : Fin n → Type*} [∀ i,Fintype (A i)] {Q : Fin n → ℕ}
    (p : ∀ i,IntegerLaw (A i) (Q i)) (hQ : ∀ i,0<Q i) :
    (pi p).toRational (Finset.prod_pos (fun i _ => hQ i))=
      piLaw (fun i => (p i).toRational (hQ i)) := by
  apply RationalLaw.ext
  funext x
  change ((∏ i,(p i).count (x i):ℕ):ℚ)/(∏ i,Q i)=∏ i,((p i).count (x i):ℚ)/Q i
  rw [Nat.cast_prod,Finset.prod_div_distrib,Nat.cast_prod]

def point [DecidableEq A] (Q : ℕ) (a : A) : IntegerLaw A Q where
  count b := if b=a then Q else 0
  total := by simp

def push [DecidableEq B] (p : IntegerLaw A Q) (f : A → B) : IntegerLaw B Q where
  count b := ∑ a,if f a=b then p.count a else 0
  total := by
    rw [Finset.sum_comm]
    simpa using p.total

def bind (p : IntegerLaw A Q) (K : A → IntegerLaw B P) : IntegerLaw B (Q*P) where
  count b := ∑ a,p.count a*(K a).count b
  total := by
    rw [Finset.sum_comm]
    simp only [←Finset.mul_sum,(K _).total,←Finset.sum_mul,p.total]

def product (p : IntegerLaw A Q) (q : IntegerLaw B P) : IntegerLaw (A×B) (Q*P) where
  count x := p.count x.1*q.count x.2
  total := by
    rw [Fintype.sum_prod_type]
    simp only [←Finset.mul_sum,q.total,←Finset.sum_mul,p.total]

theorem toRational_product (p : IntegerLaw A Q) (q : IntegerLaw B P)
    (hQ : 0<Q) (hP : 0<P) :
    (p.product q).toRational (Nat.mul_pos hQ hP)=
      productLaw (p.toRational hQ) (q.toRational hP) := by
  apply RationalLaw.ext
  funext x
  change ((p.count x.1*q.count x.2:ℕ):ℚ)/((Q*P:ℕ):ℚ)=
    (p.count x.1:ℚ)/Q*((q.count x.2:ℚ)/P)
  push_cast
  exact (div_mul_div_comm (p.count x.1:ℚ) Q (q.count x.2) P).symm

theorem toRational_push [DecidableEq B] (p : IntegerLaw A Q) (hQ : 0<Q) (f : A → B) :
    (p.push f).toRational hQ=mapLaw (p.toRational hQ) f := by
  apply RationalLaw.ext
  funext b
  change ((∑ a,if f a=b then p.count a else 0:ℕ):ℚ)/Q=
    ∑ a,if f a=b then (p.count a:ℚ)/Q else 0
  rw [Nat.cast_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

theorem toRational_bind (p : IntegerLaw A Q) (K : A → IntegerLaw B P)
    (hQ : 0<Q) (hP : 0<P) :
    (p.bind K).toRational (Nat.mul_pos hQ hP)=
      bindLaw (p.toRational hQ) (fun a => (K a).toRational hP) := by
  apply RationalLaw.ext
  funext b
  change ((∑ a,p.count a*(K a).count b:ℕ):ℚ)/((Q*P:ℕ):ℚ)=
    ∑ a,((p.count a:ℚ)/Q)*(((K a).count b:ℚ)/P)
  rw [Nat.cast_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  push_cast
  exact (div_mul_div_comm (p.count a:ℚ) Q ((K a).count b) P).symm

theorem toRational_point [DecidableEq A] (Q : ℕ) (hQ : 0<Q) (a : A) :
    (point Q a).toRational hQ=pointLaw a := by
  apply RationalLaw.ext
  funext b
  change ((if b=a then Q else 0:ℕ):ℚ)/Q=if b=a then 1 else 0
  split_ifs
  · exact div_self (by exact_mod_cast hQ.ne')
  · simp

variable [DecidableEq A]

def retryCount (p : IntegerLaw (Option A) Q) (fallback : A) : ℕ → A → ℕ
  | 0,a => if a=fallback then 1 else 0
  | N+1,a => p.count (some a)*Q^N+p.count none*retryCount p fallback N a

lemma retryCount_total (p : IntegerLaw (Option A) Q) (fallback : A) (N : ℕ) :
    ∑ a,retryCount p fallback N a=Q^N := by
  induction N with
  | zero => simp [retryCount]
  | succ N ih =>
    have ht:=p.total
    rw [Fintype.sum_option] at ht
    simp only [retryCount,Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum,ih]
    rw [←add_mul,add_comm,ht,pow_succ']

def retry (p : IntegerLaw (Option A) Q) (fallback : A) (N : ℕ) : IntegerLaw A (Q^N) :=
  ⟨retryCount p fallback N,retryCount_total p fallback N⟩

/-- First-success sums are evaluated in integers with a reserved common
denominator. No division by the acceptance probability occurs. -/
theorem toRational_retry (p : IntegerLaw (Option A) Q) (hQ : 0<Q)
    (fallback : A) (N : ℕ) :
    (p.retry fallback N).toRational (pow_pos hQ N)=
      retryLaw (p.toRational hQ) id fallback N := by
  apply RationalLaw.ext
  funext a
  induction N with
  | zero => simp [retry,toRational,retryCount,retryLaw,pointLaw]
  | succ N ih =>
    rw [retryLaw,retryStep_mass]
    simp only [successMass,failureMass,id_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    simp only [retry,toRational,retryCount,Nat.cast_add,Nat.cast_mul,Nat.cast_pow] at ih ⊢
    rw [←ih]
    rw [pow_succ]
    field_simp [show (Q:ℚ)≠0 by exact_mod_cast hQ.ne']

end
end IntegerLaw
end ContingencyTables

end OAI
