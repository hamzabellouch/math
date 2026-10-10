import Mathlib

namespace OAI

section
section
namespace ElementaryPositivity.PowerSeriesSplit
open PowerSeries
noncomputable section
variable {R : Type*} [Ring R]

def pairCoefficients (P : R →+ R) (f : PowerSeries R) : ℕ → R × R
  | 0 => (1,1)
  | n+1 =>
    let r:=coeff (n+1) f - ∑i : Fin n,
      (pairCoefficients P f (i.val+1)).1 * (pairCoefficients P f (n-i.val)).2
    (P r,r-P r)
termination_by n=>n
decreasing_by all_goals omega

def leftFactor (P : R →+ R) (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk (fun n=>(pairCoefficients P f n).1)
def rightFactor (P : R →+ R) (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk (fun n=>(pairCoefficients P f n).2)

@[simp] lemma left_constant (P : R →+ R) (f : PowerSeries R) :
    constantCoeff (leftFactor P f)=1 := by
  rw [←coeff_zero_eq_constantCoeff_apply]
  simp only [leftFactor,coeff_mk,pairCoefficients]
@[simp] lemma right_constant (P : R →+ R) (f : PowerSeries R) :
    constantCoeff (rightFactor P f)=1 := by
  rw [←coeff_zero_eq_constantCoeff_apply]
  simp only [rightFactor,coeff_mk,pairCoefficients]

lemma coeff_mul_succ (f g : PowerSeries R) (n : ℕ)
    (hf : constantCoeff f=1) (hg : constantCoeff g=1) :
    coeff (n+1) (f*g)=coeff (n+1) f+coeff (n+1) g+
      ∑i : Fin n,coeff (i.val+1) f * coeff (n-i.val) g := by
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_range_succ,Finset.sum_range_succ']
  simp only [Nat.sub_self,coeff_zero_eq_constantCoeff_apply,hf,hg,mul_one,one_mul,Nat.sub_zero]
  rw [Fin.sum_univ_eq_sum_range (fun i=>coeff (i+1) f*coeff (n-i) g) n]
  simp only [Nat.add_sub_add_right]
  abel

lemma factorization (P : R →+ R) (f : PowerSeries R) (hf : constantCoeff f=1) :
    leftFactor P f * rightFactor P f=f := by
  ext n
  cases n with
  | zero => simp only [coeff_zero_eq_constantCoeff_apply,map_mul,left_constant,right_constant,one_mul,hf]
  | succ n =>
    rw [coeff_mul_succ _ _ n (left_constant P f) (right_constant P f)]
    simp only [leftFactor,rightFactor,coeff_mk]
    rw [pairCoefficients]
    dsimp only
    abel

lemma left_fixed (P : R →+ R) (hP : ∀r,P (P r)=P r) (f : PowerSeries R) (n : ℕ) :
    P (coeff (n+1) (leftFactor P f))=coeff (n+1) (leftFactor P f) := by
  simp only [leftFactor,coeff_mk]
  rw [pairCoefficients]
  exact hP _
lemma right_killed (P : R →+ R) (hP : ∀r,P (P r)=P r) (f : PowerSeries R) (n : ℕ) :
    P (coeff (n+1) (rightFactor P f))=0 := by
  simp only [rightFactor,coeff_mk]
  rw [pairCoefficients]
  simp only [map_sub,hP,sub_self]

lemma uniqueness (P : R →+ R) (f a b : PowerSeries R)
    (ha : constantCoeff a=1) (hb : constantCoeff b=1)
    (hab : a*b=f)
    (hleft : ∀n,P (coeff (n+1) a)=coeff (n+1) a)
    (hright : ∀n,P (coeff (n+1) b)=0) :
    a=leftFactor P f ∧ b=rightFactor P f := by
  have h : ∀n,(coeff n a,coeff n b)=pairCoefficients P f n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => simp only [coeff_zero_eq_constantCoeff_apply,ha,hb,pairCoefficients]
      | succ n =>
        have hsum : (∑i : Fin n, coeff (i.val+1) a * coeff (n-i.val) b)=
            ∑i : Fin n,(pairCoefficients P f (i.val+1)).1 *
              (pairCoefficients P f (n-i.val)).2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [←ih (i.val+1) (by omega),←ih (n-i.val) (by omega)]
        have hcoeff := coeff_mul_succ a b n ha hb
        rw [hab,hsum] at hcoeff
        have hres : coeff (n+1) f-∑i : Fin n,
            (pairCoefficients P f (i.val+1)).1 * (pairCoefficients P f (n-i.val)).2 =
            coeff (n+1) a+coeff (n+1) b := by rw [hcoeff]; abel
        rw [pairCoefficients,hres]
        simp only [map_add,hleft,hright,add_zero]
        congr 1
        abel
  constructor
  · ext n
    simpa only [leftFactor,coeff_mk] using congrArg Prod.fst (h n)
  · ext n
    simpa only [rightFactor,coeff_mk] using congrArg Prod.snd (h n)

lemma factors_mem (P : R →+ R) (S : Subring R)
    (hP : ∀r∈S,P r∈S) (f : PowerSeries R) (hf : ∀n,coeff n f∈S) :
    (∀n,coeff n (leftFactor P f)∈S) ∧ (∀n,coeff n (rightFactor P f)∈S) := by
  have h : ∀n,(pairCoefficients P f n).1∈S ∧ (pairCoefficients P f n).2∈S := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => simpa only [pairCoefficients] using And.intro S.one_mem S.one_mem
      | succ n =>
        have hc : coeff (n+1) f-∑i : Fin n,
            (pairCoefficients P f (i.val+1)).1*(pairCoefficients P f (n-i.val)).2∈S := by
          apply S.sub_mem (hf (n+1))
          apply S.sum_mem
          intro i hi
          exact S.mul_mem (ih (i.val+1) (by omega)).1 (ih (n-i.val) (by omega)).2
        rw [pairCoefficients]
        exact ⟨hP _ hc,S.sub_mem hc (hP _ hc)⟩
  constructor
  · intro n
    simpa only [leftFactor,coeff_mk] using (h n).1
  · intro n
    simpa only [rightFactor,coeff_mk] using (h n).2

lemma mul_mem (S : Subring R) (a b : PowerSeries R)
    (ha : ∀n,coeff n a∈S) (hb : ∀n,coeff n b∈S) : ∀n,coeff n (a*b)∈S := by
  intro n
  rw [coeff_mul]
  exact S.sum_mem (fun p hp=>S.mul_mem (ha p.1) (hb p.2))

lemma factors_graded (P : R →+ R) (A : ℕ → AddSubgroup R)
    (h0 : (1:R)∈A 0)
    (hmul : ∀m n x y,x∈A m → y∈A n → x*y∈A (m+n))
    (hP : ∀n x,x∈A n → P x∈A n)
    (f : PowerSeries R) (hf : ∀n,coeff n f∈A n) :
    (∀n,coeff n (leftFactor P f)∈A n) ∧
    (∀n,coeff n (rightFactor P f)∈A n) := by
  have h : ∀n,(pairCoefficients P f n).1∈A n ∧ (pairCoefficients P f n).2∈A n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => simpa only [pairCoefficients] using And.intro h0 h0
      | succ n =>
        have hc : coeff (n+1) f-∑i : Fin n,
            (pairCoefficients P f (i.val+1)).1*(pairCoefficients P f (n-i.val)).2∈A (n+1) := by
          apply (A (n+1)).sub_mem (hf (n+1))
          apply (A (n+1)).sum_mem
          intro i hi
          have hmn : (i.val+1)+(n-i.val)=n+1 := by omega
          rw [←hmn]
          exact hmul _ _ _ _ (ih (i.val+1) (by omega)).1 (ih (n-i.val) (by omega)).2
        rw [pairCoefficients]
        exact ⟨hP _ _ hc,(A _).sub_mem hc (hP _ _ hc)⟩
  constructor
  · intro n
    simpa only [leftFactor,coeff_mk] using (h n).1
  · intro n
    simpa only [rightFactor,coeff_mk] using (h n).2

end
end ElementaryPositivity.PowerSeriesSplit
end
end

end OAI
