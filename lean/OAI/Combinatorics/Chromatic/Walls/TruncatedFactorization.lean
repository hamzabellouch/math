import Mathlib
import OAI.Combinatorics.Chromatic.Walls.PowerSeriesThreeFactors

namespace OAI

section
namespace ElementaryPositivity.PowerSeriesSplit
open PowerSeries
noncomputable section
variable {R : Type*} [Ring R]

lemma pair_truncated_unique (P : R→+R) (f a b : PowerSeries R) (N : ℕ)
    (ha : constantCoeff a=1) (hb : constantCoeff b=1)
    (hab : ∀n≤N,coeff n (a*b)=coeff n f)
    (hleft : ∀n,n+1≤N→P (coeff (n+1) a)=coeff (n+1) a)
    (hright : ∀n,n+1≤N→P (coeff (n+1) b)=0) :
    ∀n≤N,coeff n a=coeff n (leftFactor P f) ∧ coeff n b=coeff n (rightFactor P f) := by
  have h : ∀n≤N,(coeff n a,coeff n b)=pairCoefficients P f n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih=>
      intro hn
      cases n with
      | zero=>simp only [coeff_zero_eq_constantCoeff_apply,ha,hb,pairCoefficients]
      | succ n=>
        have hs : (∑i : Fin n,coeff (i.val+1) a*coeff (n-i.val) b)=
            ∑i : Fin n,(pairCoefficients P f (i.val+1)).1*(pairCoefficients P f (n-i.val)).2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [←ih (i.val+1) (by omega) (by omega),←ih (n-i.val) (by omega) (by omega)]
        have hc:=coeff_mul_succ a b n ha hb
        rw [hab (n+1) hn,hs] at hc
        have hr : coeff (n+1) f-∑i : Fin n,
            (pairCoefficients P f (i.val+1)).1*(pairCoefficients P f (n-i.val)).2=
            coeff (n+1) a+coeff (n+1) b :=by rw [hc]; abel
        rw [pairCoefficients,hr]
        simp only [map_add,hleft n hn,hright n hn,add_zero]
        congr 1
        abel
  intro n hn
  constructor
  · simpa only [leftFactor,coeff_mk] using congrArg Prod.fst (h n hn)
  · simpa only [rightFactor,coeff_mk] using congrArg Prod.snd (h n hn)

lemma mul_mem_through (S : Subring R) (a b : PowerSeries R) (N : ℕ)
    (ha : ∀n≤N,coeff n a∈S) (hb : ∀n≤N,coeff n b∈S) :
    ∀n≤N,coeff n (a*b)∈S :=by
  intro n hn
  rw [coeff_mul]
  apply S.sum_mem
  intro p hp
  have hh:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  exact S.mul_mem (ha p.1 (by omega)) (hb p.2 (by omega))

lemma three_truncated_unique (P Q : R→+R) (S : Subring R) (hS : ∀x,x∈S↔P x=0)
    (f a b c : PowerSeries R) (N : ℕ)
    (ha : constantCoeff a=1) (hb : constantCoeff b=1) (hc : constantCoeff c=1)
    (habc : ∀n≤N,coeff n (a*b*c)=coeff n f)
    (haP : ∀n,n+1≤N→P (coeff (n+1) a)=coeff (n+1) a)
    (hbP : ∀n≤N,P (coeff n b)=0) (hcP : ∀n≤N,P (coeff n c)=0)
    (hbQ : ∀n,n+1≤N→Q (coeff (n+1) b)=coeff (n+1) b)
    (hcQ : ∀n,n+1≤N→Q (coeff (n+1) c)=0) :
    ∀n≤N,coeff n a=coeff n (positiveFactor P f) ∧
      coeff n b=coeff n (zeroFactor P Q f) ∧ coeff n c=coeff n (negativeFactor P Q f) :=by
  have hbc : ∀n≤N,P (coeff n (b*c))=0:=fun n hn=>(hS _).mp
    (mul_mem_through S b c N (fun k hk=>(hS _).mpr (hbP k hk))
      (fun k hk=>(hS _).mpr (hcP k hk)) n hn)
  have H:=pair_truncated_unique P f a (b*c) N ha (by simp [hb,hc])
    (fun n hn=>by simpa only [mul_assoc] using habc n hn) haP (fun n hn=>hbc (n+1) hn)
  have H0:=pair_truncated_unique Q (rightFactor P f) b c N hb hc
    (fun n hn=>(H n hn).2) hbQ hcQ
  exact fun n hn=>⟨(H n hn).1,(H0 n hn).1,(H0 n hn).2⟩
end
end ElementaryPositivity.PowerSeriesSplit

end

end OAI
