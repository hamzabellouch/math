import Mathlib
import OAI.Combinatorics.Chromatic.Walls.PowerSeriesThreeFactors

namespace OAI

section
section
namespace ElementaryPositivity.PowerSeriesSplit
open PowerSeries
noncomputable section
variable {R : Type*} [Ring R]

lemma pair_congr (P : R →+ R) (f g : PowerSeries R) (n : ℕ)
    (h : ∀k≤n,coeff k f=coeff k g) : pairCoefficients P f n=pairCoefficients P g n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => rw [pairCoefficients,pairCoefficients]
    | succ n =>
      have hs : (∑i : Fin n,(pairCoefficients P f (i.val+1)).1*(pairCoefficients P f (n-i.val)).2)=
          ∑i : Fin n,(pairCoefficients P g (i.val+1)).1*(pairCoefficients P g (n-i.val)).2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [ih (i.val+1) (by omega) (fun k hk=>h k (by omega)),
          ih (n-i.val) (by omega) (fun k hk=>h k (by omega))]
      rw [pairCoefficients,pairCoefficients,h (n+1) le_rfl,hs]

lemma left_coeff_congr (P : R →+ R) (f g : PowerSeries R) (n : ℕ)
    (h : ∀k≤n,coeff k f=coeff k g) : coeff n (leftFactor P f)=coeff n (leftFactor P g) := by
  simpa only [leftFactor,coeff_mk] using congrArg Prod.fst (pair_congr P f g n h)
lemma right_coeff_congr (P : R →+ R) (f g : PowerSeries R) (n : ℕ)
    (h : ∀k≤n,coeff k f=coeff k g) : coeff n (rightFactor P f)=coeff n (rightFactor P g) := by
  simpa only [rightFactor,coeff_mk] using congrArg Prod.snd (pair_congr P f g n h)

lemma leading_difference (P : R →+ R) (f g : PowerSeries R) (n : ℕ)
    (h : ∀k≤n,coeff k f=coeff k g) :
    coeff (n+1) (leftFactor P f)-coeff (n+1) (leftFactor P g)=P (coeff (n+1) f-coeff (n+1) g) ∧
    coeff (n+1) (rightFactor P f)-coeff (n+1) (rightFactor P g)=
      (coeff (n+1) f-coeff (n+1) g)-P (coeff (n+1) f-coeff (n+1) g) := by
  have hs : (∑i : Fin n,(pairCoefficients P f (i.val+1)).1*(pairCoefficients P f (n-i.val)).2)=
      ∑i : Fin n,(pairCoefficients P g (i.val+1)).1*(pairCoefficients P g (n-i.val)).2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [pair_congr P f g (i.val+1) (fun k hk=>h k (by omega)),
      pair_congr P f g (n-i.val) (fun k hk=>h k (by omega))]
  simp only [leftFactor,rightFactor,coeff_mk]
  rw [pairCoefficients,pairCoefficients,hs]
  simp only [map_sub]
  constructor <;> abel

lemma zero_leading_difference (P Q : R →+ R) (hQP : ∀x,Q (P x)=0)
    (f g : PowerSeries R) (n : ℕ) (h : ∀k≤n,coeff k f=coeff k g) :
    coeff (n+1) (zeroFactor P Q f)-coeff (n+1) (zeroFactor P Q g)=
      Q (coeff (n+1) f-coeff (n+1) g) := by
  have hr : ∀k≤n,coeff k (rightFactor P f)=coeff k (rightFactor P g) := by
    intro k hk
    exact right_coeff_congr P f g k (fun j hj=>h j (hj.trans hk))
  have hl:= (leading_difference Q (rightFactor P f) (rightFactor P g) n hr).1
  rw [(leading_difference P f g n h).2,map_sub,hQP,sub_zero] at hl
  exact hl

lemma zero_coeff_congr (P Q : R →+ R) (f g : PowerSeries R) (n : ℕ)
    (h : ∀k≤n,coeff k f=coeff k g) : coeff n (zeroFactor P Q f)=coeff n (zeroFactor P Q g) := by
  apply left_coeff_congr Q _ _ n
  intro k hk
  exact right_coeff_congr P f g k (fun j hj=>h j (hj.trans hk))
end
end ElementaryPositivity.PowerSeriesSplit
end
section
namespace ElementaryPositivity.FormalLog
open PowerSeries
noncomputable section
variable {R : Type*} [Ring R]

lemma mul_coeff_congr (a b c d : PowerSeries R) (n : ℕ)
    (ha : ∀j≤n,coeff j a=coeff j c) (hb : ∀j≤n,coeff j b=coeff j d) :
    coeff n (a*b)=coeff n (c*d) := by
  rw [coeff_mul,coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hh:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [ha _ (by omega),hb _ (by omega)]

lemma pow_coeff_congr (a b : PowerSeries R) (n k : ℕ)
    (h : ∀j≤n,coeff j a=coeff j b) : coeff n (a^k)=coeff n (b^k) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ a k,pow_succ b k]
    apply mul_coeff_congr
    · intro j hj
      exact ih j (fun i hi=>h i (hi.trans hj))
    · exact h

lemma pow_coeff_congr_of_two_le (a b : PowerSeries R) (n k : ℕ)
    (ha : constantCoeff a=0) (hb : constantCoeff b=0) (hk : 2≤k)
    (h : ∀j<n,coeff j a=coeff j b) : coeff n (a^k)=coeff n (b^k) := by
  obtain ⟨j,rfl⟩:=Nat.exists_eq_add_of_le hk
  rw [show 2+j=(j+1)+1 by omega,pow_succ a (j+1),pow_succ b (j+1)]
  rw [coeff_mul,coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hh:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  by_cases h0 : p.1=0
  · simp only [h0,coeff_zero_eq_constantCoeff_apply,map_pow,ha,hb,zero_pow (by omega : j+1≠0),zero_mul]
  by_cases h1 : p.2=0
  · simp only [h1,coeff_zero_eq_constantCoeff_apply,ha,hb,mul_zero]
  have hn1 : p.1<n := by omega
  have hn2 : p.2<n := by omega
  rw [pow_coeff_congr a b p.1 (j+1) (fun i hi=>h i (hi.trans_lt hn1)),h _ hn2]

variable [Module ℚ R]

def log (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk (fun n=>∑k∈Finset.range n, ((-1:ℚ)^k/(k+1:ℕ)) • coeff n ((f-1)^(k+1)))

@[simp] lemma log_constant (f : PowerSeries R) : constantCoeff (log f)=0 := by
  rw [←coeff_zero_eq_constantCoeff_apply]
  simp only [log,coeff_mk,Finset.range_zero,Finset.sum_empty]

lemma log_coeff_congr (f g : PowerSeries R) (n : ℕ)
    (h : ∀j≤n,coeff j f=coeff j g) : coeff n (log f)=coeff n (log g) := by
  simp only [log,coeff_mk]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  apply pow_coeff_congr
  intro j hj
  rw [map_sub,map_sub,h j hj]

lemma log_coeff_succ (f : PowerSeries R) (n : ℕ) :
    coeff (n+1) (log f)=coeff (n+1) f+
      ∑k∈Finset.range n,((-1:ℚ)^(k+1)/(k+2:ℕ)) • coeff (n+1) ((f-1)^(k+2)) := by
  simp only [log,coeff_mk]
  rw [Finset.sum_range_succ']
  simp only [pow_zero,Nat.cast_one,one_div,inv_one,zero_add,pow_one,map_sub,
    coeff_one,Nat.succ_ne_zero,ite_false,sub_zero,one_smul]
  rw [add_comm]

lemma log_leading_difference (f g : PowerSeries R) (n : ℕ)
    (hf : constantCoeff f=1) (hg : constantCoeff g=1)
    (h : ∀j≤n,coeff j f=coeff j g) :
    coeff (n+1) (log f)-coeff (n+1) (log g)=coeff (n+1) f-coeff (n+1) g := by
  rw [log_coeff_succ,log_coeff_succ]
  have hs : (∑k∈Finset.range n,((-1:ℚ)^(k+1)/(k+2:ℕ)) • coeff (n+1) ((f-1)^(k+2)))=
      ∑k∈Finset.range n,((-1:ℚ)^(k+1)/(k+2:ℕ)) • coeff (n+1) ((g-1)^(k+2)) := by
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    apply pow_coeff_congr_of_two_le
    · simp [hf]
    · simp [hg]
    · omega
    · intro j hj
      simp only [map_sub,h j (by omega)]
  rw [hs]
  abel
end
end ElementaryPositivity.FormalLog
end
end

end OAI
