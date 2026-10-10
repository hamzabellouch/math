import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.DisjointPool

namespace OAI

namespace MetricKMedianRecovery.DyadicGrid
abbrev State := ℕ × ℕ × ℕ
def point (a b : ℚ) (i d : ℕ) : ℚ := a+(b-a)*(i:ℚ)/(d:ℚ)
def interval (a b : ℚ) (g : State) : ℚ×ℚ := (point a b g.1 g.2.2,point a b g.2.1 g.2.2)
def advance (count : ℚ→ℕ) (k : ℕ) (a b : ℚ) (g : State) : State :=
  if k≤count (point a b (g.1+g.2.1) (2*g.2.2)) then (g.1+g.2.1,2*g.2.1,2*g.2.2)
  else (2*g.1,g.1+g.2.1,2*g.2.2)
def start : State := (0,1,1)
lemma point_double (a b : ℚ) (i d : ℕ) (hd : d≠0) : point a b (2*i) (2*d)=point a b i d := by
  have hz : (d:ℚ)≠0 := by exact_mod_cast hd
  unfold point
  push_cast
  field_simp
lemma point_mid (a b : ℚ) (i j d : ℕ) (hd : d≠0) :
    point a b (i+j) (2*d)=(point a b i d+point a b j d)/2 := by
  have hz : (d:ℚ)≠0 := by exact_mod_cast hd
  unfold point
  push_cast
  field_simp
  ring
lemma advance_interval (count : ℚ→ℕ) (k : ℕ) (a b : ℚ) (g : State) (hg : g.2.2≠0) :
    interval a b (advance count k a b g)=PriceBisection.refine count k (interval a b g) := by
  rcases g with ⟨i,j,d⟩
  simp only [advance,interval,PriceBisection.refine,point_mid a b i j d hg]
  split_ifs with h <;> simp only [point_mid a b i j d hg,point_double a b _ d hg,h,ite_true,ite_false]
lemma advance_bounds (count : ℚ→ℕ) (k : ℕ) (a b : ℚ) (g : State) (hg : g.1≤g.2.2 ∧ g.2.1≤g.2.2) :
    (advance count k a b g).1≤2*g.2.2 ∧ (advance count k a b g).2.1≤2*g.2.2 ∧
      (advance count k a b g).2.2=2*g.2.2 := by
  unfold advance
  split_ifs <;> dsimp <;> omega
lemma iterate_bounds (count : ℚ→ℕ) (k : ℕ) (a b : ℚ) (n : ℕ) :
    let g := (advance count k a b)^[n] start
    g.1≤2^n ∧ g.2.1≤2^n ∧ g.2.2=2^n := by
  induction n with
  | zero=>simp only [Function.iterate_zero_apply,start,pow_zero,Nat.zero_le,Nat.le_refl,and_self]
  | succ n ih=>
    have hh:=advance_bounds count k a b ((advance count k a b)^[n] start) ⟨by omega,by omega⟩
    rw [Function.iterate_succ_apply']
    simp only [pow_succ']
    omega
lemma search_iterate (count : ℚ→ℕ) (k n : ℕ) (I : ℚ×ℚ) :
    PriceBisection.search count k n I=(PriceBisection.refine count k)^[n] I := by
  induction n generalizing I with
  | zero=>rfl
  | succ n ih=>rw [PriceBisection.search,ih,Function.iterate_succ_apply]
lemma iterate_interval (count : ℚ→ℕ) (k : ℕ) (a b : ℚ) (n : ℕ) :
    interval a b ((advance count k a b)^[n] start)=PriceBisection.search count k n (a,b) := by
  rw [search_iterate]
  induction n with
  | zero=>simp only [Function.iterate_zero_apply,interval,start,point,Nat.cast_zero,Nat.cast_one,mul_zero,add_zero,mul_one,div_one,add_sub_cancel]
  | succ n ih=>
    have hd : ((advance count k a b)^[n] start).2.2≠0 := by
      rw [(iterate_bounds count k a b n).2.2]
      positivity
    rw [Function.iterate_succ_apply',advance_interval count k a b _ hd,ih,Function.iterate_succ_apply']
end MetricKMedianRecovery.DyadicGrid

end OAI
