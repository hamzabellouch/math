import Mathlib

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation

lemma sparse_polynomial_doubling_scales (f : ℕ → ℕ) (hf : Monotone f)
    (hpos : ∀ n, 1≤f n) (d : ℕ) (hpoly : ∀ R, ∃ n≥R, f n≤n^d) :
    ∀ R : ℕ, ∃ n≥R, f (5*n)≤5^(d+1)*f n := by
  intro R
  by_contra! hbad
  let A := max R 1
  have hA : 0<A := by dsimp [A]; omega
  have hRA : R≤A := le_max_left _ _
  have hgrow : ∀ k : ℕ, (5^(d+1))^k≤f (5^k*A) := by
    intro k
    induction k with
    | zero => simpa using hpos A
    | succ k ih =>
      have hbase : R≤5^k*A := hRA.trans (by
        have : 1≤5^k := Nat.one_le_pow k 5 (by omega)
        nlinarith)
      have hh := (hbad (5^k*A) hbase).le
      calc
        (5^(d+1))^(k+1) = 5^(d+1)*(5^(d+1))^k := by rw [pow_succ]; ring
        _ ≤ 5^(d+1)*f (5^k*A) := Nat.mul_le_mul_left _ ih
        _ ≤ f (5*(5^k*A)) := hh
        _ = f (5^(k+1)*A) := by congr 1; rw [pow_succ]; ring
  obtain ⟨n,hn,hnpoly⟩ := hpoly (5*A*((5*A)^d+1))
  have hnA : 5*((5*A)^d+1)≤n/A := by
    apply (Nat.le_div_iff_mul_le hA).mpr
    nlinarith
  have hnApos : n/A≠0 := by omega
  let k := Nat.log 5 (n/A)
  let P := 5^k
  have hP : P≤n/A := Nat.pow_log_le_self 5 hnApos
  have hP' : n/A<5*P := by
    have hh := Nat.lt_pow_of_log_lt (b := 5) (x := k+1) (y := n/A) (by omega)
      (show Nat.log 5 (n/A)<k+1 by omega)
    simpa only [pow_succ,Nat.mul_comm] using hh
  have hPL : (5*A)^d<P := by nlinarith
  have hPA : P*A≤n := (Nat.le_div_iff_mul_le hA).mp hP
  have hnupper : n<(5*P)*A := (Nat.div_lt_iff_lt_mul hA).mp hP'
  have hPP : 5^((d+1)*k)≤f n := by
    rw [pow_mul]
    exact (hgrow k).trans (hf hPA)
  have hform : 5^((d+1)*k)=P^d*P := by
    dsimp [P]
    rw [←pow_mul,←pow_add]
    congr 1
    ring
  rw [hform] at hPP
  have hupper : n^d≤P^d*(5*A)^d := by
    have hh := Nat.pow_le_pow_left hnupper.le d
    convert hh using 1
    ring
  have hPpos : 0<P^d := pow_pos (by dsimp [P]; positivity) d
  have hlt : P^d*(5*A)^d<P^d*P := Nat.mul_lt_mul_of_pos_left hPL hPpos
  exact (not_lt_of_ge (hPP.trans (hnpoly.trans hupper))) hlt

end CriticalPercolation
end
end

end OAI
