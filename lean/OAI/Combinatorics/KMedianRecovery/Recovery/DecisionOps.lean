import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.DisjointPool
import OAI.Combinatorics.KMedianRecovery.Recovery.Basic2

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
noncomputable def PolyComputes.not {p : List Bool → Bool} (hp : PolyComputes (fun x=>[p x])) :
    PolyComputes (fun x=>[!p x]) := by
  have h:=hp.cond (const_computes [false]) (const_computes [true])
  convert h using 1
  funext x
  cases p x <;> rfl
noncomputable def PolyComputes.and {p q : List Bool → Bool}
    (hp : PolyComputes (fun x=>[p x])) (hq : PolyComputes (fun x=>[q x])) :
    PolyComputes (fun x=>[p x && q x]) := by
  have h:=hp.cond hq (const_computes [false])
  convert h using 1
  funext x
  cases p x <;> rfl
noncomputable def PolyComputes.or {p q : List Bool → Bool}
    (hp : PolyComputes (fun x=>[p x])) (hq : PolyComputes (fun x=>[q x])) :
    PolyComputes (fun x=>[p x || q x]) := by
  have h:=hp.cond (const_computes [true]) hq
  convert h using 1
  funext x
  cases p x <;> rfl
namespace NatOps
noncomputable def lt {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>[decide (value (f x)<value (g x))]) := by
  simpa only [←decide_not,not_le] using (le hg hf).not
end NatOps
namespace RatOps
noncomputable def lt {f g : List Bool → ℚ}
    (hf : PolyComputes (fun x=>BinaryRational.encode (f x)))
    (hg : PolyComputes (fun x=>BinaryRational.encode (g x))) :
    PolyComputes (fun x=>[decide (f x<g x)]) := by
  simpa only [←decide_not,not_le] using (le hg hf).not
noncomputable def eq {f g : List Bool → ℚ}
    (hf : PolyComputes (fun x=>BinaryRational.encode (f x)))
    (hg : PolyComputes (fun x=>BinaryRational.encode (g x))) :
    PolyComputes (fun x=>[decide (f x=g x)]) := by
  simpa only [←Bool.decide_and,le_antisymm_iff] using ((le hf hg).and (le hg hf))
end RatOps
end MetricKMedianRecovery.BitMachine

namespace MetricKMedianRecovery.PriceBisection

section
open RationalHeight

lemma search_eq_iterate (count : ℚ → ℕ) (h n : ℕ) (I : ℚ × ℚ) :
    search count h n I = (refine count h)^[n] I := by
  induction n generalizing I with
  | zero => rfl
  | succ n ih => rw [search, ih, Function.iterate_succ_apply]

lemma iterate_dyadic (count : ℚ → ℕ) (h n : ℕ) (a b : ℚ) :
    ∃ j : ℕ, j < 2^n ∧
      ((refine count h)^[n] (a,b)).1 = a+(b-a)*(j:ℚ)/2^n ∧
      ((refine count h)^[n] (a,b)).2 = a+(b-a)*(j+1:ℕ)/2^n := by
  induction n with
  | zero => exact ⟨0,by norm_num,by simp,by simp⟩
  | succ n ih =>
    obtain ⟨j,hj,hl,hu⟩ := ih
    have hn : (2:ℚ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
    have hm : (((refine count h)^[n] (a,b)).1+
        ((refine count h)^[n] (a,b)).2)/2 =
        a+(b-a)*(2*j+1:ℕ)/(2:ℚ)^(n+1) := by
      rw [hl,hu,pow_succ]
      push_cast
      field_simp
      ring
    rw [Function.iterate_succ_apply']
    simp only [refine]
    split_ifs with hc
    · refine ⟨2*j+1,by rw [pow_succ]; omega,hm,?_⟩
      rw [hu,pow_succ]
      push_cast
      field_simp
      ring
    · refine ⟨2*j,by rw [pow_succ]; omega,?_,hm⟩
      rw [hl,pow_succ]
      push_cast
      field_simp

lemma dyadic_height {a b : ℚ} {N n j : ℕ}
    (ha : Height a N) (hb : Height b N) (hj : j ≤ 2^n) :
    Height (a+(b-a)*(j:ℚ)/(2:ℚ)^n) (3*N+2*n+2) := by
  have hjh := natCast j n hj
  have h2 : Height ((2:ℚ)^n) n := by
    have hh := natCast (2^n) n le_rfl
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
  have hh := ha.add (((hb.sub ha).mul hjh).div h2)
  convert hh using 1
  omega

lemma iterate_height {a b : ℚ} {N : ℕ} (ha : Height a N) (hb : Height b N)
    (count : ℚ → ℕ) (h n : ℕ) :
    Height ((refine count h)^[n] (a,b)).1 (3*N+2*n+2) ∧
    Height ((refine count h)^[n] (a,b)).2 (3*N+2*n+2) := by
  obtain ⟨j,hj,hl,hu⟩ := iterate_dyadic count h n a b
  rw [hl,hu]
  exact ⟨dyadic_height ha hb hj.le,dyadic_height ha hb (by omega)⟩

end

lemma clog_two_bits (n : ℕ) : Nat.clog 2 n = (n-1).bits.length := by
  apply eq_of_forall_ge_iff
  intro t
  rw [Nat.clog_le_iff_le_pow (by norm_num : 1 < 2), Nat.size_eq_bits_len, Nat.size_le]
  have hp : 0 < (2:ℕ)^t := pow_pos (by norm_num) _
  omega

end MetricKMedianRecovery.PriceBisection

end OAI
