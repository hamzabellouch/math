import Mathlib
import OAI.Computability.QuantumFactoring.AuxiliaryTree

namespace OAI

section
open scoped BigOperators


/-! Bounded, guarded binary factor controller for a single auxiliary-tree node.
Only proper divisors are accepted and primality is tested, never assumed.  The
mathematical prime-factor count is used solely in its termination proof. -/
namespace ExactQuantumFactoring.FactorController
open AuxiliaryTree

def ProperDivisor (m d : ℕ) : Prop := 1 < d ∧ d < m ∧ d ∣ m
instance (m d : ℕ) : Decidable (ProperDivisor m d) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

lemma ProperDivisor.quotient {m d : ℕ} (h : ProperDivisor m d) :
    2 ≤ m/d ∧ m/d < m ∧ d*(m/d)=m := by
  rcases h with ⟨hd,hdm,hdiv⟩
  have he := Nat.mul_div_cancel' hdiv
  have hp : 0 < m/d := Nat.div_pos (by omega) (by omega)
  have hl : m/d < m := Nat.div_lt_self (by omega) hd
  refine ⟨?_,hl,he⟩
  by_contra hh
  have : m/d=1 := by omega
  rw [this,mul_one] at he
  omega

lemma splitWeight_pos {m : ℕ} (hm : 2 ≤ m) : 0 < splitWeight m := by
  by_contra h
  have hl : m.primeFactorsList=[] := List.length_eq_zero_iff.mp (by
    change splitWeight m=0
    omega)
  have he := Nat.prod_primeFactorsList (by omega : m≠0)
  rw [hl,List.prod_nil] at he
  omega

lemma splitWeight_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    splitWeight (a*b)=splitWeight a+splitWeight b := by
  have hh := (Nat.perm_primeFactorsList_mul ha.ne' hb.ne').length_eq
  simpa only [splitWeight,List.length_append] using hh

lemma splitWeight_split {m d : ℕ} (h : ProperDivisor m d) :
    splitWeight m=splitWeight d+splitWeight (m/d) := by
  have hq := h.quotient
  conv_lhs =>  rw [← hq.2.2]
  exact splitWeight_mul (by have := h.1; omega) (by omega)

def weight (ms : List ℕ) : ℕ := (ms.map (fun m =>  2*splitWeight m-1)).sum

lemma weight_prime (m : ℕ) (ms : List ℕ) (hm : m.Prime) :
    weight (m::ms)=weight ms+1 := by
  simp [weight,splitWeight,Nat.primeFactorsList_prime hm,Nat.add_comm]

lemma weight_split {m d : ℕ} (h : ProperDivisor m d) (ms : List ℕ) :
    weight (m::ms)=weight (d::m/d::ms)+1 := by
  have hd := splitWeight_pos (by have := h.1; omega : 2 ≤ d)
  have hq := splitWeight_pos h.quotient.1
  have he := splitWeight_split h
  simp only [weight,List.map_cons,List.sum_cons]
  omega

/-- `choose i m` is the prospective divisor obtained at the i-th guarded
controller step from its recorded classical transition outputs. -/
def run (choose : ℕ→ℕ→ℕ) : ℕ→ℕ→List ℕ→Option (List ℕ)
  | _, _, [] =>  some []
  | 0, _, _::_ =>  none
  | fuel+1, i, m::ms => 
    if m.Prime then (run choose fuel (i+1) ms).map (m::·)
    else let d := choose i m
         if ProperDivisor m d then run choose fuel (i+1) (d::m/d::ms) else none

/-- On every output sequence, a successful result is a genuine complete
factorization. Bad divisors cause an abort, not a false prime leaf. -/
theorem run_sound (choose : ℕ→ℕ→ℕ) {fuel i : ℕ} {ms ps : List ℕ}
    (h : run choose fuel i ms=some ps) :
    (∀ p∈ps, p.Prime) ∧ ps.prod=ms.prod := by
  induction fuel generalizing i ms ps with
  | zero => 
    cases ms with
    | nil =>  simp only [run,Option.some.injEq] at h; subst ps; simp
    | cons m ms =>  simp [run] at h
  | succ fuel ih => 
    cases ms with
    | nil =>  simp only [run,Option.some.injEq] at h; subst ps; simp
    | cons m ms => 
      simp only [run] at h
      split_ifs at h with hp hd
      · obtain ⟨qs,hq,hps⟩ := Option.map_eq_some_iff.mp h
        subst ps
        obtain ⟨hprime,hprod⟩ := ih hq
        exact ⟨by simpa only [List.mem_cons,forall_eq_or_imp] using And.intro hp hprime,
          by simp only [List.prod_cons,hprod]⟩
      · obtain ⟨hprime,hprod⟩ := ih h
        refine ⟨hprime,?_⟩
        rw [List.prod_cons,List.prod_cons,← Nat.mul_assoc,hd.quotient.2.2] at hprod
        exact hprod

/-- All-good divisors cannot exhaust the linear (in logarithmic input size)
controller clock. This theorem controls arbitrary supplied good outputs. -/
theorem run_complete (choose : ℕ→ℕ→ℕ) {N fuel i : ℕ} {ms : List ℕ}
    (hgood : ∀ i m, 2 ≤ m → m ≤ N → ¬m.Prime → ProperDivisor m (choose i m))
    (hms : ∀ m∈ms, 2 ≤ m ∧ m ≤ N) (hw : weight ms ≤ fuel) :
    ∃ ps, run choose fuel i ms=some ps := by
  induction fuel generalizing i ms with
  | zero => 
    cases ms with
    | nil =>  exact ⟨[],rfl⟩
    | cons m ms => 
      have hm := hms m (by simp)
      have hp := splitWeight_pos hm.1
      simp only [weight,List.map_cons,List.sum_cons] at hw
      omega
  | succ fuel ih => 
    cases ms with
    | nil =>  exact ⟨[],rfl⟩
    | cons m ms => 
      have hm := hms m (by simp)
      have htail : ∀ a∈ms, 2 ≤ a ∧ a ≤ N := fun a ha =>  hms a (by simp [ha])
      by_cases hp : m.Prime
      · have hw' : weight ms ≤ fuel := by rw [weight_prime m ms hp] at hw; omega
        obtain ⟨ps,hps⟩ := ih htail hw' (i:=i+1)
        refine ⟨m::ps,?_⟩
        simp only [run,ite_eq_left hp,hps,Option.map_some]
      · have hd := hgood i m hm.1 hm.2 hp
        have hq := hd.quotient
        have hms' : ∀ a∈choose i m::m/choose i m::ms, 2 ≤ a ∧ a ≤ N := by
          intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact ⟨by have := hd.1; omega,hd.2.1.le.trans hm.2⟩
          · rcases List.mem_cons.mp ha with rfl | ha
            · exact ⟨hq.1,hq.2.1.le.trans hm.2⟩
            · exact htail a ha
        have hw' : weight (choose i m::m/choose i m::ms) ≤ fuel := by
          rw [weight_split hd ms] at hw
          omega
        obtain ⟨ps,hps⟩ := ih hms' hw' (i:=i+1)
        exact ⟨ps,by simpa only [run,ite_eq_right hp,ite_eq_left hd] using hps⟩

/-- A 2n-step clock suffices for every bounded node. Its successful list is
then sorted, padded and passed to the concrete verifier. -/
theorem bounded_node_complete {N n : ℕ} (hN : 2 ≤ N) (hb : N < 2^n)
    (choose : ℕ→ℕ→ℕ)
    (hgood : ∀ i m, 2 ≤ m → m ≤ N → ¬m.Prime → ProperDivisor m (choose i m)) :
    ∃ ps, run choose (2*n) 0 [N]=some ps ∧
      (∀ p∈ps, p.Prime) ∧ ps.prod=N ∧ ps.length < n := by
  have hw : weight [N] ≤ 2*n := by
    have h := splitWeight_bound (by omega) hb
    simp only [weight,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    omega
  obtain ⟨ps,hps⟩ := run_complete choose hgood (by simpa using And.intro hN (le_rfl : N ≤ N)) hw (i:=0)
  have hs := run_sound choose hps
  have hprod : ps.prod=N := by simpa using hs.2
  have hlen : ps.length=splitWeight N := (Nat.primeFactorsList_unique hprod hs.1).length_eq
  exact ⟨ps,hps,hs.1,hprod,hlen.trans_lt (splitWeight_bound (by omega) hb)⟩

end ExactQuantumFactoring.FactorController


end

end OAI
