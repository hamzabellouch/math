import OAI.NumberTheory.TotientAsymptotic.OrderedFactorizations
import OAI.NumberTheory.TotientAsymptotic.SmoothResidualMass
import OAI.NumberTheory.TotientAsymptotic.TupleRecovery
import OAI.NumberTheory.TotientAsymptotic.SmoothSuffix

namespace OAI

/-! The small smooth terminal factors when only one prime survives. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma smooth_terminal_factorization {d s t e : ℕ} (hd : 0 < d) (heq : d*s=t*e) :
    ∃ d₁ d₂ a b : ℕ,d=d₁*d₂ ∧ t=d₁*a ∧ e=d₂*b ∧ s=a*b := by
  have hdiv : d ∣ t*e := ⟨s,heq.symm⟩
  obtain ⟨d₁,d₂,ht,he,hdd⟩ := exists_dvd_and_dvd_of_dvd_mul hdiv
  obtain ⟨a,ha⟩ := ht
  obtain ⟨b,hb⟩ := he
  refine ⟨d₁,d₂,a,b,hdd,ha,hb,?_⟩
  apply Nat.eq_of_mul_eq_mul_left hd
  rw [heq,ha,hb,hdd]
  ring

lemma two_factorizations_card_le {d : ℕ} (hd : 0 < d) (Q : Finset (ℕ × ℕ))
    (hQ : ∀ z ∈ Q,z.1*z.2=d) : Q.card ≤ 2^d.primeFactorsList.length := by
  classical
  let f : ℕ × ℕ → Fin 2 → ℕ := fun z => ![z.1,z.2]
  have hi : Function.Injective f := by
    intro z w he
    have h₁ := congrFun he 0
    have h₂ := congrFun he 1
    exact Prod.ext (by simpa [f] using h₁) (by simpa [f] using h₂)
  have hh := ordered_factorizations_card_le d hd (Q.image f) (by
    intro g hg
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hg
    simpa [f,Fin.prod_univ_two] using hQ z hz)
  simpa only [Finset.card_image_of_injective Q hi,Fintype.card_fin] using hh

lemma smooth_divisor_bound {n a N : ℕ} (hn : 0 < n) (ha : a ∣ n)
    (hN : largestPrimeFactor n ≤ N) : largestPrimeFactor a ≤ N := by
  apply largestPrimeFactor_le_of_prime_divisors ((le_max_left _ _).trans hN)
  intro p hp hpa _
  exact (prime_dvd_le_largest hp hn.ne' (hpa.trans ha)).trans hN

abbrev SmoothTerminalTriple := ℕ × ℕ × ℕ

def terminalFirst (z : SmoothTerminalTriple) : ℕ := z.1

def terminalMiddle (z : SmoothTerminalTriple) : ℕ := z.2.1

def terminalLast (z : SmoothTerminalTriple) : ℕ := z.2.2

/-- The first coordinate is `s`; the equation is `d*s=t*e`. -/
def TerminalConditions (d N : ℕ) (z : SmoothTerminalTriple) : Prop :=
  0 < terminalFirst z ∧ d*terminalFirst z=terminalMiddle z*terminalLast z ∧
  largestPrimeFactor (terminalFirst z) ≤ N

noncomputable def terminalEncoding {N : ℕ} (d : ℕ) (hd : 0 < d)
    (z : SmoothTerminalTriple) (hz : TerminalConditions d N z) : (ℕ × ℕ) × (ℕ × ℕ) :=
  let h := smooth_terminal_factorization hd hz.2.1
  let d₁ := h.choose
  let d₂ := h.choose_spec.choose
  let a := h.choose_spec.choose_spec.choose
  let b := h.choose_spec.choose_spec.choose_spec.choose
  ((d₁,d₂),(a,b))

lemma terminalEncoding_spec (d N : ℕ) (hd : 0 < d)
    (z : SmoothTerminalTriple) (hz : TerminalConditions d N z) :
    let w := terminalEncoding d hd z hz
    d=w.1.1*w.1.2 ∧ terminalMiddle z=w.1.1*w.2.1 ∧
      terminalLast z=w.1.2*w.2.2 ∧ terminalFirst z=w.2.1*w.2.2 := by
  exact (smooth_terminal_factorization hd hz.2.1).choose_spec.choose_spec.choose_spec.choose_spec

end TotientAsymptotic

end

end OAI
