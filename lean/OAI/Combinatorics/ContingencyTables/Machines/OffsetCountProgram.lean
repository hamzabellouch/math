import OAI.Combinatorics.ContingencyTables.Machines.ScaledWordProgram
import Mathlib.Algebra.Order.Floor.Div

namespace OAI

/-! # Exact binary tabulation of the bounded offset law -/

namespace ContingencyTables.OffsetCountPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

def ceilQuotient (z : ℕ×ℕ) : ℕ := (z.1+z.2-1)/z.2

def ceilQuotientRealizer : Realizer ceilQuotient :=
  composition (pair
    (composition (pair (composition (pair first second) add) (constant 1)) subtract)
    second) quotient

lemma polynomial_ceilQuotient : PolynomialTime ceilQuotientRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair polynomial_first polynomial_second) polynomial_add)
      (polynomial_constant 1)) polynomial_subtract)
    polynomial_second) polynomial_quotient

lemma ceilQuotient_eq (n d : ℕ) (hd : 0<d) :
    ceilQuotient (n,d)=⌈(n:ℚ)/d⌉₊ := by
  change n ⌈/⌉ d=⌈(n:ℚ)/d⌉₊
  have hdq : (0:ℚ)<d := by exact_mod_cast hd
  apply le_antisymm
  · rw [ceilDiv_le_iff_le_mul hd]
    have hh:=Nat.le_ceil ((n:ℚ)/d)
    have hn : n≤⌈(n:ℚ)/d⌉₊*d := by exact_mod_cast (div_le_iff₀ hdq).mp hh
    simpa only [Nat.mul_comm] using hn
  · rw [Nat.ceil_le,div_le_iff₀ hdq]
    have hn : n≤d*(n ⌈/⌉ d) := by
      simpa only [smul_eq_mul] using (le_smul_ceilDiv (b := n) hd)
    have hn' : n≤(n ⌈/⌉ d)*d := by simpa only [Nat.mul_comm] using hn
    exact_mod_cast hn'

abbrev Input := (ℕ×ℕ)×ℕ

def endpoint (z : Input) : ℕ := ceilQuotient (z.2*z.1.2,z.1.1)

def endpointRealizer : Realizer endpoint :=
  composition (pair
    (composition (pair second (composition first second)) multiply)
    (composition first first)) ceilQuotientRealizer

lemma polynomial_endpoint : PolynomialTime endpointRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_second
      (polynomial_composition polynomial_first polynomial_second)) polynomial_multiply)
    (polynomial_composition polynomial_first polynomial_first)) polynomial_ceilQuotient

def offsetCount (z : Input) : ℕ := endpoint (z.1,z.2+1)-endpoint z

def offsetCountRealizer : Realizer offsetCount :=
  composition (pair
    (composition (pair first (composition second successor)) endpointRealizer)
    endpointRealizer) subtract

lemma polynomial_offsetCount : PolynomialTime offsetCountRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_successor)) polynomial_endpoint)
    polynomial_endpoint) polynomial_subtract

lemma endpoint_eq (M Q β : ℕ) (hM : 0<M) :
    endpoint ((M,Q),β)=FairBits.endpoint M Q β := by
  rw [endpoint,ceilQuotient_eq _ _ hM]
  simp only [FairBits.endpoint,Nat.cast_mul]

/-- Only two ceiling divisions are required, regardless of the number of
random words whose probability is being counted. -/
theorem offsetCount_eq (M Q β : ℕ) (hM : 0<M) (hQ : 0<Q) (hβ : β<M) :
    offsetCount ((M,Q),β)=(FairBits.fiber M Q β).card := by
  rw [FairBits.fiber_card hM hQ hβ,offsetCount,endpoint_eq _ _ _ hM,endpoint_eq _ _ _ hM]

theorem scaledLaw_mass (M k : ℕ) (hM : 0<M) (β : Fin M) :
    (FairBits.scaledLaw M k hM).mass β=
      (offsetCount ((M,2^k),β.val):ℚ)/(2:ℚ)^k := by
  rw [offsetCount_eq _ _ _ hM (by positivity) β.isLt]
  simp only [FairBits.scaledLaw,FairBits.outputMass,Nat.cast_pow,Nat.cast_ofNat]

end ContingencyTables.OffsetCountPrograms

end OAI
