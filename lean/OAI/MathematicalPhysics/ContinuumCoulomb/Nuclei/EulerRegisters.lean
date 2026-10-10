import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalBoxRound
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.CappedKernelProgram
import OAI.Computability.QuantumFactoring.BitStackListMapWith

namespace OAI

/-! Three bounded integer numerator registers suffice for a rounded Euler
trajectory. The size invariant is unconditional on the supplied sampler;
it therefore supports polynomial-time iteration on every encoded input. -/

namespace ContinuumCoulomb.EulerRegisters
open ExactQuantumFactoring.BitStackProgram
open CappedKernelProgram (Triple)

abbrev Registers := ℤ×(ℤ×ℤ)
abbrev Parameters (E : Type) := E×(ℕ×(ℕ×ℚ))
abbrev Config (E : Type) := Parameters E×(ℕ×Registers)

def registersCode : Registers → List Bool := prodCode intCode (prodCode intCode intCode)
def parametersCode {E : Type} (ce : E → List Bool) : Parameters E → List Bool :=
  prodCode ce (prodCode Nat.bits (prodCode Nat.bits ratCode))
def configCode {E : Type} (ce : E → List Bool) : Config E → List Bool :=
  prodCode (parametersCode ce) (prodCode Nat.bits registersCode)

def point (D : ℕ) (r : Registers) : Triple :=
  ((r.1:ℚ)/D,((r.2.1:ℚ)/D,(r.2.2:ℚ)/D))

def round (D B : ℕ) (q : Triple) : Registers :=
  (RationalBoxRound.numerator D B q.1,
    (RationalBoxRound.numerator D B q.2.1,RationalBoxRound.numerator D B q.2.2))

def proposal (h : ℚ) (q v : Triple) : Triple :=
  (q.1+h*v.1,(q.2.1+h*v.2.1,q.2.2+h*v.2.2))

def advance {E : Type} (evaluate : E → ℚ → Triple → Triple) (c : Config E) : Config E :=
  let q := point c.1.2.1 c.2.2
  let h := c.1.2.2.2
  let v := evaluate c.1.1 ((c.2.1:ℚ)*h) q
  (c.1,(c.2.1+1,round c.1.2.1 c.1.2.2.1 (proposal h q v)))

theorem parameters_length {E : Type} (ce : E → List Bool) (p : Parameters E) :
    (parametersCode ce p).length = 2*(ce p.1).length+2*p.2.1.bits.length+
      2*p.2.2.1.bits.length+(ratCode p.2.2.2).length+3 := by
  simp only [parametersCode,prodCode,pairBits_length]
  omega

theorem config_length {E : Type} (ce : E → List Bool) (c : Config E) :
    (configCode ce c).length = 2*(parametersCode ce c.1).length+2*c.2.1.bits.length+
      2*c.2.2.1.natAbs.bits.length+2*c.2.2.2.1.natAbs.bits.length+
      c.2.2.2.2.natAbs.bits.length+19 := by
  simp only [configCode,registersCode,prodCode,pairBits_length,intCode,intData,
    Procedure.boolCode,List.length_singleton]
  omega

theorem iterate_parameters {E : Type} (evaluate : E → ℚ → Triple → Triple)
    (c : Config E) (n : ℕ) : ((advance evaluate)^[n] c).1 = c.1 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Function.iterate_succ_apply',advance] using ih

theorem iterate_counter {E : Type} (evaluate : E → ℚ → Triple → Triple)
    (c : Config E) (n : ℕ) : ((advance evaluate)^[n] c).2.1 = c.2.1+n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change ((advance evaluate)^[n] c).2.1+1 = c.2.1+(n+1)
    rw [ih]
    omega

theorem iterate_register_bounds {E : Type} (evaluate : E → ℚ → Triple → Triple)
    (c : Config E) {n : ℕ} (hn : 0 < n) :
    let r := ((advance evaluate)^[n] c).2.2
    r.1.natAbs.bits.length ≤ c.1.2.2.1.bits.length ∧
      r.2.1.natAbs.bits.length ≤ c.1.2.2.1.bits.length ∧
      r.2.2.natAbs.bits.length ≤ c.1.2.2.1.bits.length := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [Function.iterate_succ_apply']
  simp only [advance,round]
  rw [iterate_parameters]
  exact ⟨RationalBoxRound.numerator_bits _ _ _,RationalBoxRound.numerator_bits _ _ _,
    RationalBoxRound.numerator_bits _ _ _⟩

theorem iterate_code_bound {E : Type} (ce : E → List Bool)
    (evaluate : E → ℚ → Triple → Triple) (n : ℕ) (c : Config E) (i : ℕ) (hi : i ≤ n) :
    (configCode ce ((advance evaluate)^[i] c)).length ≤
      (32*(Polynomial.X+1)^2 : Polynomial ℕ).eval (n+(configCode ce c).length) := by
  let L := (configCode ce c).length
  have hlen := config_length ce c
  have hp := parameters_length ce c.1
  have hB : c.1.2.2.1.bits.length ≤ L := by dsimp [L]; omega
  have hk : c.2.1.bits.length ≤ L := by dsimp [L]; omega
  have hpar : (parametersCode ce c.1).length ≤ L := by dsimp [L]; omega
  have hsize : (configCode ce ((advance evaluate)^[i] c)).length ≤ 9*L+2*n+24 := by
    by_cases hz : i=0
    · subst i
      simp only [Function.iterate_zero_apply]
      dsimp [L]
      omega
    · have hr := iterate_register_bounds evaluate c (Nat.pos_of_ne_zero hz)
      have hc := bits_length_add c.2.1 i
      have hiBits := ExactQuantumFactoring.NativeAIG.nat_bits_length_bound i
      rw [config_length,iterate_parameters,iterate_counter]
      omega
  apply hsize.trans
  simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_one]
  change 9*L+2*n+24 ≤ 32*(n+L+1)^2
  nlinarith

end ContinuumCoulomb.EulerRegisters

end OAI
