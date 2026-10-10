import OAI.Combinatorics.ContingencyTables.Machines.SignedFloorProgram
import OAI.Combinatorics.ContingencyTables.Machines.DyadicRootProgram
import OAI.Combinatorics.ContingencyTables.Transport.PowerOfTwoApproximation

namespace OAI

/-! # Executing the rounded power used by the correction oracle

The exponent lies in [-2,2]. Clipping the computed signed floor
at twice the supplied degree allowance plus one is therefore inactive
on valid inputs, and keeps every binary execution polynomial even on
arbitrary malformed numerator/denominator data.
-/

namespace ContingencyTables.RoundedPowerProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial SignedPairProgram

abbrev Input := SignedFloorProgram.ScaledInput

def normalized (z : Input) : Signed := SignedPairProgram.normalize (SignedFloorProgram.scaledFloor z)
def normalizedRealizer : Realizer normalized :=
  composition SignedFloorProgram.scaledFloorRealizer SignedPairProgram.normalizeRealizer
lemma polynomial_normalized : PolynomialTime normalizedRealizer :=
  polynomial_composition SignedFloorProgram.polynomial_scaledFloor SignedPairProgram.polynomial_normalize

def cap (z : Input) : ℕ := 2*z.2.length+1
def capRealizer : Realizer cap := composition
  (f:=fun z : Input=>2*z.2.length) (g:=Nat.succ)
  (composition (f:=fun z : Input=>(2,z.2.length)) (g:=fun p : ℕ×ℕ=>p.1*p.2)
    (pair (constant 2) (composition second listLength)) multiply) successor
lemma polynomial_cap : PolynomialTime capRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_pair (polynomial_constant 2)
      (polynomial_composition polynomial_second polynomial_listLength)) polynomial_multiply)
    polynomial_successor

def clipped (z : Input) : Signed :=
  (min (normalized z).1 (cap z),min (normalized z).2 (cap z))
def clippedRealizer : Realizer clipped := pair
  (composition (pair (composition normalizedRealizer first) capRealizer) minimum)
  (composition (pair (composition normalizedRealizer second) capRealizer) minimum)
lemma polynomial_clipped : PolynomialTime clippedRealizer := polynomial_pair
  (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_normalized polynomial_first) polynomial_cap) polynomial_minimum)
  (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_normalized polynomial_second) polynomial_cap) polynomial_minimum)

def positiveInput (z : Input) : ℕ×ℕ := (2,(clipped z).1)
def negativeInput (z : Input) : ℕ×ℕ := (2,(clipped z).2)
def positiveInputRealizer : Realizer positiveInput := pair (constant 2) (composition clippedRealizer first)
def negativeInputRealizer : Realizer negativeInput := pair (constant 2) (composition clippedRealizer second)
lemma polynomial_positiveInput : PolynomialTime positiveInputRealizer :=
  polynomial_pair (polynomial_constant 2) (polynomial_composition polynomial_clipped polynomial_first)
lemma polynomial_negativeInput : PolynomialTime negativeInputRealizer :=
  polynomial_pair (polynomial_constant 2) (polynomial_composition polynomial_clipped polynomial_second)

def positivePower (z : Input) : ℕ := BinaryPowerPrograms.power (positiveInput z)
def negativePower (z : Input) : ℕ := BinaryPowerPrograms.power (negativeInput z)
def positivePowerRealizer : Realizer positivePower :=
  composition positiveInputRealizer BinaryPowerPrograms.powerRealizer
def negativePowerRealizer : Realizer negativePower :=
  composition negativeInputRealizer BinaryPowerPrograms.powerRealizer

lemma polynomial_positivePower : PolynomialTime positivePowerRealizer := by
  apply work_composition polynomial_positiveInput BinaryPowerPrograms.work_power (2*X+10)
  intro z
  have hl: z.2.length ≤ weight z:=(list_length_le_weight z.2).trans (weight_snd z)
  have hm: (clipped z).1 ≤ cap z:=min_le_right _ _
  have ht: weight (2:ℕ) ≤ 9:=by decide
  simp only [positiveInput,cap,eval_add,eval_mul,eval_ofNat,eval_X] at *
  omega

lemma polynomial_negativePower : PolynomialTime negativePowerRealizer := by
  apply work_composition polynomial_negativeInput BinaryPowerPrograms.work_power (2*X+10)
  intro z
  have hl: z.2.length ≤ weight z:=(list_length_le_weight z.2).trans (weight_snd z)
  have hm: (clipped z).2 ≤ cap z:=min_le_right _ _
  have ht: weight (2:ℕ) ≤ 9:=by decide
  simp only [negativeInput,cap,eval_add,eval_mul,eval_ofNat,eval_X] at *
  omega

def output (z : Input) : TreeFraction.Fraction :=
  TreeFraction.normalize (positivePower z,negativePower z)
def outputRealizer : Realizer output :=
  composition (pair positivePowerRealizer negativePowerRealizer) TreeFraction.normalizeRealizer
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition (polynomial_pair polynomial_positivePower polynomial_negativePower)
    TreeFraction.polynomial_normalize

lemma floor_bounds (beta : ℚ) (hlo : -2 ≤ beta) (hhi : beta ≤ 2) (s : ℕ) :
    -2*(s:ℤ) ≤ ⌊(s:ℚ)*beta⌋ ∧ ⌊(s:ℚ)*beta⌋ ≤ 2*(s:ℤ) := by
  have hL:=mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg s : (0:ℚ) ≤ s)
  have hU:=mul_le_mul_of_nonneg_left hhi (Nat.cast_nonneg s : (0:ℚ) ≤ s)
  constructor
  · apply Int.le_floor.mpr
    push_cast
    linarith
  · have hf: (⌊(s:ℚ)*beta⌋:ℚ) ≤ 2*s:=(Int.floor_le _).trans (by linarith)
    exact_mod_cast hf

lemma clipped_eq (p n d : ℕ) (xs : List Bool)
    (hlo: -2 ≤ ((p:ℚ)-n)/d) (hhi: ((p:ℚ)-n)/d ≤ 2) :
    clipped (((p,n),d),xs)=
      ((⌊(xs.length:ℚ)*(((p:ℚ)-n)/d)⌋:ℤ).toNat,
        (-⌊(xs.length:ℚ)*(((p:ℚ)-n)/d)⌋:ℤ).toNat) := by
  have hb:=floor_bounds _ hlo hhi xs.length
  have hp: (⌊(xs.length:ℚ)*(((p:ℚ)-n)/d)⌋:ℤ).toNat ≤ 2*xs.length+1:=by omega
  have hn: (-⌊(xs.length:ℚ)*(((p:ℚ)-n)/d)⌋:ℤ).toNat ≤ 2*xs.length+1:=by omega
  simp only [clipped,normalized,SignedPairProgram.normalize_eq,SignedFloorProgram.scaledFloor_value,
    ForestAffineProgram.signedParts,cap,min_eq_left hp,min_eq_left hn]

/-- The returned natural fraction is exactly the rational power used
by the approximation, including negative rounded exponents. -/
theorem output_value (p n d : ℕ) (xs : List Bool)
    (hlo: -2 ≤ ((p:ℚ)-n)/d) (hhi: ((p:ℚ)-n)/d ≤ 2) :
    TreeFraction.val (output (((p,n),d),xs))=
      (2:ℚ)^PowerOfTwoApproximation.numerator (((p:ℚ)-n)/d) xs.length := by
  rw [output,TreeFraction.normalize_val]
  simp only [positivePower,negativePower,positiveInput,negativeInput,
    BinaryPowerPrograms.power_eq,clipped_eq p n d xs hlo hhi,TreeFraction.val,Nat.cast_pow,Nat.cast_ofNat]
  let q:ℤ:=⌊(xs.length:ℚ)*(((p:ℚ)-n)/d)⌋
  change (2:ℚ)^q.toNat/(2:ℚ)^(-q).toNat=(2:ℚ)^q
  have he: (q.toNat:ℤ)-(-q).toNat=q:=by omega
  conv_rhs => rw [←he]
  rw [zpow_sub₀ (by norm_num : (2:ℚ)≠0),zpow_natCast,zpow_natCast]

theorem output_denominator_pos (z : Input) : 0<(output z).2 :=
  TreeFraction.normalize_den_pos _

end ContingencyTables.RoundedPowerProgram

end OAI
