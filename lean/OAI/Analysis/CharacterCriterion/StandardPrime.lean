import OAI.Analysis.CharacterCriterion.Definitions
import OAI.Analysis.CharacterCriterion.PrimeChannels

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.StandardPrimeMultiplicity


lemma copies_pos (p : ℕ) (hp : 2≤p) : 0<copies p := by
  unfold copies
  exact Nat.mul_pos (by omega) (by positivity)
lemma dimension (p : ℕ) (hp : 2≤p) : p+p*(p+1)*copies p=next p := by
  cases p with
  | zero => omega
  | succ p => simp only [copies,next,Nat.add_sub_cancel]; ring
lemma middle_add_one (p : ℕ) (hp : 2≤p) : middle p+1=p*(p+1)*(copies p)^2 := by
  have hc := copies_pos p hp
  unfold middle
  exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by positivity))
lemma zero_low (p : ℕ) (hp : 2≤p) : (p+1)*lower p=next p+1 := by
  rw [←dimension p hp]
  unfold lower
  ring
lemma one_low (p : ℕ) (hp : 2≤p) : p*upper p=next p := by
  rw [←dimension p hp]
  unfold upper
  ring
lemma zero_mid (p : ℕ) (hp : 2≤p) : upper p+middle p=copies p*(next p+1) := by
  have he : (upper p+middle p)+1=copies p*(next p+1)+1 := by
    rw [add_assoc,middle_add_one p hp,←dimension p hp]
    unfold upper
    ring
  omega
lemma one_mid (p : ℕ) (hp : 2≤p) : lower p+middle p=next p*copies p := by
  have he : (lower p+middle p)+1=next p*copies p+1 := by
    rw [add_assoc,middle_add_one p hp,←dimension p hp]
    unfold lower
    ring
  omega
lemma lower_pos (p : ℕ) : 0<lower p := by unfold lower; omega
lemma upper_pos (p : ℕ) : 0<upper p := by unfold upper; omega
lemma next_two (p : ℕ) (hp : 2≤p) : 2≤next p := by
  exact hp.trans (Nat.le_self_pow (by decide) p)


@[simp] lemma size_zero : size 0=2 := rfl
@[simp] lemma size_succ (n : ℕ) : size (n+1)=next (size n) := rfl
lemma size_two (n : ℕ) : 2 ≤ size n := by
  induction n with
  | zero => simp
  | succ n ih => exact next_two _ ih
lemma size_power (n : ℕ) : size n=2^(7^n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [size_succ,next,ih,←pow_mul,pow_succ]
lemma size_coprime (n : ℕ) : (size n).Coprime (size n+1) :=
  Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
end KirchbergRordam.StandardPrimeMultiplicity
namespace KirchbergRordam.StandardPrimeModel
open StandardPrimeMultiplicity
def Algebra : Type := presentation.Algebra
instance : CStarAlgebra Algebra := inferInstanceAs (CStarAlgebra presentation.Algebra)
instance : Nontrivial Algebra := inferInstanceAs (Nontrivial presentation.Algebra)
instance : TopologicalSpace.SeparableSpace Algebra :=
  inferInstanceAs (TopologicalSpace.SeparableSpace presentation.Algebra)
end KirchbergRordam.StandardPrimeModel

namespace KirchbergRordam.StandardPrimeMultiplicity

def k₀ (p : ℕ) : ℕ := upper p
def k₁ (p : ℕ) : ℕ := lower p
lemma k₀_formula (p : ℕ) (hp : 2≤p) : k₀ p=p^6 := by
  apply Nat.eq_of_mul_eq_mul_left (by omega : 0<p)
  change p*upper p=p*p^6
  rw [one_low p hp]
  simp [next,pow_succ,mul_comm]
lemma next_factors (p : ℕ) (hp : 2≤p) :
    next p=p*k₀ p ∧ next p+1=(p+1)*k₁ p :=
  ⟨(one_low p hp).symm,(zero_low p hp).symm⟩
lemma next_coprime (p : ℕ) : (next p).Coprime (next p+1) :=
  Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
lemma multipliers_coprime (p : ℕ) (hp : 2≤p) : (k₀ p).Coprime (k₁ p) := by
  apply (next_coprime p).of_dvd
  · exact ⟨p,by rw [(next_factors p hp).1,mul_comm]⟩
  · exact ⟨p+1,by rw [(next_factors p hp).2,mul_comm]⟩
lemma copies_ge_fourth (p : ℕ) (hp : 2≤p) : p^4≤copies p := by
  have h : 1≤p-1 := by omega
  calc
    p^4 ≤ p^4+p^2+1 := by omega
    _ = 1*(p^4+p^2+1) := (one_mul _).symm
    _ ≤ (p-1)*(p^4+p^2+1) := Nat.mul_le_mul_right _ h
lemma fourth_large (p : ℕ) (hp : 2≤p) : 2*(p+1)<p^4 := by
  have h2 : 2*p≤p^2 := by nlinarith
  have h3 : 4≤p^2 := by nlinarith
  have h4 : 4*p^2≤p^4 := by nlinarith [sq_nonneg (p^2)]
  nlinarith
lemma multiplier_growth (p : ℕ) (hp : 2≤p) :
    2*p*(p+1)<k₀ p ∧ 2*p*(p+1)<k₁ p := by
  have hc := (fourth_large p hp).trans_le (copies_ge_fourth p hp)
  constructor
  · change 2*p*(p+1)<(p+1)*copies p+1
    nlinarith
  · change 2*p*(p+1)<p*copies p+1
    nlinarith
lemma total_slots (p : ℕ) (hp : 2≤p) :
    lower p+upper p+middle p=k₀ p*k₁ p := by
  have h : (lower p+upper p+middle p)+1=k₀ p*k₁ p+1 := by
    rw [add_assoc,middle_add_one p hp]
    unfold k₀ k₁ lower upper
    ring
  omega
lemma zero_remainder_lt (p : ℕ) (hp : 2≤p) : lower p<next p+1 := by
  have h := lower_pos p
  rw [(next_factors p hp).2]
  change lower p<(p+1)*lower p
  nlinarith
lemma one_remainder_lt (p : ℕ) (hp : 2≤p) : upper p<next p := by
  have h := upper_pos p
  rw [(next_factors p hp).1]
  change upper p<p*upper p
  nlinarith
lemma zero_remainder (p : ℕ) (hp : 2≤p) :
    (k₀ p*k₁ p)%(next p+1)=lower p := by
  have he : k₀ p*k₁ p=lower p+copies p*(next p+1) := by
    rw [←total_slots p hp,add_assoc,zero_mid p hp]
  rw [he,Nat.add_mod]
  simp [Nat.mod_eq_of_lt (zero_remainder_lt p hp)]
lemma one_remainder (p : ℕ) (hp : 2≤p) :
    (k₀ p*k₁ p)%next p=upper p := by
  have he : k₀ p*k₁ p=upper p+next p*copies p := by
    rw [←one_mid p hp]
    exact (total_slots p hp).symm.trans (by omega)
  rw [he,Nat.add_mod]
  simp [Nat.mod_eq_of_lt (one_remainder_lt p hp)]
lemma middle_classical (p : ℕ) (hp : 2≤p) :
    middle p=k₀ p*k₁ p-(k₀ p*k₁ p)%(next p+1)-(k₀ p*k₁ p)%next p := by
  rw [zero_remainder p hp,one_remainder p hp]
  have h := total_slots p hp
  omega
end KirchbergRordam.StandardPrimeMultiplicity
end

end OAI
