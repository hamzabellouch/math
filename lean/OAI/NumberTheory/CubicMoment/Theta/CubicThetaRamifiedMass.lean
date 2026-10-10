import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoefficientMass
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaUnitCount

namespace OAI

/-! The exact six-unit multiplicity in the squared theta coefficients.
The order congruent to one has precisely the two real units. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
private instance : Finite Eisensteinˣ :=
  Nat.finite_of_card_ne_zero (by rw [eisenstein_units_card]; norm_num)
private instance : Fintype Eisensteinˣ := Fintype.ofFinite _

def cubicThetaRamifiedMass (σ : ℝ) (u : Eisensteinˣ) (k : ℕ) : ℝ :=
  (if k%3=0 ∧ 3 ≤ k then 1
   else if k%3=1 ∧ ((u:Eisenstein)=1 ∨ (u:Eisenstein)=-1) then 1 else 0) *
    3^(8-2*((k/3:ℕ):ℝ)-(k:ℝ)*σ)

lemma cubicTheta_real_unit_sum (x : ℝ) :
    (∑ u : Eisensteinˣ, if (u:Eisenstein)=1 ∨ (u:Eisenstein)=-1 then x else 0)=2*x := by
  have hne : (1:Eisensteinˣ) ≠ -1 := by
    intro h
    have he := congrArg (fun u : Eisensteinˣ => (u:Eisenstein)) h
    norm_num at he
  have he (u : Eisensteinˣ) :
      ((u:Eisenstein)=1 ∨ (u:Eisenstein)=-1) ↔ (u=1 ∨ u=-1) := by
    constructor
    · exact Or.imp (fun h => Units.ext h) (fun h => Units.ext h)
    · rintro (rfl|rfl) <;> simp
  have hf (u : Eisensteinˣ) :
      (if u=1 ∨ u=-1 then x else 0) =
        (if u=1 then x else 0)+(if u=-1 then x else 0) := by
    by_cases h1 : u=1 <;> by_cases hm : u=-1 <;> simp_all
  simp_rw [he,hf]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  ring

lemma cubicThetaRamifiedMass_unit_sum (σ : ℝ) (k : ℕ) :
    (∑' u : Eisensteinˣ, cubicThetaRamifiedMass σ u k) =
      (if k%3=0 ∧ 3 ≤ k then 6 else if k%3=1 then 2 else 0) *
        3^(8-2*((k/3:ℕ):ℝ)-(k:ℝ)*σ) := by
  rw [tsum_fintype]
  have hcard : Fintype.card Eisensteinˣ = 6 := by
    rw [←Nat.card_eq_fintype_card,eisenstein_units_card]
  by_cases h0 : k%3=0 ∧ 3 ≤ k
  · simp only [cubicThetaRamifiedMass,ite_eq_left h0,one_mul,Finset.sum_const,
      Finset.card_univ,nsmul_eq_mul,hcard,Nat.cast_ofNat]
  · simp only [cubicThetaRamifiedMass,ite_eq_right h0]
    by_cases h1 : k%3=1
    · simp only [h1,true_and,ite_true]
      simpa only [ite_mul,one_mul,zero_mul] using
        cubicTheta_real_unit_sum (3^(8-2*((k/3:ℕ):ℝ)-(k:ℝ)*σ))
    · simp only [h1,false_and,ite_false,zero_mul,Finset.sum_const_zero]

end CubicFirstMoment

end

end OAI
