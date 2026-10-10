import OAI.Combinatorics.ContingencyTables.Transport.FiniteDependentLaw
import OAI.Combinatorics.ContingencyTables.Transport.RationalWalkApproximation

namespace OAI

/-! # Total variation for state-dependent finite completion laws -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators
open ResidualMixture

variable {X : Type*} {Y : X → Type*} [Fintype X] [∀ x,Fintype (Y x)]

theorem variation_dependentJoint (p q : RationalLaw X)
    (K L : (x : X) → RationalLaw (Y x)) :
    variation (dependentJointLaw p K) (dependentJointLaw q L) ≤
      variation p q+∑ x,p.mass x*variation (K x) (L x) := by
  have hpoint (x : X) (y : Y x) :
      |p.mass x*(K x).mass y-q.mass x*(L x).mass y| ≤
      p.mass x*|(K x).mass y-(L x).mass y|+|p.mass x-q.mass x| *(L x).mass y := by
    calc
      _ = |p.mass x*((K x).mass y-(L x).mass y)+(p.mass x-q.mass x)*(L x).mass y| := by
        congr 1
        ring
      _ ≤ |p.mass x*((K x).mass y-(L x).mass y)|+|(p.mass x-q.mass x)*(L x).mass y| :=
        abs_add_le _ _
      _ = _ := by
        rw [abs_mul,abs_mul,abs_of_nonneg (p.nonnegative x),abs_of_nonneg ((L x).nonnegative y)]
  have hsum := Finset.sum_le_sum (fun x (_ : x∈Finset.univ) =>
    Finset.sum_le_sum (fun y (_ : y∈Finset.univ) => hpoint x y))
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,(L _).total,mul_one] at hsum
  unfold variation
  change (∑ a : (x : X) × Y x,|p.mass a.1*(K a.1).mass a.2-q.mass a.1*(L a.1).mass a.2|)/2 ≤ _
  rw [Fintype.sum_sigma]
  have hh := div_le_div_of_nonneg_right hsum (show (0:ℚ) ≤ 2 by norm_num)
  convert hh using 1
  simp only [add_div,Finset.sum_div,mul_div_assoc]
  ring

theorem variation_dependentJoint_uniform (p q : RationalLaw X)
    (K L : (x : X) → RationalLaw (Y x)) (η : ℚ)
    (hη : ∀ x,variation (K x) (L x) ≤ η) :
    variation (dependentJointLaw p K) (dependentJointLaw q L) ≤ variation p q+η := by
  calc
    _ ≤ variation p q+∑ x,p.mass x*variation (K x) (L x) := variation_dependentJoint p q K L
    _ ≤ variation p q+∑ x,p.mass x*η := by
      apply add_le_add_right
      exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hη x) (p.nonnegative x))
    _ = _ := by rw [←Finset.sum_mul,p.total,one_mul]

end ContingencyTables.FirstSuccess

end OAI
