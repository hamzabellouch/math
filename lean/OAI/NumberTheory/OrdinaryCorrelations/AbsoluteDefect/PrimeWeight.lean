import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.AdmissibleFacts

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff

namespace OrdinaryAnalyticCentering
open Finset OrdinaryCorrelations OrdinaryTwistWidth OrdinaryAnalyticCutoff
noncomputable def primeWeight (B:ℝ) (p:ℕ) : ℝ := if p∈core B then A/p else (p:ℝ)⁻¹
lemma primeWeight_nonneg (B:ℝ) (p:ℕ) : 0≤primeWeight B p := by
  have hA:0<A:=Real.exp_pos _
  unfold primeWeight
  split_ifs <;> positivity
lemma divisorWeight_pos (B:ℝ) (u:ℕ) : 0<divisorWeight B u :=
  pow_pos (Real.exp_pos _) _
lemma count_by_primeFactors (B:ℝ) (u:ℕ) (hu:0<u) :
    (core B).filter (fun p=>p∣u)=u.primeFactors.filter (fun p=>p∈core B) := by
  ext p
  simp only [mem_filter]
  constructor
  · rintro ⟨hp,hpu⟩
    exact ⟨Nat.mem_primeFactors.mpr ⟨core_prime B hp,hpu,hu.ne'⟩,hp⟩
  · rintro ⟨hp,hpc⟩
    exact ⟨hpc,(Nat.mem_primeFactors.mp hp).2.1⟩
lemma product_primeWeight (B:ℝ) (u:ℕ) (hu:0<u) (hp:(∏p∈u.primeFactors,p)=u) :
    (∏p∈u.primeFactors,primeWeight B p)=divisorWeight B u/u := by
  have he : (∏p∈u.primeFactors,primeWeight B p)=
      (∏p∈u.primeFactors,if p∈core B then A else 1)/(∏p∈u.primeFactors,(p:ℝ)) := by
    rw [←prod_div_distrib]
    apply prod_congr rfl
    intro p hp
    unfold primeWeight
    split_ifs <;> simp [one_div]
  rw [he,prod_ite,prod_const,prod_const_one,mul_one,←Nat.cast_prod,hp]
  unfold divisorWeight primeCount
  rw [count_by_primeFactors B u hu]

lemma euler_product (B:ℝ) :
    (∑R∈(core B∪center B).powerset,∏p∈R,primeWeight B p)=L₀ B := by
  rw [←prod_one_add,prod_union (core_center_disjoint B)]
  unfold L₀
  congr 1
  · apply prod_congr rfl
    intro p hp
    simp only [primeWeight,ite_eq_left hp]
  · apply prod_congr rfl
    intro p hp
    have hpc : p∉core B := by
      intro hpc;exact disjoint_left.mp (core_center_disjoint B) hpc hp
    simp only [primeWeight,ite_eq_right hpc]

lemma retained_mass {B C₀ τ H:ℝ} {D:Finset ℕ} (hD:Admissible B C₀ τ H D) :
    (∑u∈retainedSet B D,divisorWeight B u/(u:ℝ))≤L₀ B := by
  have hinj : Set.InjOn Nat.primeFactors (retainedSet B D : Set ℕ) := by
    intro u hu v hv he
    have h1:=(retained_properties hD hu).2.2.2
    have h2:=(retained_properties hD hv).2.2.2
    rw [←h1,←h2,he]
  have hsub : (retainedSet B D).image Nat.primeFactors⊆(core B∪center B).powerset := by
    intro R hR
    obtain ⟨u,hu,rfl⟩:=mem_image.mp hR
    exact mem_powerset.mpr (retained_properties hD hu).2.1
  calc
    _ = ∑R∈(retainedSet B D).image Nat.primeFactors,∏p∈R,primeWeight B p := by
      rw [sum_image hinj]
      apply sum_congr rfl
      intro u hu
      exact (product_primeWeight B u (retained_properties hD hu).1 (retained_properties hD hu).2.2.2).symm
    _ ≤∑R∈(core B∪center B).powerset,∏p∈R,primeWeight B p :=
      sum_le_sum_of_subset_of_nonneg hsub (fun R hR hnR=>prod_nonneg (fun p hp=>primeWeight_nonneg B p))
    _ = _ := euler_product B
lemma L₀_nonneg (B:ℝ) : 0≤L₀ B := by
  rw [←euler_product]
  exact sum_nonneg (fun R hR=>prod_nonneg (fun p hp=>primeWeight_nonneg B p))
end OrdinaryAnalyticCentering

end

end OAI
