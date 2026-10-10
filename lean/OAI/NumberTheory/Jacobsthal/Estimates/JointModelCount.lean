import OAI.NumberTheory.Jacobsthal.Primes.ActualPrimeSelectors
import OAI.NumberTheory.Jacobsthal.Sieve.CoprimePositionSieve

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceMoments
open NumberTheoryLean ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem zero_jointDensity_full_class (P S : Finset ℕ) (hP : ∀ t ∈ P,t.Prime)
    (hz : jointDensity P S = 0) : ∃ t ∈ P,(positionResidues S t).card = t := by
  obtain ⟨t,ht,hzero⟩ := Finset.prod_eq_zero_iff.mp hz
  have htpos : (0 : ℝ) < t := by exact_mod_cast (hP t ht).pos
  have he : ((positionResidues S t).card : ℝ)/(t : ℝ) = 1 := by
    change 1-((positionResidues S t).card : ℝ)/(t : ℝ) = 0 at hzero
    linarith
  refine ⟨t,ht,?_⟩
  exact_mod_cast (div_eq_one_iff_eq htpos.ne').mp he

theorem zero_coprimeJoint (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (p : (ZMod (coprimeModulus w H))ˣ)
    (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t)
    (hz : jointDensity (coprimePrimes w H) S = 0) (m : ℤ) :
    ¬coprimeJoint w H qA delta S m p := by
  obtain ⟨t,ht,hfull⟩ := zero_jointDensity_full_class (coprimePrimes w H) S
    (fun t ht => (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1) hz
  let : NeZero t := ⟨(LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1.ne_zero⟩
  have he : coprimeForbidden w H qA delta S p t ht (hqA t ht) = Finset.univ :=
    forbiddenClasses_full_of_card _ _ _ _ hfull
  intro h
  have hav := (coprimeJoint_avoidance w H qA delta S p hqA m).mp h t ht
  apply hav
  simp only [coprimeForbiddenFamily,dite_eq_left ht,he,Finset.mem_univ]

theorem zero_coprimePositionSurvivors (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (p : (ZMod (coprimeModulus w H))ˣ)
    (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t)
    (hz : jointDensity (coprimePrimes w H) S = 0) (b c : ℝ) :
    coprimePositionSurvivors w H qA delta S p b c = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro m hm
  exact zero_coprimeJoint w H qA delta S p hqA hz m (Finset.mem_filter.mp hm).2

theorem zero_divisorJoint (w : ℝ) (H : ℕ) (C0 : ℤ) (beta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (m : ℤ) (hC0 : Int.gcd C0 (H : ℤ) = 1) (hm : m.natAbs.Coprime H)
    (hz : jointDensity (divisorPrimes w H) S = 0) :
    Finset.univ.filter (divisorJoint w H C0 beta S m) = ∅ := by
  have hc := divisorJoint_card_real w H C0 beta S m hC0 hm
  rw [hz,mul_zero,Nat.cast_eq_zero] at hc
  exact Finset.card_eq_zero.mp hc

end ErdosVarianceMoments

end

section

namespace ErdosVarianceMoments
open ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem unitInterval_eq_modelUnitIntegers (R xi : ℝ) (H : ℕ) (C0 : ℤ) :
    unitIntervalIntegers H (modelLeft R xi (C0 : ℝ)) (modelRight R xi (H : ℝ) (C0 : ℝ)) =
      modelUnitIntegers R xi H C0 := by
  ext m
  simp only [unitIntervalIntegers,modelUnitIntegers,modelIntegers,Finset.mem_filter,Nat.coprime_comm]

theorem joint_model_card (R xi w : ℝ) (H qA : ℕ) (C0 : ℤ)
    (beta delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ) (hC0 : Int.gcd C0 (H : ℤ) = 1) :
    ((modelUniverse R xi w H C0).filter (jointCondition w H C0 qA beta delta S)).card =
      (∑ p : (ZMod (coprimeModulus w H))ˣ,
        (coprimePositionSurvivors w H qA delta S p (modelLeft R xi (C0 : ℝ))
          (modelRight R xi (H : ℝ) (C0 : ℝ))).card)*
        ∏ t ∈ divisorPrimes w H,(t-(positionResidues S t).card) := by
  have hsplit : ((modelUniverse R xi w H C0).filter (jointCondition w H C0 qA beta delta S)).card =
      ∑ m ∈ modelUnitIntegers R xi H C0,
        (Finset.univ.filter (fun s : Pattern w H => jointCondition w H C0 qA beta delta S (m,s))).card := by
    simp only [modelUniverse,Finset.product_eq_sprod,Finset.card_filter,Finset.sum_product]
  rw [hsplit]
  have hc : (∑ m ∈ modelUnitIntegers R xi H C0,
        (Finset.univ.filter (fun s : Pattern w H => jointCondition w H C0 qA beta delta S (m,s))).card) =
      (∑ m ∈ modelUnitIntegers R xi H C0,
        (Finset.univ.filter (coprimeJoint w H qA delta S m)).card)*
        ∏ t ∈ divisorPrimes w H,(t-(positionResidues S t).card) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    exact conditional_pattern_card w H C0 qA beta delta S m hC0 (Finset.mem_filter.mp hm).2
  rw [hc]
  congr 1
  simp only [coprimePositionSurvivors,unitInterval_eq_modelUnitIntegers,Finset.card_filter]
  exact Finset.sum_comm

theorem joint_model_mass (R xi w : ℝ) (H qA : ℕ) (C0 : ℤ)
    (beta delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ) (hC0 : Int.gcd C0 (H : ℤ) = 1) :
    modelMass R xi w H C0 (jointCondition w H C0 qA beta delta S) =
      atomWeight R xi w H C0*((divisorModulus w H : ℝ)*jointDensity (divisorPrimes w H) S)*
        ∑ p : (ZMod (coprimeModulus w H))ˣ,
          ((coprimePositionSurvivors w H qA delta S p (modelLeft R xi (C0 : ℝ))
            (modelRight R xi (H : ℝ) (C0 : ℝ))).card : ℝ) := by
  rw [modelMass_card,joint_model_card R xi w H qA C0 beta delta S hC0,Nat.cast_mul,Nat.cast_sum,
    product_allowed_eq_density (divisorPrimes w H) S (fun t ht =>
      (NumberTheoryLean.LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1)]
  change (_*((divisorModulus w H : ℝ)*jointDensity (divisorPrimes w H) S))*_ = _
  ring

end ErdosVarianceMoments

end

end Erdos970

end OAI
