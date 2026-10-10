import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.StepFactor
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TreeDestinationInjective

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open Finset Classical
variable {S : PrimeSystem} {h ℓ : ℕ}

lemma primeCharge_product (r : S.Residues) (d : ℕ) (b : ℤ) :
    (∏ p : S.Index, S.primeCharge p d b (r p)) =
      Real.exp (kappa * S.cutoffCount d (S.shiftCore (S.restrictCore r) b)) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype S.IsCore]
  have hn : (∏ p : {p : S.Index // ¬ S.IsCore p}, S.primeCharge p.val d b (r p.val)) = 1 := by
    apply prod_eq_one
    intro p _
    simp only [primeCharge, p.property, false_and, ite_false]
  rw [hn, mul_one]
  trans ∏ p : S.CoreIndex,
    Real.exp (if r p.val + (b : ZMod (p.val : ℕ)) = 0 ∧ ¬(p.val : ℕ) ∣ d then kappa else 0)
  · apply prod_congr rfl
    intro p _
    simp only [primeCharge, p.property, true_and]
    by_cases hd : (p.val : ℕ) ∣ d <;>
      by_cases ha : r p.val + (b : ZMod (p.val : ℕ)) = 0 <;>
      simp [hd,ha]
  · rw [← Real.exp_sum]
    congr 1
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    simp only [cutoffCount, shiftCore, restrictCore]
    exact mul_comm _ _

def allPrimeCharges (w : ClosedLine h ℓ) (U : Finset ℤ) (p : S.Index)
    (a : ZMod (p : ℕ)) : ℝ :=
  (∏ i ∈ returnSteps w, S.primeCharge p (w.label i) (w.offset i.castSucc) a) *
   ∏ i ∈ incomingCharges w U, S.primeCharge p (w.label i) (w.offset i.succ) a

lemma allPrimeCharges_nonneg (w : ClosedLine h ℓ) (U : Finset ℤ) (p : S.Index)
    (a : ZMod (p : ℕ)) : 0 ≤ allPrimeCharges w U p a :=
  mul_nonneg (prod_nonneg (fun _ _ => primeCharge_nonneg _ _ _ _))
    (prod_nonneg (fun _ _ => primeCharge_nonneg _ _ _ _))

lemma allPrimeCharges_center (w : ClosedLine h ℓ) (U : Finset ℤ) (p : S.Index)
    (hc : ¬S.IsCore p) (a : ZMod (p : ℕ)) : allPrimeCharges w U p a = 1 := by
  simp only [allPrimeCharges, primeCharge, hc, false_and, ite_false, prod_const_one, mul_one]

def chargeConstant (w : ClosedLine h ℓ) (T : ℝ) (U : Finset ℤ) : ℝ :=
  Real.exp (-kappa * (S.harmonicCore - T * Real.sqrt S.harmonicCore) *
    (((returnSteps w).card : ℝ) + U.card))

theorem cutoff_product_primewise (w : ClosedLine h ℓ) {T : ℝ}
    (cut : S.Cutoffs T) (r : S.Residues) (U : Finset ℤ) (hU : U ⊆ goodOrigins w) :
    S.cutoffProduct w cut (S.restrictCore r) ≤ chargeConstant (S := S) w T U *
      ∏ p : S.Index, allPrimeCharges w U p (r p) := by
  have h := source_cutoff_charges w cut (S.restrictCore r) U hU
  convert h using 1
  congr 1
  simp only [allPrimeCharges, prod_mul_distrib]
  rw [prod_comm, prod_comm (s := (univ : Finset S.Index)) (t := incomingCharges w U)]
  simp_rw [primeCharge_product]
  rw [← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add]
  simp only [← mul_sum, mul_add]

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
