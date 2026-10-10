import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SubtreeUnionWeightNonneg

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

def fixedCharges (w : ClosedLine h ℓ) (U : Finset ℤ) (a : S.FixedResidues w) : ℝ :=
  ∏ p : S.FixedIndex w, allPrimeCharges w U p.val (a p)

def freeCoreCharges (w : ClosedLine h ℓ) (U : Finset ℤ) (b : S.FreeCoreResidues w) : ℝ :=
  ∏ p : S.FreeCoreIndex w, allPrimeCharges w U p.val.val (b p)

lemma fixedCharges_nonneg (w : ClosedLine h ℓ) (U : Finset ℤ) (a : S.FixedResidues w) :
    0 ≤ fixedCharges w U a := prod_nonneg (fun _ _ => allPrimeCharges_nonneg _ _ _ _)

lemma freeCoreCharges_nonneg (w : ClosedLine h ℓ) (U : Finset ℤ) (b : S.FreeCoreResidues w) :
    0 ≤ freeCoreCharges w U b := prod_nonneg (fun _ _ => allPrimeCharges_nonneg _ _ _ _)

lemma splitCutoff_le (w : ClosedLine h ℓ) {T : ℝ} (cut : S.Cutoffs T)
    (U : Finset ℤ) (hU : U ⊆ goodOrigins w) (a : S.FixedResidues w)
    (b : S.FreeCoreResidues w) :
    splitCutoff w cut a b ≤ chargeConstant (S := S) w T U *
      fixedCharges w U a * freeCoreCharges w U b := by
  let c : S.FreeCenterResidues w := fun _ => 0
  have hh := cutoff_product_primewise w cut ((S.splitResidues w).symm (a,(b,c))) U hU
  rw [restrictCore_merge, product_merge] at hh
  have hc : (∏ p : S.FreeCenterIndex w, allPrimeCharges w U p.val.val (c p)) = 1 := by
    exact prod_eq_one (fun p _ => allPrimeCharges_center w U p.val.val p.property _)
  rw [hc, mul_one] at hh
  simpa only [splitCutoff, fixedCharges, freeCoreCharges, mul_assoc] using hh

lemma localWithList_core_nonneg (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (p : S.Index) (hc : S.IsCore p) (a : ZMod (p : ℕ)) :
    0 ≤ localWithList w 𝔏 p a :=
  mul_nonneg (S.core_primeFactor_nonneg w p hc a) (listLocal_nonneg w 𝔏 p a)

lemma fixed_charged_product (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (U : Finset ℤ) (a : S.FixedResidues w) :
    |fixedProduct w 𝔏 a| * fixedCharges w U a =
      ∏ p : S.FixedIndex w, |localWithList w 𝔏 p.val (a p)| * allPrimeCharges w U p.val (a p) := by
  rw [fixedProduct, abs_prod, fixedCharges, prod_mul_distrib]

lemma freeCore_charged_mean (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (U : Finset ℤ) :
    avg (fun b => freeCoreCharges w U b * freeCoreProduct w 𝔏 b) =
      ∏ p : S.FreeCoreIndex w, avg (fun a =>
        |localWithList w 𝔏 p.val.val a| * allPrimeCharges w U p.val.val a) := by
  have hh (b : S.FreeCoreResidues w) : freeCoreCharges w U b * freeCoreProduct w 𝔏 b =
      ∏ p : S.FreeCoreIndex w,
        |localWithList w 𝔏 p.val.val (b p)| * allPrimeCharges w U p.val.val (b p) := by
    rw [freeCoreCharges, freeCoreProduct, ← prod_mul_distrib]
    apply prod_congr rfl
    intro p _
    rw [abs_of_nonneg (localWithList_core_nonneg w 𝔏 p.val.val p.property _), mul_comm]
  simp_rw [hh]
  simp only [avg, Fintype.card_pi, Nat.cast_prod]
  conv_rhs => rw [prod_mul_distrib]
  congr 1
  · rw [prod_inv_distrib]
  · exact (Fintype.prod_sum (fun (p : S.FreeCoreIndex w) (a : ZMod (p.val.val : ℕ)) =>
      |localWithList w 𝔏 p.val.val a| * allPrimeCharges w U p.val.val a)).symm

lemma fixed_group_charged_mean_le (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (U : Finset ℤ) (group : S.FixedResidues w → Prop)
    (E : S.FixedIndex w → Finset (Fin ℓ))
    (hgroup : ∀ a, group a → ∀ p : S.FixedIndex w, litEdges w p.val (a p) = E p) :
    avg (fun a => if group a then |fixedProduct w 𝔏 a| * fixedCharges w U a else 0) ≤
      ∏ p : S.FixedIndex w, avg (recordPrime w 𝔏 U p.val (E p)) := by
  calc
    _ ≤ avg (fun a : S.FixedResidues w => ∏ p : S.FixedIndex w,
        recordPrime w 𝔏 U p.val (E p) (a p)) := by
      apply avg_mono
      intro a
      split_ifs with ha
      · rw [fixed_charged_product]
        apply le_of_eq
        apply prod_congr rfl
        intro p _
        rw [recordPrime, ite_eq_left (hgroup a ha p)]
      · exact prod_nonneg (fun p _ => recordPrime_nonneg w 𝔏 U p.val (E p) (a p))
    _ = _ := by
      simp only [avg, Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib,
        ← Fintype.prod_sum, prod_mul_distrib]

theorem assignedKernelIntegral_le_prime_means (w : ClosedLine h ℓ) {T : ℝ}
    (cut : S.Cutoffs T) (𝔏 : List (AttachedSpec w D L)) (U : Finset ℤ)
    (hU : U ⊆ goodOrigins w) (group : S.FixedResidues w → Prop)
    (E : S.FixedIndex w → Finset (Fin ℓ))
    (hgroup : ∀ a, group a → ∀ p : S.FixedIndex w, litEdges w p.val (a p) = E p) :
    assignedKernelIntegral w cut 𝔏 group ≤
      chargeConstant (S := S) w T U *
      (∏ p : S.FreeCenterIndex w, |avg (localWithList w 𝔏 p.val.val)|) *
      (∏ p : S.FixedIndex w, avg (recordPrime w 𝔏 U p.val (E p))) *
      ∏ p : S.FreeCoreIndex w, avg (fun a =>
        |localWithList w 𝔏 p.val.val a| * allPrimeCharges w U p.val.val a) := by
  have hM : 0 ≤ chargeConstant (S := S) w T U := (Real.exp_pos _).le
  rw [assignedKernelIntegral_eq]
  have hh := assignedIntegral_le_product group (splitCutoff w cut)
    (fixedProduct w 𝔏) (freeCoreProduct w 𝔏) (freeCenterProduct w 𝔏)
    (chargeConstant (S := S) w T U) (fixedCharges w U) (freeCoreCharges w U)
    (fun a b => cutoffProduct_nonneg S w cut _) (freeCoreProduct_nonneg w 𝔏)
    hM (fixedCharges_nonneg w U) (freeCoreCharges_nonneg w U)
    (fun a _ b => splitCutoff_le w cut U hU a b)
  rw [freeCenter_mean, abs_prod, freeCore_charged_mean] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul_of_nonneg_left (fixed_group_charged_mean_le w 𝔏 U group E hgroup)
      (mul_nonneg hM (prod_nonneg (fun _ _ => abs_nonneg _)))
  · exact prod_nonneg (fun p _ => avg_nonneg (fun a =>
      mul_nonneg (abs_nonneg _) (allPrimeCharges_nonneg w U p.val.val a)))

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
