import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TreeOccurrencesEmptyOfFree

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

lemma card_treeVertices_le (w : ClosedLine h ℓ) : (treeVertices w).card ≤ ℓ+1 := by
  exact (card_image_le).trans_eq (by simp)

lemma background_numerator_le (w : ClosedLine h ℓ) (U : Finset ℤ)
    (hU : U ⊆ goodOrigins w) (p : S.Index) :
    treeDefect w p - (if S.IsCore p then betaC * (Real.exp kappa - 1) * U.card else 0) ≤ ℓ+1 := by
  rw [← charged_correction_sum w U
    (fun v hv => (good_origin_data w (hU hv)).1)
    (fun v hv => (good_origin_data w (hU hv)).2.2.1) p]
  calc
    _ ≤ ∑ _v ∈ treeVertices w, (1 : ℝ) := by
      apply sum_le_sum
      intro v hv
      have hb := beta_nonneg p
      have : 0 ≤ S.beta p ^ w.children v *
          (if S.IsCore p ∧ v ∈ U then Real.exp kappa else 1) := by
        split_ifs <;> positivity
      linarith
    _ = ((treeVertices w).card : ℝ) := by simp
    _ ≤ ℓ+1 := by exact_mod_cast card_treeVertices_le w

lemma backgroundExponent_lower (w : ClosedLine h ℓ) (U : Finset ℤ)
    (hU : U ⊆ goodOrigins w) (p : S.Index) :
    -((ℓ : ℝ)+1) / (p : ℝ) ≤ backgroundExponent w U p := by
  exact div_le_div_of_nonneg_right (neg_le_neg (background_numerator_le w U hU p))
    (Nat.cast_nonneg _)

lemma backgroundExponent_nonpos (w : ClosedLine h ℓ) (U : Finset ℤ)
    (hU : U ⊆ goodOrigins w) (p : S.Index) : backgroundExponent w U p ≤ 0 := by
  apply div_nonpos_of_nonpos_of_nonneg
  · exact neg_nonpos.mpr (background_numerator_nonneg w U
      (fun v hv => (good_origin_data w (hU hv)).1)
      (fun v hv => (good_origin_data w (hU hv)).2.2.1) p)
  · exact Nat.cast_nonneg _

def UsedPrime (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L)) (p : S.Index) : Prop :=
  (treeOccurrences w p).Nonempty ∨ (p : ℕ) ∈ listSupport w 𝔏

def OmittedPrime (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L)) (p : S.Index) : Prop :=
  UsedPrime w 𝔏 p ∨ IsCollision w p

def tokenPrimeFactor (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (E : S.Index → Finset (Fin ℓ)) (p : S.Index) : ℝ :=
  if (treeOccurrences w p).Nonempty then
    (if S.IsFixed w p then fixedTreeWeight w p (E p) else freeTreeWeight w 𝔏 p) / (p : ℝ)
  else if (p : ℕ) ∈ listSupport w 𝔏 then (p : ℝ)⁻¹ else 1

lemma tokenPrimeFactor_nonneg (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (E : S.Index → Finset (Fin ℓ)) (p : S.Index) : 0 ≤ tokenPrimeFactor w 𝔏 E p := by
  unfold tokenPrimeFactor
  split_ifs
  · exact div_nonneg (fixedTreeWeight_nonneg w p _) (Nat.cast_nonneg _)
  · exact div_nonneg (freeTreeWeight_nonneg w 𝔏 p) (Nat.cast_nonneg _)
  · positivity
  · norm_num

lemma primeBound_factorization (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (U : Finset ℤ) (E : S.Index → Finset (Fin ℓ)) (p : S.Index) :
    primeBound w 𝔏 U E p = tokenPrimeFactor w 𝔏 E p *
      Real.exp (if OmittedPrime w 𝔏 p then 0 else backgroundExponent w U p) := by
  unfold primeBound tokenPrimeFactor outsideTreeBound OmittedPrime UsedPrime
  split_ifs <;> simp_all

def restorationError (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L)) : ℝ :=
  ((ℓ : ℝ)+1) * ∑ p : S.Index, if OmittedPrime w 𝔏 p then (p : ℝ)⁻¹ else 0

lemma restorationError_nonneg (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L)) :
    0 ≤ restorationError w 𝔏 := by
  unfold restorationError
  positivity

lemma background_sum_restored (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (U : Finset ℤ) (hU : U ⊆ goodOrigins w) :
    (∑ p : S.Index, if OmittedPrime w 𝔏 p then 0 else backgroundExponent w U p) ≤
      (∑ p : S.Index, backgroundExponent w U p) + restorationError w 𝔏 := by
  rw [restorationError, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro p hp
  by_cases ho : OmittedPrime w 𝔏 p
  · simp only [ho, ite_true]
    have hh := backgroundExponent_lower w U hU p
    simp only [div_eq_mul_inv, neg_mul] at hh
    linarith
  · simp only [ho, ite_false, mul_zero, add_zero, le_refl]

theorem all_prime_bounds_restored (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (U : Finset ℤ) (hU : U ⊆ goodOrigins w) (E : S.Index → Finset (Fin ℓ)) :
    (∏ p : S.Index, primeBound w 𝔏 U E p) ≤
      (∏ p : S.Index, tokenPrimeFactor w 𝔏 E p) *
        Real.exp ((∑ p : S.Index, backgroundExponent w U p) + restorationError w 𝔏) := by
  simp_rw [primeBound_factorization]
  rw [prod_mul_distrib, ← Real.exp_sum]
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (background_sum_restored w 𝔏 U hU))
    (prod_nonneg (fun p _ => tokenPrimeFactor_nonneg w 𝔏 E p))

abbrev CenterIndex (S : PrimeSystem) := {p : S.Index // ¬S.IsCore p}
def harmonicCenter (S : PrimeSystem) : ℝ := ∑ p : S.CenterIndex, (p.val : ℝ)⁻¹

def bandDefect (w : ClosedLine h ℓ) (β : ℝ) : ℝ :=
  ∑ v ∈ treeVertices w, (1 - β ^ w.children v)

lemma sum_backgroundExponent (w : ClosedLine h ℓ) (U : Finset ℤ) :
    (∑ p : S.Index, backgroundExponent w U p) =
      -S.harmonicCore * bandDefect w betaC - S.harmonicCenter * bandDefect w betaZ +
        S.harmonicCore * betaC * (Real.exp kappa - 1) * U.card := by
  rw [← Fintype.sum_subtype_add_sum_subtype (S.IsCore)]
  have hC (p : S.CoreIndex) : backgroundExponent w U p.val =
      (-(bandDefect w betaC) + betaC * (Real.exp kappa - 1) * U.card) * (p.val : ℝ)⁻¹ := by
    simp only [backgroundExponent, treeDefect,
      beta, amplitude, p.property, ite_true, betaC, bandDefect]
    ring
  have hZ (p : S.CenterIndex) : backgroundExponent w U p.val =
      -(bandDefect w betaZ) * (p.val : ℝ)⁻¹ := by
    simp only [backgroundExponent, p.property, ite_false, sub_zero,
      treeDefect, beta_eq_center p.val p.property, bandDefect]
    ring
  simp_rw [hC, hZ]
  rw [← mul_sum, ← mul_sum]
  change _ * S.harmonicCore + _ * S.harmonicCenter = _
  ring

theorem assignedKernelIntegral_restored (w : ClosedLine h ℓ) (hh : 0 < h)
    {T : ℝ} (cut : S.Cutoffs T) (𝔏 : List (AttachedSpec w D L))
    (E : S.Index → Finset (Fin ℓ)) (hE : ∀ p, E p ⊆ treeOccurrences w p)
    (group : S.FixedResidues w → Prop)
    (hgroup : ∀ a, group a → ∀ p : S.FixedIndex w, litEdges w p.val (a p) = E p.val)
    (hlarge : ∀ p : S.Index, 2 * (ℓ+1) ≤ (p : ℕ)) :
    assignedKernelIntegral w cut 𝔏 group ≤
      chargeConstant (S := S) w T (recordU w E) *
      Real.exp (-S.harmonicCore * bandDefect w betaC - S.harmonicCenter * bandDefect w betaZ +
        S.harmonicCore * betaC * (Real.exp kappa - 1) * (recordU w E).card +
        restorationError w 𝔏) * ∏ p : S.Index, tokenPrimeFactor w 𝔏 E p := by
  apply (assignedKernelIntegral_le_all_prime_bounds w hh cut 𝔏 E hE group hgroup hlarge).trans
  have hh' := mul_le_mul_of_nonneg_left
    (all_prime_bounds_restored w 𝔏 (recordU w E) (recordU_subset w E) E)
    ((Real.exp_pos _).le : 0 ≤ chargeConstant (S := S) w T (recordU w E))
  rw [sum_backgroundExponent] at hh'
  simpa only [chargeConstant, mul_assoc, mul_left_comm, mul_comm] using hh'

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
