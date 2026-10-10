import OAI.Probability.SignedSweeps.MarginalKernels
import OAI.Probability.SignedSweeps.FiniteProbability

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I] (d : ℕ)

def sweepEndpointProb (A : Finset I) (x y : I → Fin (2 ^ d)) : ℝ :=
  finiteProb (fun p : PhysicalSettings d => ∀ a ∈ A,
    sampleSweep d (physicalSettingsEquiv d p) (x a) = y a)

def switchConstraintProb (i : Fin d) (c : SwitchAddress d i) (A : Finset I)
    (x y : I → Fin (2 ^ d)) : ℝ :=
  finiteProb (fun p : Equiv.Perm (Fin 2) => ∀ a ∈ A,
    pathAddress d i (x a) (y a) = c → p ((positionsEquiv d).symm (x a) i) =
      (positionsEquiv d).symm (y a) i)

omit [Fintype I] [DecidableEq I] in
lemma sweepEndpointProb_eq_product (A : Finset I) (x y : I → Fin (2 ^ d)) :
    sweepEndpointProb d A x y =
      ∏ i : Fin d, ∏ c : SwitchAddress d i, switchConstraintProb d i c A x y := by
  unfold sweepEndpointProb
  have he : finiteProb (fun p : PhysicalSettings d => ∀ a ∈ A,
      sampleSweep d (physicalSettingsEquiv d p) (x a) = y a) =
      finiteProb (fun p : PhysicalSettings d => ∀ i : Fin d, ∀ c : SwitchAddress d i,
        ∀ a ∈ A, pathAddress d i (x a) (y a) = c →
          p i c ((positionsEquiv d).symm (x a) i) = (positionsEquiv d).symm (y a) i) := by
    apply finiteProb_congr
    intro p
    constructor
    · intro h i c a ha hc
      rw [← hc]
      exact (sampleSweep_endpoints_iff d p (x a) (y a)).mp (h a ha) i
    · intro h a ha
      apply (sampleSweep_endpoints_iff d p (x a) (y a)).mpr
      intro i
      exact h i _ a ha rfl
  refine he.trans ((finiteProb_pi_forall (fun i : Fin d => LayerSettings d i)
    (fun i p => ∀ c : SwitchAddress d i, ∀ a ∈ A,
      pathAddress d i (x a) (y a) = c →
        p c ((positionsEquiv d).symm (x a) i) = (positionsEquiv d).symm (y a) i)).trans ?_)
  apply Finset.prod_congr rfl
  intro i _
  exact finiteProb_pi_forall (fun _ : SwitchAddress d i => Equiv.Perm (Fin 2))
    (fun c p => ∀ a ∈ A, pathAddress d i (x a) (y a) = c →
      p ((positionsEquiv d).symm (x a) i) = (positionsEquiv d).symm (y a) i)

omit [Fintype I] in
lemma switchConstraintProb_insert (A : Finset I) (x y : I → Fin (2 ^ d))
    (a : I) (i : Fin d) (c : SwitchAddress d i)
    (hiso : ∀ b ∈ A, pathAddress d i (x a) (y a) ≠ pathAddress d i (x b) (y b)) :
    switchConstraintProb d i c (insert a A) x y =
      (if c = pathAddress d i (x a) (y a) then (1 / 2 : ℝ) else 1) *
        switchConstraintProb d i c A x y := by
  by_cases hc : c = pathAddress d i (x a) (y a)
  · subst c
    have hb : switchConstraintProb d i (pathAddress d i (x a) (y a)) A x y = 1 := by
      calc
        _ = finiteProb (fun _ : Equiv.Perm (Fin 2) => True) := by
          apply finiteProb_congr
          intro p
          constructor
          · intro _; trivial
          · intro _ b hb hab
            exact False.elim (hiso b hb hab.symm)
        _ = 1 := finiteProb_true _
    have ha : switchConstraintProb d i (pathAddress d i (x a) (y a)) (insert a A) x y = 1 / 2 := by
      calc
        _ = finiteProb (fun p : Equiv.Perm (Fin 2) =>
            p ((positionsEquiv d).symm (x a) i) = (positionsEquiv d).symm (y a) i) := by
          apply finiteProb_congr
          intro p
          constructor
          · intro h
            exact h a (Finset.mem_insert_self _ _) rfl
          · intro h b hb hab
            rcases Finset.mem_insert.mp hb with rfl | hb
            · exact h
            · exact False.elim (hiso b hb hab.symm)
        _ = 1 / 2 := finiteProb_bit_switch _ _
    rw [ha, hb, ite_eq_left rfl, mul_one]
  · rw [ite_eq_right hc, one_mul]
    apply finiteProb_congr
    intro p
    constructor
    · intro h b hb
      exact h b (Finset.mem_insert_of_mem hb)
    · intro h b hb hab
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact False.elim (hc hab.symm)
      · exact h b hb hab

omit [Fintype I] in
theorem sweepEndpointProb_insert_isolated (A : Finset I) (x y : I → Fin (2 ^ d))
    (a : I)
    (hiso : ∀ b ∈ A, ∀ i : Fin d,
      pathAddress d i (x a) (y a) ≠ pathAddress d i (x b) (y b)) :
    sweepEndpointProb d (insert a A) x y = ((2 ^ d : ℕ) : ℝ)⁻¹ * sweepEndpointProb d A x y := by
  rw [sweepEndpointProb_eq_product, sweepEndpointProb_eq_product]
  have hi (i : Fin d) :
      (∏ c : SwitchAddress d i, switchConstraintProb d i c (insert a A) x y) =
        (1 / 2 : ℝ) * ∏ c : SwitchAddress d i, switchConstraintProb d i c A x y := by
    simp_rw [switchConstraintProb_insert d A x y a i _ (fun b hb => hiso b hb i)]
    rw [Finset.prod_mul_distrib]
    simp
  simp_rw [hi]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  simp only [one_div, inv_pow, Nat.cast_pow, Nat.cast_ofNat]

def normalizedEndpointProb (A : Finset I) (x y : I → Fin (2 ^ d)) : ℝ :=
  (2 ^ d : ℕ) ^ A.card * sweepEndpointProb d A x y

omit [Fintype I] in
lemma normalizedEndpointProb_insert_isolated (A : Finset I) (x y : I → Fin (2 ^ d))
    (a : I) (ha : a ∉ A)
    (hiso : ∀ b ∈ A, ∀ i : Fin d,
      pathAddress d i (x a) (y a) ≠ pathAddress d i (x b) (y b)) :
    normalizedEndpointProb d (insert a A) x y = normalizedEndpointProb d A x y := by
  unfold normalizedEndpointProb
  rw [Finset.card_insert_of_notMem ha, pow_succ, sweepEndpointProb_insert_isolated d A x y a hiso]
  have hn : ((2 ^ d : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

def subsetEndpointKernel (A : Finset I) (x y : InjectiveTuple I (2 ^ d)) : ℝ :=
  ((2 ^ d : ℕ) ^ Fintype.card I : ℝ)⁻¹ * normalizedEndpointProb d A x y

omit [DecidableEq I] in
lemma subsetEndpointKernel_nonneg (A : Finset I) (x y : InjectiveTuple I (2 ^ d)) :
    0 ≤ subsetEndpointKernel d A x y := by
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _))
    (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (finiteProb_nonneg _))

omit [DecidableEq I] in
lemma subsetEndpointKernel_full (x y : InjectiveTuple I (2 ^ d)) :
    subsetEndpointKernel d Finset.univ x y = sweepEndpointProb d Finset.univ x y := by
  unfold subsetEndpointKernel normalizedEndpointProb
  rw [Finset.card_univ, ← mul_assoc, inv_mul_cancel₀, one_mul]
  positivity

theorem sweep_differenceKernel_vanishes_of_isolate
    (x y : InjectiveTuple I (2 ^ d)) (a : I)
    (hiso : ∀ b, ¬(endpointEncounter d x y).Adj a b) :
    differenceKernel (subsetEndpointKernel d) x y = 0 := by
  apply differenceKernel_vanishes_of_isolate _ x y a
  intro A ha
  unfold subsetEndpointKernel
  rw [normalizedEndpointProb_insert_isolated d A x y a ha]
  intro b hb i hab
  apply hiso b
  exact ⟨fun hab => ha (hab ▸ hb), i, hab⟩

end SignedSweeps
end

end OAI
