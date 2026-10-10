import OAI.NumberTheory.Ostmann.Construction.ConstituentCharacterCoefficient
import OAI.NumberTheory.Ostmann.Construction.ConstituentUnweighted
import OAI.NumberTheory.Ostmann.Construction.FiniteMatchedPrior

namespace OAI

/-! # The original priors in each matched character correlation -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

noncomputable def constituentCharacterCore {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D) : ℂ := by
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  letI : ∀ h, Fact (a.1 h : ℕ).Prime := fun h => ⟨hP _ (a.1 h).property⟩
  letI : ∀ y, Fact (u y : ℕ).Prime := fun y => ⟨hP _ (u y).property⟩
  exact constituentUnweightedTransferWeight role size n P childBound pivotBound ranges leaf hist u M a *
    retainedCharacterBranch (fun h => (a.1 h : ℕ)) (fun y => (u y : ℕ))
      (fun h => χ (copyScheduleOrigin n h.val)) (fun y => χ (copyScheduleOrigin n y.val))
      (scheduledRetainedGraph ρ initialCompleteGraph pivot n)
      (fun h => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
        n (hist a.2) h.val (a.1 h))
      (fun y => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
        n (hist a.2) y.val (u y)) M

section

variable {I D : Type*} [Fintype I]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
variable (Q : (Σ i, Fin (size i)) → Finset ℕ)
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
variable (center : ∀ p : ℕ, ZMod p)
variable (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)

theorem constituentCharacterCoefficient_factor
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D) :
    constituentCharacterCoefficient role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist u M a =
    ((∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (a.1 h) : ℝ) : ℂ) *
      constituentCharacterCore role size χ κ pivot n P hP childBound pivotBound ranges leaf hist u M a := by
  unfold constituentCharacterCoefficient constituentCharacterCore
  rw [constituentTransferWeight_eq_prior_mul]
  ring

theorem constituent_matched_character_normalization
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n))
    (d d' : D) (X : ℝ) (hX : X ≠ 0) :
    let μ := fun l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P =>
      ∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (l h)
    let G := fun l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P =>
      constituentCharacterCore role size χ κ pivot n P hP childBound pivotBound ranges leaf hist u M (l, d) *
        conj (constituentCharacterCore role size χ κ pivot n P hP
          childBound pivotBound ranges leaf hist u M (l ∘ e.symm, d'))
    (∑ l, constituentCharacterCoefficient role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist u M (l, d) *
      conj (constituentCharacterCoefficient role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist u M (l ∘ e.symm, d'))) =
      (((∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
        (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹) * X⁻¹ : ℝ) : ℂ) *
      ∑ l, (μ l : ℂ) * ((X / (∏ h, (l h : ℝ)) : ℝ) : ℂ) *
        ((∏ h, if (l h : ℕ) ∈ Q (copyScheduleOrigin n (e h).val) then (1 : ℝ) else 0) : ℂ) * G l := by
  dsimp only
  let μ := fun l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P =>
    ∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (l h)
  let G := fun l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P =>
    constituentCharacterCore role size χ κ pivot n P hP childBound pivotBound ranges leaf hist u M (l, d) *
      conj (constituentCharacterCore role size χ κ pivot n P hP
        childBound pivotBound ranges leaf hist u M (l ∘ e.symm, d'))
  calc
    _ = ∑ l, (μ l : ℂ) *
        (∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (l (e.symm h)) : ℝ) * G l := by
      apply Finset.sum_congr rfl
      intro l _
      rw [constituentCharacterCoefficient_factor, constituentCharacterCoefficient_factor]
      simp only [map_mul, Complex.conj_ofReal, Function.comp_apply]
      dsimp only [μ, G]
      ring
    _ = _ := by
      have ht := finite_matched_harmonic_correlation_eq
        P (fun h => Q (copyScheduleOrigin n h.val)) e.symm μ G X hX
      simp only [Equiv.symm_symm] at ht
      convert ht using 1
      · with_reducible exact finite_enumeration_sum _ _ _
      · congr 1
        with_reducible exact finite_enumeration_sum _ _ _

end

end Ostmann

end OAI
