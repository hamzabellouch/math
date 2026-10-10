import OAI.NumberTheory.Ostmann.Construction.ConstituentMatchingEnergy
import OAI.NumberTheory.Ostmann.Arithmetic.SupportedMatchedHistoryEnergy
import OAI.NumberTheory.Ostmann.Construction.HarmonicTupleProductBound

namespace OAI

/-! # The diagonal uses the actual supported product lower bound -/
namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- This holds for every matching, including the bad component-rich ones.
Its small factor is the exact counterpart harmonic normalizer and product
lower endpoint. The retained square has its original H prime law. -/
theorem constituent_matching_energy_on_product {I D R : Type*}
    [Fintype I] [Fintype D] [Fintype R]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (hκ : ∀ i p, ‖κ i p‖ ≤ 1)
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (hhist : Function.Injective hist) (root : D → R)
    (hroot : ∀ d d', root d = root d' → frequencyRoot n (hist d) = frequencyRoot n (hist d'))
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n))
    (lower : ℝ) (hlower : 0 < lower)
    (hproduct : ∀ (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) (d : D),
      fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (scheduledInsertedAtoms role n M
          (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
          (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist d) ≠ 0 →
      lower ≤ ∏ h, (l h : ℝ)) :
    ‖∑ d : D, ∑ d' : D, if root d = root d' then
      ∑ l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P,
        constituentCharacterCoefficient role size χ κ pivot n P hP Q
          childBound pivotBound ranges leaf hist u M (l, d) *
        conj (constituentCharacterCoefficient role size χ κ pivot n P hP Q
          childBound pivotBound ranges leaf hist u M (l ∘ e.symm, d')) else 0‖ ≤
      ((∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
          (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹) * lower⁻¹) *
      ∑ d : D, ∑ l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P,
        (∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (l h)) *
        ‖fullAtomTransferWeight role childBound pivotBound ranges leaf n
          (scheduledInsertedAtoms role n M
            (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
            (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist d)‖ ^ 2 := by
  let H := CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n
  let μ := fun l : H → P => ∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (l h)
  let A₀ := (∏ h : H, (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹) * lower⁻¹
  have hA₀ : 0 ≤ A₀ := by
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun _ _ => by positivity)
    · exact inv_nonneg.mpr hlower.le
  let E : Equiv.Perm (H → P) :=
    { toFun := fun l => l ∘ e.symm
      invFun := fun l => l ∘ e
      left_inv := by intro l; funext h; simp
      right_inv := by intro l; funext h; simp }
  let F := fun d l => constituentCharacterCore role size χ κ pivot n P hP
    childBound pivotBound ranges leaf hist u M (l, d)
  have he := permuted_history_energy_on_support E μ root F A₀ hA₀
    (fun _ => Finset.prod_nonneg (fun _ _ => primeSubsetPrior_nonneg _ _ _))
    (by
      intro l d hd
      have hfull := (norm_pos_iff.mpr hd).trans_le
        (constituentCharacterCore_norm_le_full role size χ κ pivot n P hP childBound
          pivotBound ranges leaf hist u M hκ l d)
      exact harmonicTuple_point_le_product_lower P _ l lower hlower
        (hproduct l d (norm_pos_iff.mp hfull)))
    (fun l d d' hd hd' hr => hhist (validTransferHistory_unique
      (scheduleAtomSystem role childBound pivotBound) n _ _ _
      (constituentCharacterCore_nonzero_valid role size χ κ pivot n P hP childBound pivotBound
        ranges leaf hist u M l d hd)
      (constituentCharacterCore_nonzero_valid role size χ κ pivot n P hP childBound pivotBound
        ranges leaf hist u M l d' hd') (hroot d d' hr)))
  have hpair (l : H → P) (d d' : D) :
      constituentCharacterCoefficient role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist u M (l, d) *
      conj (constituentCharacterCoefficient role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist u M (l ∘ e.symm, d')) =
      ((μ l * μ (E l) : ℝ) : ℂ) * (F d l * conj (F d' (E l))) := by
    rw [constituentCharacterCoefficient_factor, constituentCharacterCoefficient_factor]
    simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
    dsimp only [μ, E, Equiv.coe_fn_mk, F]
    ring
  simp_rw [hpair]
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ hA₀
  apply Finset.sum_le_sum
  intro d _
  apply Finset.sum_le_sum
  intro l _
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
    (constituentCharacterCore_norm_le_full role size χ κ pivot n P hP childBound pivotBound
      ranges leaf hist u M hκ l d) 2) (Finset.prod_nonneg (fun _ _ => primeSubsetPrior_nonneg _ _ _))

end Ostmann

end OAI
