import OAI.NumberTheory.Ostmann.Construction.ScheduledWordLeafProducts
import OAI.NumberTheory.Ostmann.Construction.ConstituentBlockProducts

namespace OAI

/-! # Selected leaf primes in the literal grouped-atom reversal products -/

namespace Ostmann
open scoped BigOperators Classical

theorem constituent_H_product {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ) (b : Bool)
    (q : SurvivingConstituent role size (n + 1) → ℕ) :
    (∏ h : CopyScheduleH role n,
      ((scheduleConstituentWord role size (n + 1) ⟨.inl (b, h.val), h.property⟩).map q).prod) =
      ∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
        q ⟨.inl (b, h.val), h.property⟩ := by
  simp only [scheduleConstituentWord_prod]
  rw [← constituentH_product role size n
    (fun h => q ⟨.inl (b, h.val), h.property⟩)]
  apply Finset.prod_congr rfl
  intro h _
  apply Finset.prod_congr rfl
  intro k _
  change Fin (size (copyScheduleOrigin n h.val)) at k
  exact congrArg q (constituentH_output role size n b h k)

noncomputable def wordLeafFixedHProduct {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word) (n : ℕ) (b : Bool)
    (y : WordLeafOutside role i hi (n + 1) → ℕ) : ℕ :=
  ∏ h : WordLeafHOutside role i hi n, y (copiedWordLeafOutside role i hi n b h)

theorem constituent_wordLeaf_H_product {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (i : Σ a, Fin (size a)) (hi : role i.1 = .word) (n : ℕ) (b : Bool)
    (y : WordLeafOutside (fun j : Σ a, Fin (size a) => role j.1) i hi (n + 1) → ℕ)
    (x : TreeLeafIndex (n + 1) → ℕ) :
    (∏ h : CopyScheduleH role n,
      ((scheduleConstituentWord role size (n + 1) ⟨.inl (b, h.val), h.property⟩).map
        (wordLeafAssignment (fun j : Σ a, Fin (size a) => role j.1) i hi (n + 1) y x)).prod) =
      wordLeafFixedHProduct (fun j : Σ a, Fin (size a) => role j.1) i hi n b y *
        ∏ t : TreeLeafIndex n, x (if b then .inl t else .inr t) := by
  rw [constituent_H_product]
  exact wordLeaf_H_product _ i hi n b y x

/-- The reversal equation now uses exactly the selected child products and
coefficients made only from the fixed remaining prime coordinates. -/
theorem constituent_wordLeaf_node_relation {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (i : Σ a, Fin (size a)) (hi : role i.1 = .word) (n : ℕ)
    (y : WordLeafOutside (fun j : Σ a, Fin (size a) => role j.1) i hi (n + 1) → ℕ)
    (x : TreeLeafIndex (n + 1) → ℕ) (childBound pivotBound : ℕ → ℕ)
    (s v w : ℤ) (P : ℕ)
    (h : ValidTransferNode (scheduleAtomSystem role childBound pivotBound)
      ⟨n + 1, fun a => ((scheduleConstituentWord role size (n + 1) a).map
        (wordLeafAssignment (fun j : Σ a, Fin (size a) => role j.1) i hi (n + 1) y x)).prod⟩
      s v w P) :
    v * ((wordLeafFixedHProduct (fun j : Σ a, Fin (size a) => role j.1) i hi n false y : ℕ) : ℤ) *
        ((∏ t : TreeLeafIndex n, x (.inr t) : ℕ) : ℤ) -
      w * ((wordLeafFixedHProduct (fun j : Σ a, Fin (size a) => role j.1) i hi n true y : ℕ) : ℤ) *
        ((∏ t : TreeLeafIndex n, x (.inl t) : ℕ) : ℤ) = s * P := by
  have hr := h.relation
  change v * ((∏ a : CopyScheduleH role n, _) : ℕ) -
    w * ((∏ a : CopyScheduleH role n, _) : ℕ) = s * P at hr
  rw [constituent_wordLeaf_H_product, constituent_wordLeaf_H_product] at hr
  simpa [mul_assoc] using hr

theorem constituent_wordLeaf_coefficient_unit {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (i : Σ a, Fin (size a)) (hi : role i.1 = .word) (n : ℕ)
    (y : WordLeafOutside (fun j : Σ a, Fin (size a) => role j.1) i hi (n + 1) → ℕ)
    (x : TreeLeafIndex (n + 1) → ℕ) (s : ℤ)
    (hunit : ∀ a : CopyScheduleAtoms role (n + 1),
      (((scheduleConstituentWord role size (n + 1) a).map
        (wordLeafAssignment (fun j : Σ a, Fin (size a) => role j.1) i hi (n + 1) y x)).prod).Coprime
          s.natAbs) (b : Bool) :
    IsCoprime ((wordLeafFixedHProduct (fun j : Σ a, Fin (size a) => role j.1) i hi n b y : ℕ) : ℤ) s := by
  have hp := Nat.coprime_fintype_prod_left_iff.mpr
    (fun h : CopyScheduleH role n => hunit ⟨.inl (b, h.val), h.property⟩)
  rw [constituent_wordLeaf_H_product] at hp
  have hc := (Nat.coprime_mul_iff_left.mp hp).1
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  change Nat.gcd (wordLeafFixedHProduct _ i hi n b y) s.natAbs = 1
  exact hc

end Ostmann

end OAI
