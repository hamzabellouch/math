import OAI.RepresentationTheory.FoulkesHowe.VanishingOne
import OAI.RepresentationTheory.FoulkesHowe.VanishingInduction

namespace OAI

noncomputable section

namespace Problem346

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- The induction on the number of slots, isolated from the two polynomial
transfer arguments. The first argument packages the binary-pencil identity and
the first transfer; the second is the common-power-removal transfer. -/
theorem vanishing_induction_from_transfer_steps
    (firstTransfer : ∀ r m : ℕ, 0 < r → 0 < m → (r+1)*r ≤ r+m →
      ∀ T : SymmetricMultilinearForm (r+1) (r+m) V,
      IsSymmetricMultilinearForm (r+1) (r+m) V T →
      (∀ y : Fin (r+m) → V, T (fun _ => symMonomial (r+m) V y) = 0) →
      ∀ x t : V, ∀ y : Fin m → V,
        lowerProductForm r m T x t (fun _ => symMonomial m V y) = 0)
    (secondTransfer : ∀ r m : ℕ, 0 < r → 0 < m → (r+1)*r ≤ r+m →
      ∀ T : SymmetricMultilinearForm (r+1) (r+m) V,
      IsSymmetricMultilinearForm (r+1) (r+m) V T →
      (∀ x t : V, ∀ Q : Fin r → SymPow m V, lowerProductForm r m T x t Q = 0) →
      ∀ v : Fin (r+1) → V,
        T (fun i => symMonomial (r+m) V (fun _ => v i)) = 0)
    (purePowerExt : ∀ a b : ℕ, ∀ T : SymmetricMultilinearForm a b V,
      (∀ v : Fin a → V, T (fun i => symMonomial b V (fun _ => v i)) = 0) → T = 0) :
    ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → a*(a-1) ≤ b →
      ∀ T : SymmetricMultilinearForm a b V,
      IsSymmetricMultilinearForm a b V T →
      (∀ y : Fin b → V, T (fun _ => symMonomial b V y) = 0) → T = 0 := by
  intro a
  induction a with
  | zero =>
      intro b ha
      omega
  | succ r ih =>
      intro b ha hb hab T hT hdiag
      by_cases hr : r = 0
      · subst r
        exact vanishing_on_products_one V b T hdiag
      have hrpos : 0 < r := Nat.pos_of_ne_zero hr
      have hrb : r ≤ b := by
        have hmul : r ≤ (r+1)*r := by nlinarith
        simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using hmul.trans hab
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hrb
      have hbound : (r+1)*r ≤ r+m := by simpa only [Nat.succ_eq_add_one,
        Nat.add_sub_cancel] using hab
      have hm : 0 < m := by nlinarith
      have hmrange : r*(r-1) ≤ m := by
        have hsub : r-1 ≤ r := Nat.sub_le ..
        have hmul : r*(r-1) ≤ r*r := Nat.mul_le_mul_left r hsub
        nlinarith
      have hrestricted : ∀ x t : V, lowerProductForm r m T x t = 0 := by
        intro x t
        exact ih m hrpos hm hmrange (lowerProductForm r m T x t)
          (lowerProductForm_symmetric r m T hT x t)
          (firstTransfer r m hrpos hm hbound T hT hdiag x t)
      apply purePowerExt (r+1) (r+m) T
      apply secondTransfer r m hrpos hm hbound T hT
      intro x t Q
      rw [hrestricted x t]
      rfl

end Problem346

end

end OAI
