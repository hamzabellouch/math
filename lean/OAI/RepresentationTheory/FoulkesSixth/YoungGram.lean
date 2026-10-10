import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.ColorOrbits
import OAI.RepresentationTheory.FoulkesSixth.HomogeneousPlethysm

namespace OAI

noncomputable section

namespace Foulkes.Young
open MvPolynomial Foulkes.Complete Finset Module

instance finiteContingency {A B : Type*} [Fintype A] [Fintype B]
    (mu : A → ℕ) (nu : B → ℕ) : Finite (Contingency mu nu) := by
  classical
  let f : Contingency mu nu → (∀ a : A, B → Fin (mu a + 1)) := fun M a b =>
    ⟨M.val a b, by
      have hh := Finset.single_le_sum (f := M.val a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
      rw [M.property.1 a] at hh
      omega⟩
  apply Finite.of_injective f
  intro M N h
  apply Subtype.ext
  ext a b
  exact congrArg Fin.val (congrFun (congrFun h a) b)

def rowChoicesEquiv {A B : Type*} [Fintype A] [Fintype B]
    (mu : A → ℕ) (nu : B → ℕ) :
    {r : ∀ a, Degree B (mu a) // (∑ a, (r a).val) = Finsupp.equivFunOnFinite.symm nu} ≃
      Contingency mu nu where
  toFun r := ⟨fun a b => (r.val a).val b,
    (fun a => (Finsupp.degree_eq_sum _).symm.trans (r.val a).property),
    fun b => by simpa only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_equivFunOnFinite_symm]
      using congrArg (fun f : B →₀ ℕ => f b) r.property⟩
  invFun M := ⟨fun a => ⟨Finsupp.equivFunOnFinite.symm (M.val a), by
      rw [Finsupp.degree_eq_sum]
      exact M.property.1 a⟩, by
    ext b
    rw [Finsupp.finsetSum_apply]
    exact M.property.2 b⟩
  left_inv r := by apply Subtype.ext; funext a; apply Subtype.ext; ext b; rfl
  right_inv M := rfl

theorem coeff_product_h {A B : Type*} [Fintype A] [Fintype B]
    (mu : A → ℕ) (nu : B → ℕ) :
    (∏ a, h B (mu a)).coeff (Finsupp.equivFunOnFinite.symm nu) =
      (Nat.card (Contingency mu nu) : ℤ) := by
  classical
  have he : (∏ a, h B (mu a)) = ∑ r : ∀ a, Degree B (mu a),
      monomial (∑ a, (r a).val) (1 : ℤ) := by
    simp only [h, Fintype.prod_sum, ← monomial_sum_one]
  rw [he, coeff_sum]
  simp only [coeff_monomial]
  have hh : (∑ r : ∀ a, Degree B (mu a),
      if (∑ a, (r a).val) = Finsupp.equivFunOnFinite.symm nu then (1 : ℤ) else 0) =
      (Nat.card {r : ∀ a, Degree B (mu a) //
        (∑ a, (r a).val) = Finsupp.equivFunOnFinite.symm nu} : ℤ) := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hh, Nat.card_congr (rowChoicesEquiv mu nu)]

theorem young_hom_as_coefficient {K D A B : Type*} [Field K]
    [Fintype D] [Fintype A] [Fintype B] (mu : A → ℕ) (nu : B → ℕ)
    (hnu : ∑ b, nu b = Fintype.card D) :
    (finrank K ((permRep K (Equiv.Perm D) (Coloring D A mu)).IntertwiningMap
      (permRep K (Equiv.Perm D) (Coloring D B nu))) : ℤ) =
      (∏ b, h A (nu b)).coeff (Finsupp.equivFunOnFinite.symm mu) := by
  rw [young_hom_finrank mu nu hnu, coeff_product_h]

end Foulkes.Young

end

end OAI
