import OAI.Probability.SignedSweeps.PairTwirlLift

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

def enumeratedPermutation {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) :
    Equiv.Perm (Fin (Fintype.card A)) :=
  (Fintype.equivFin A).symm.trans (e.trans ((Fintype.equivFin B).trans
    (finCongr (Fintype.card_congr e)).symm))

def equivSign {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) : ℤˣ :=
  Equiv.Perm.sign (enumeratedPermutation e)

lemma enumeratedPermutation_refl {A : Type*} [Fintype A] :
    enumeratedPermutation (Equiv.refl A) = 1 := by
  ext i
  simp [enumeratedPermutation]

lemma enumeratedPermutation_trans {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (e : A ≃ B) (f : B ≃ C) :
    enumeratedPermutation (e.trans f) =
      (finCongr (Fintype.card_congr e)).symm.permCongr (enumeratedPermutation f) *
        enumeratedPermutation e := by
  ext i
  simp [enumeratedPermutation, Equiv.permCongr_apply]

@[simp] lemma equivSign_refl {A : Type*} [Fintype A] :
    equivSign (Equiv.refl A) = 1 := by
  rw [equivSign, enumeratedPermutation_refl, map_one]

lemma equivSign_trans {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (e : A ≃ B) (f : B ≃ C) :
    equivSign (e.trans f) = equivSign f * equivSign e := by
  simp only [equivSign, enumeratedPermutation_trans, map_mul, Equiv.Perm.sign_permCongr]

lemma equivSign_perm {A : Type*} [Fintype A] (e : Equiv.Perm A) :
    equivSign e = Equiv.Perm.sign e := by
  have he : enumeratedPermutation e = (Fintype.equivFin A).permCongr e := by
    ext i
    simp [enumeratedPermutation, Equiv.permCongr_apply]
  rw [equivSign, he, Equiv.Perm.sign_permCongr]

lemma equivSign_symm {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) :
    equivSign e.symm = (equivSign e)⁻¹ := by
  have hh := equivSign_trans e e.symm
  rw [Equiv.self_trans_symm, equivSign_refl] at hh
  exact eq_inv_of_mul_eq_one_left hh.symm

def complexEquivSign {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) : ℂ :=
  ((equivSign e : ℤ) : ℂ)

@[simp] lemma complexEquivSign_refl {A : Type*} [Fintype A] :
    complexEquivSign (Equiv.refl A) = 1 := by simp [complexEquivSign]

lemma complexEquivSign_trans {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (e : A ≃ B) (f : B ≃ C) :
    complexEquivSign (e.trans f) = complexEquivSign f * complexEquivSign e := by
  simp [complexEquivSign, equivSign_trans]

lemma complexEquivSign_norm {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) :
    ‖complexEquivSign e‖ = 1 := by
  rcases Int.units_eq_one_or (equivSign e) with he|he <;> simp [complexEquivSign, he]

lemma complexEquivSign_perm {p : ℕ} (g : SymmetricGroup p) :
    complexEquivSign g = complexSign p g := by
  simp only [complexEquivSign, equivSign_perm, complexSign, MonoidHom.coe_mk, OneHom.coe_mk]
  congr 3
  exact congrArg (fun h : DecidableEq (Fin p) => @Equiv.Perm.sign (Fin p) h _)
    (Subsingleton.elim _ _)

end SignedSweeps
end

end OAI
