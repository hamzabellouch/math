import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.CompleteNewton
import OAI.RepresentationTheory.FoulkesSixth.SignedStrips

namespace OAI

noncomputable section

namespace Foulkes.Complete
open MvPolynomial Finset

def degreeEquiv {α β : Type*} (e : α ≃ β) (b : ℕ) : Degree α b ≃ Degree β b where
  toFun d := ⟨d.val.mapDomain e, by simpa using d.property⟩
  invFun d := ⟨d.val.mapDomain e.symm, by simpa using d.property⟩
  left_inv d := by
    apply Subtype.ext
    ext j
    simp [Finsupp.mapDomain_equiv_apply]
  right_inv d := by
    apply Subtype.ext
    ext j
    simp [Finsupp.mapDomain_equiv_apply]

theorem rename_h {α β : Type*} [Finite α] [Finite β] (e : α ≃ β) (b : ℕ) :
    rename e (h α b) = h β b := by
  simp only [h, map_sum, rename_monomial]
  exact Equiv.sum_comp (degreeEquiv e b) (fun d => monomial d.val 1)

theorem alphabetH_reindex {α β σ : Type*} [Finite α] [Finite β]
    (e : α ≃ β) (x : β → MvPolynomial σ ℤ) (b : ℕ) :
    alphabetH (x ∘ e) b = alphabetH x b := by
  have hh := congrArg (eval₂Hom (Int.castRingHom (MvPolynomial σ ℤ)) x) (rename_h e b)
  simpa only [eval₂Hom_rename, alphabetH] using hh

theorem rename_pleth (n b a : ℕ) (σ : Equiv.Perm (Fin n)) :
    rename σ (pleth n b a) = pleth n b a := by
  unfold pleth alphabetH
  change (rename σ).toRingHom _ = _
  rw [MvPolynomial.map_eval₂Hom]
  have hh : (rename σ).toRingHom.comp (Int.castRingHom (MvPolynomial (Fin n) ℤ)) =
      Int.castRingHom (MvPolynomial (Fin n) ℤ) := by ext; simp
  rw [hh]
  simpa only [alphabetH, Function.comp_def, degreeEquiv, Equiv.coe_fn_mk, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_monomial] using
    alphabetH_reindex (degreeEquiv σ a) (fun d => monomial d.val (1 : ℤ)) b

end Foulkes.Complete

namespace Foulkes.Lookup
open MvPolynomial Finset Foulkes.Strips

def Alternating {n : ℕ} (p : MvPolynomial (Fin n) ℤ) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), rename σ p = (Equiv.Perm.sign σ : ℤ) • p

lemma alternant_alternating {n : ℕ} (m : Fin n → ℕ) : Alternating (alternant m) := by
  intro σ
  let M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) ℤ) := Matrix.of (fun r c => X r ^ m c)
  have hm : (rename σ).toRingHom.mapMatrix M = M.submatrix σ id := by
    ext r c
    simp [M, RingHom.mapMatrix_apply]
  have hh := (rename σ).toRingHom.map_det M
  rw [hm, Matrix.det_permute] at hh
  change rename σ (alternant m) = _ at hh
  have he : M.det = alternant m := rfl
  rw [he] at hh
  simpa only [zsmul_eq_mul] using hh

lemma alternating_mul_symmetric {n : ℕ} {p q : MvPolynomial (Fin n) ℤ}
    (hp : ∀ σ : Equiv.Perm (Fin n), rename σ p = p) (hq : Alternating q) :
    Alternating (p*q) := by
  intro σ
  simp only [map_mul, hp σ, hq σ, mul_smul_comm]

lemma mapDomain_expVector {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n → ℕ) :
    (expVector v).mapDomain σ = expVector (v ∘ σ.symm) := by
  ext j
  simp [Finsupp.mapDomain_equiv_apply, Function.comp_def]

lemma coeff_comp {n : ℕ} {p : MvPolynomial (Fin n) ℤ} (hp : Alternating p)
    (v : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    p.coeff (expVector (v ∘ σ)) = (Equiv.Perm.sign σ : ℤ) * p.coeff (expVector v) := by
  have hm : (expVector (v ∘ σ)).mapDomain σ = expVector v := by
    rw [mapDomain_expVector]
    congr 1
    funext j
    simp
  have hh := coeff_rename_mapDomain σ σ.injective p (expVector (v ∘ σ))
  rw [hm, hp σ, coeff_smul] at hh
  simpa [zsmul_eq_mul] using hh.symm

lemma coeff_eq_sign_mul_comp {n : ℕ} {p : MvPolynomial (Fin n) ℤ} (hp : Alternating p)
    (v : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    p.coeff (expVector v) = (Equiv.Perm.sign σ : ℤ) * p.coeff (expVector (v ∘ σ)) := by
  have hh := coeff_comp hp (v ∘ σ) σ.symm
  have he : (v ∘ σ) ∘ σ.symm = v := by funext j; simp
  simpa only [he, Equiv.Perm.sign_symm] using hh

lemma coeff_repeated {n : ℕ} {p : MvPolynomial (Fin n) ℤ} (hp : Alternating p)
    (v : Fin n → ℕ) {j k : Fin n} (hjk : j ≠ k) (he : v j = v k) :
    p.coeff (expVector v) = 0 := by
  classical
  have hs : v ∘ Equiv.swap j k = v := by
    funext r
    by_cases hrj : r = j
    · subst r; simp [he]
    by_cases hrk : r = k
    · subst r; simp [he]
    simp [Equiv.swap_apply_of_ne_of_ne hrj hrk]
  have hh := coeff_comp hp v (Equiv.swap j k)
  rw [hs, Equiv.Perm.sign_swap hjk] at hh
  simp only [Units.val_neg, Units.val_one, neg_one_mul] at hh
  omega

def sortDesc {n : ℕ} (v : Fin n → ℕ) : Equiv.Perm (Fin n) :=
  Tuple.sort (α := ℕᵒᵈ) (fun j => v j)

lemma sortDesc_antitone {n : ℕ} (v : Fin n → ℕ) : Antitone (v ∘ sortDesc v) :=
by
  intro j k hjk
  exact Tuple.monotone_sort (α := ℕᵒᵈ) (fun j => v j) hjk

lemma sortDesc_strict {n : ℕ} (v : Fin n → ℕ) (hv : Function.Injective v) :
    StrictAnti (v ∘ sortDesc v) :=
  (sortDesc_antitone v).strictAnti_of_injective (hv.comp (sortDesc v).injective)

def sortedPartition {n : ℕ} (v : Fin n → ℕ) (j : Fin n) : ℕ :=
  v (sortDesc v j) - staircase n j

def schurCoeff {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (mu : Fin n → ℕ) : ℤ :=
  (p * alternant (staircase n)).coeff (expVector (shifted mu))

def Q (n b : ℕ) (mu : Fin n → ℕ) : ℤ := schurCoeff (Complete.pleth n b 6) mu
def F (n b : ℕ) (mu : Fin n → ℕ) : ℤ := schurCoeff (Complete.pleth n 6 b) mu

end Foulkes.Lookup

end

end OAI
