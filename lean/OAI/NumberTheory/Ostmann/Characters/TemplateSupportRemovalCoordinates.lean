import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalNonzero

namespace OAI

noncomputable section
namespace Ostmann.Characters.TemplateSupportRemoval
open MvPolynomial
variable {ι : Type*} [DecidableEq ι]

abbrev Other (i : ι) := {j : ι // j ≠ i}

def insertCoordinate {R : Type*} (i : ι) (x : Other i → R) (b : R) : ι → R :=
  fun j => if h : j=i then b else x ⟨j,h⟩

@[simp] theorem insertCoordinate_self {R : Type*} (i : ι) (x : Other i → R) (b : R) :
    insertCoordinate i x b i=b := by simp [insertCoordinate]

@[simp] theorem insertCoordinate_other {R : Type*} (i : ι) (x : Other i → R) (b : R) (j : Other i) :
    insertCoordinate i x b j=x j := by simp [insertCoordinate,j.property]

def eraseCoordinate (i : ι) : MvPolynomial ι ℤ →+* MvPolynomial (Other i) ℤ :=
  eval₂Hom C (fun j => if h : j=i then 0 else X ⟨j,h⟩)

theorem rename_eraseCoordinate (i : ι) (P : MvPolynomial ι ℤ) :
    rename (fun j : Other i => j.val) (eraseCoordinate i P)=ZeroVariable.setZero i P := by
  have h : (rename (fun j : Other i => j.val)).toRingHom.comp (eraseCoordinate i)=
      ZeroVariable.setZero i := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [eraseCoordinate,ZeroVariable.setZero]
    · intro j
      by_cases hj : j=i
      · simp [eraseCoordinate,ZeroVariable.setZero,hj]
      · simp [eraseCoordinate,ZeroVariable.setZero,hj]
  exact congrArg (fun f : MvPolynomial ι ℤ →+* MvPolynomial ι ℤ => f P) h

theorem eraseCoordinate_ne_zero_iff (i : ι) (P : MvPolynomial ι ℤ) :
    eraseCoordinate i P ≠ 0 ↔ ZeroVariable.setZero i P ≠ 0 := by
  rw [← rename_eraseCoordinate i P]
  exact (not_congr (rename_eq_zero_iff_of_injective (eraseCoordinate i P) Subtype.val_injective)).symm

theorem eval_eraseCoordinate (i : ι) (P : MvPolynomial ι ℤ) (x : Other i → ℤ) :
    eval x (eraseCoordinate i P)=eval (insertCoordinate i x 0) P := by
  change eval₂ (RingHom.id ℤ) x (eval₂ C (fun j => if h : j=i then 0 else X ⟨j,h⟩) P)=_
  rw [← eval₂_assoc]
  apply congrArg (fun y : ι → ℤ => eval y P)
  funext j
  by_cases hj : j=i <;> simp [insertCoordinate,hj]

theorem eval_eraseCoordinate_mod (i : ι) (P : MvPolynomial ι ℤ) (x : Other i → ℤ) (p : ℕ) :
    ((eval x (eraseCoordinate i P) : ℤ) : ZMod p)=
      ((eval (insertCoordinate i x (p:ℤ)) P : ℤ) : ZMod p) := by
  let a := insertCoordinate i x (p:ℤ)
  have hai : (a i : ZMod p)=0 := by simp [a]
  have h := ZeroVariable.eval₂_setZero i P (Int.castRingHom (ZMod p))
    (fun j => (a j : ZMod p)) hai
  rw [← rename_eraseCoordinate i P,eval₂_rename] at h
  have hx : (fun j : Other i => (a j.val : ZMod p)) = fun j => (x j : ZMod p) := by
    funext j
    simp [a]
  simp only [Function.comp_def] at h
  rw [hx] at h
  change (Int.castRingHom (ZMod p)) (eval x (eraseCoordinate i P))=
    (Int.castRingHom (ZMod p)) (eval a P)
  rw [eval₂_comp,eval₂_comp]
  exact h

theorem dvd_eval_eraseCoordinate_iff (i : ι) (P : MvPolynomial ι ℤ) (x : Other i → ℤ) (p : ℕ) :
    (p:ℤ) ∣ eval x (eraseCoordinate i P) ↔ (p:ℤ) ∣ eval (insertCoordinate i x (p:ℤ)) P := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,← ZMod.intCast_zmod_eq_zero_iff_dvd,
    eval_eraseCoordinate_mod]

end Ostmann.Characters.TemplateSupportRemoval

end

end OAI
