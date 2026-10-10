import Mathlib

namespace OAI

namespace PiExponent.PowerCover

noncomputable section

variable {σ : Type*} [Fintype σ]

def scale (w : σ → ℕ) (q : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => w i * q i)

def quotient (w : σ → ℕ) (a : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => a i / w i)

def residue (w : σ → ℕ) (hw : ∀ i, 0 < w i) (a : σ →₀ ℕ) :
    ∀ i, Fin (w i) :=
  fun i => ⟨a i % w i, Nat.mod_lt _ (hw i)⟩

def combine (w : σ → ℕ) (p : (σ →₀ ℕ) × (∀ i, Fin (w i))) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => w i * p.1 i + (p.2 i).val)

@[simp] theorem scale_apply (w : σ → ℕ) (q : σ →₀ ℕ) (i : σ) :
    scale w q i = w i * q i := by simp [scale]

@[simp] theorem quotient_apply (w : σ → ℕ) (a : σ →₀ ℕ) (i : σ) :
    quotient w a i = a i / w i := by simp [quotient]

omit [Fintype σ] in
@[simp] theorem residue_apply (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (a : σ →₀ ℕ) (i : σ) :
    (residue w hw a i).val = a i % w i := rfl

@[simp] theorem combine_apply (w : σ → ℕ)
    (p : (σ →₀ ℕ) × (∀ i, Fin (w i))) (i : σ) :
    combine w p i = w i * p.1 i + (p.2 i).val := by simp [combine]

@[simp] theorem combine_quotient_residue (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (a : σ →₀ ℕ) :
    combine w (quotient w a, residue w hw a) = a := by
  ext i
  simp only [combine_apply, quotient_apply, residue_apply]
  exact Nat.div_add_mod (a i) (w i)

@[simp] theorem quotient_combine (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : (σ →₀ ℕ) × (∀ i, Fin (w i))) :
    quotient w (combine w p) = p.1 := by
  ext i
  simp only [quotient_apply, combine_apply]
  rw [Nat.mul_add_div (hw i)]
  simp [Nat.div_eq_of_lt (p.2 i).isLt]

@[simp] theorem residue_combine (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : (σ →₀ ℕ) × (∀ i, Fin (w i))) :
    residue w hw (combine w p) = p.2 := by
  funext i
  apply Fin.ext
  simp [Nat.add_mod, Nat.mod_eq_of_lt (p.2 i).isLt]

def exponentEquiv (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    (σ →₀ ℕ) ≃ ((σ →₀ ℕ) × (∀ i, Fin (w i))) where
  toFun a := (quotient w a, residue w hw a)
  invFun := combine w
  left_inv := combine_quotient_residue w hw
  right_inv p := by simp [quotient_combine w hw]

@[simp] theorem exponentEquiv_apply (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (a : σ →₀ ℕ) : exponentEquiv w hw a = (quotient w a, residue w hw a) := rfl

@[simp] theorem exponentEquiv_symm_apply (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : (σ →₀ ℕ) × (∀ i, Fin (w i))) :
    (exponentEquiv w hw).symm p = combine w p := rfl

@[simp] theorem quotient_add_scale (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (a q : σ →₀ ℕ) :
    quotient w (a + scale w q) = quotient w a + q := by
  ext i
  simp only [quotient_apply, Finsupp.add_apply, scale_apply]
  simp [Nat.add_mul_div_left, hw i]

@[simp] theorem residue_add_scale (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (a q : σ →₀ ℕ) :
    residue w hw (a + scale w q) = residue w hw a := by
  funext i
  apply Fin.ext
  simp [Nat.add_mod]

@[simp] theorem exponentEquiv_add_scale (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (a q : σ →₀ ℕ) :
    exponentEquiv w hw (a + scale w q) = (quotient w a + q, residue w hw a) := by
  simp [quotient_add_scale w hw]

@[simp] theorem combine_add (w : σ → ℕ) (q q' : σ →₀ ℕ)
    (r : ∀ i, Fin (w i)) :
    combine w (q + q', r) = combine w (q, r) + scale w q' := by
  ext i
  simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm]

@[simp] theorem scale_zero (w : σ → ℕ) : scale w 0 = 0 := by
  ext i
  simp

@[simp] theorem scale_add (w : σ → ℕ) (q q' : σ →₀ ℕ) :
    scale w (q + q') = scale w q + scale w q' := by
  ext i
  simp [Nat.mul_add]

end
end PiExponent.PowerCover

end OAI
