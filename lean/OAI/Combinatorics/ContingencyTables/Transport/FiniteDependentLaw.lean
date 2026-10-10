import OAI.Combinatorics.ContingencyTables.Transport.RationalMapProducts

namespace OAI

/-! # Exact joint laws with a finite state-dependent completion space -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture

variable {X : Type*} {Y : X → Type*} [Fintype X] [∀ x,Fintype (Y x)]

def dependentJointLaw (p : RationalLaw X) (q : (x : X) → RationalLaw (Y x)) :
    RationalLaw ((x : X) × Y x) where
  mass := fun a => p.mass a.1*(q a.1).mass a.2
  nonnegative := fun a => mul_nonneg (p.nonnegative a.1) ((q a.1).nonnegative a.2)
  total := by
    rw [Fintype.sum_sigma]
    simp only [←Finset.mul_sum,(q _).total,mul_one,p.total]

variable [Nonempty X] [∀ x,Nonempty (Y x)]

instance dependentJointNonempty : Nonempty ((x : X) × Y x) :=
  ⟨⟨Classical.choice ‹Nonempty X›, Classical.choice (inferInstance : Nonempty (Y (Classical.choice ‹Nonempty X›)))⟩⟩

/-- A state chosen in proportion to its completion count, followed by a
uniform completion, gives exactly the uniform law on all joint pairs. -/
theorem dependentJointLaw_uniform (p : RationalLaw X)
    (hp : ∀ x,p.mass x=(Fintype.card (Y x):ℚ)/(∑ z : X,(Fintype.card (Y z):ℚ))) :
    dependentJointLaw p (fun x => uniformLaw (α := Y x))=
      uniformLaw (α := (x : X) × Y x) := by
  apply RationalLaw.ext
  funext a
  have hcard : (Fintype.card (Y a.1):ℚ)≠0 := by
    exact_mod_cast (Fintype.card_pos (α := Y a.1)).ne'
  change p.mass a.1*(1/(Fintype.card (Y a.1):ℚ))=1/(Fintype.card ((x : X) × Y x):ℚ)
  rw [hp,Fintype.card_sigma,Nat.cast_sum]
  field_simp

end ContingencyTables.FirstSuccess

end OAI
