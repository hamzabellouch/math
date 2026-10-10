import OAI.Analysis.Laughlin.Fock.SpinRepresentation

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators Matrix

theorem occupationInner_basis_left (Q : ℕ) (A : Finset (Fin (Q+1))) (x : Space Q) :
    occupationInner Q (occupationBasis Q A) x = (occupationBasis Q).repr x A := by
  simp [occupationInner,Module.Basis.repr_self,Finsupp.single_apply]

theorem occupationInner_ext_right (Q : ℕ) (x y : Space Q)
    (h : ∀ z, occupationInner Q z x = occupationInner Q z y) : x=y := by
  apply (occupationBasis Q).repr.injective
  ext A
  simpa only [occupationInner_basis_left] using h (occupationBasis Q A)

theorem occupationInner_rotation_left (Q : ℕ) (g : SourceSU2) (x y : Space Q) :
    occupationInner Q (exteriorRotation Q g⁻¹ x) y =
      occupationInner Q x (exteriorRotation Q g y) := by
  have h := exteriorRotation_unitary Q g (exteriorRotation Q g⁻¹ x) y
  rw [exteriorRotation_mul,mul_inv_cancel,exteriorRotation_one] at h
  exact h.symm

theorem exteriorFamily_contraction_rotation {I : Type*} [Fintype I] [DecidableEq I]
    (Q : ℕ) (ρ : SourceSU2 →* Matrix I I ℂ)
    (hρ : ∀ g, ρ g⁻¹=(ρ g)ᴴ)
    (v : I → Space Q) (minus : I → Module.End ℂ (Space Q))
    (ha : ∀ i x y, occupationInner Q (v i*x) y = occupationInner Q x (minus i y))
    (hv : ∀ g i, exteriorRotation Q g (v i) = ∑ j, ρ g j i • v j)
    (g : SourceSU2) (i : I) (x : Space Q) :
    minus i (exteriorRotation Q g x) = ∑ j, ρ g i j • exteriorRotation Q g (minus j x) := by
  apply occupationInner_ext_right Q
  intro y
  rw [← ha,← occupationInner_rotation_left,map_mul,hv]
  simp only [Finset.sum_mul,smul_mul_assoc,occupationInner_sum_left,occupationInner_smul_left,
    ha,hρ,Matrix.conjTranspose_apply,star_star,occupationInner_sum_right,occupationInner_smul_right,
    occupationInner_rotation_left]

end Laughlin.Fock

end OAI
