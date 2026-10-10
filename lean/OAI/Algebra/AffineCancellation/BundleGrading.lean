import OAI.Algebra.AffineCancellation.ReplicaLift
import OAI.Algebra.AffineCancellation.GradedCommutation

namespace OAI

noncomputable section

namespace ComplexCancellation.Bundle
open Determinant
lemma fiberEuler_j (r : T) : fiberEuler (j r)=j (Euler r) := AffineModification.euler_coefficient _ _ _ r
lemma fiberEuler_τ : fiberEuler τ=0 := AffineModification.euler_τ _ _ _
lemma fiberEuler_V : fiberEuler V=2*V := AffineModification.euler_V _ _ _
lemma j_mem (r : T) : j r ∈ valuationPieces 0 := AffineModification.coefficient_mem T v r
lemma τ_mem : τ ∈ valuationPieces (-1) := AffineModification.τ_mem T v
lemma V_mem : V ∈ valuationPieces 2 := AffineModification.V_mem T v
lemma fiberEuler_homogeneous (i : ℤ) (r : B) (hr : r ∈ valuationPieces i) :
    fiberEuler r ∈ valuationPieces i := by
  have he : fiberEuler=GradedLND.component valuationPieces fiberEuler 0 := by
    apply sub_eq_zero.mp
    apply AffineModification.derivation_zero_of_generators v
    · intro a
      change fiberEuler (j a)-GradedLND.component valuationPieces fiberEuler 0 (j a)=0
      rw [GradedLND.component_of_mem valuationPieces fiberEuler 0 (j_mem a),add_zero,
        fiberEuler_j,GradedLND.proj_of_mem valuationPieces (j_mem _),sub_self]
    · change fiberEuler τ-GradedLND.component valuationPieces fiberEuler 0 τ=0
      rw [GradedLND.component_of_mem valuationPieces fiberEuler 0 τ_mem,fiberEuler_τ,map_zero,sub_self]
    · change fiberEuler V-GradedLND.component valuationPieces fiberEuler 0 V=0
      rw [GradedLND.component_of_mem valuationPieces fiberEuler 0 V_mem,add_zero,fiberEuler_V]
      have hm : 2*V ∈ valuationPieces 2 := by simpa only [two_mul] using add_mem V_mem V_mem
      rw [GradedLND.proj_of_mem valuationPieces hm,sub_self]
  rw [he]
  simpa only [add_zero] using GradedLND.component_homogeneous valuationPieces fiberEuler 0 hr
lemma pullback_graded (i : ℤ) (r : Degeneration.G) (hr : r ∈ Degeneration.pieces i) :
    pullback r ∈ valuationPieces i := by
  obtain ⟨p,hp,rfl⟩ := hr
  change pullback (Degeneration.π p) ∈ valuationPieces i
  rw [pullback_π]
  apply GradedMap.mvpolynomial valuationPieces Degeneration.weight eval _ hp
  intro z
  fin_cases z
  · change eval (MvPolynomial.X 0) ∈ valuationPieces (-1)
    simpa only [eval,MvPolynomial.aeval_X,values,Matrix.cons_val_zero] using τ_mem
  · change eval (MvPolynomial.X 1) ∈ valuationPieces 0
    simpa only [eval,MvPolynomial.aeval_X,values,Matrix.cons_val_one,Matrix.cons_val_zero] using j_mem (inclusion Quadric.s)
  · change eval (MvPolynomial.X 2) ∈ valuationPieces 0
    simpa only [eval,MvPolynomial.aeval_X,values,Matrix.cons_val] using j_mem Determinant.u
  · change eval (MvPolynomial.X 3) ∈ valuationPieces 2
    have h := SetLike.mul_mem_graded (j_mem C₁) V_mem
    simpa only [zero_add,eval,MvPolynomial.aeval_X,values,Matrix.cons_val] using h
  · change eval (MvPolynomial.X 4) ∈ valuationPieces 2
    have h := SetLike.mul_mem_graded (j_mem (b^2)) V_mem
    simpa only [zero_add,eval,MvPolynomial.aeval_X,values,Matrix.cons_val] using h
end ComplexCancellation.Bundle

end

end OAI
