import OAI.Analysis.OperatorAlgebra.GNSVectorDensity
import OAI.Analysis.TracialSplitting.GNSRepresentations

namespace OAI

/-! Vector formulas determine the left and right actions on the full GNS space. -/
noncomputable section
open scoped ComplexOrder Topology
namespace WeakPureInfiniteness

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma gnsVector_left (f : A →ₚ[ℂ] ℂ) (a b : A) :
    f.gnsStarAlgHom a (gnsVector f b) = gnsVector f (a * b) := by
  change f.gnsNonUnitalStarAlgHom a (f.toPreGNS b : f.GNS) = _
  rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe]
  simp only [PositiveLinearMap.leftMulMapPreGNS_apply,
    PositiveLinearMap.ofPreGNS_toPreGNS, gnsVector]

lemma gnsVector_right (f : A →ₚ[ℂ] ℂ) (ht : ∀ a b, f (a * b) = f (b * a))
    (a b : A) :
    NuclearTrace.rightGNS f ht (MulOpposite.op b) (gnsVector f a) =
      gnsVector f (a * b) := by
  change NuclearTrace.rightGNS f ht (MulOpposite.op b) (f.toPreGNS a : f.GNS) = _
  rw [NuclearTrace.rightGNS_coe]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS, MulOpposite.unop_op, gnsVector]

omit [CompleteSpace H] in
lemma gns_left_intertwines (f : A →ₚ[ℂ] ℂ) (V : gnsHilbert f →ₗᵢ[ℂ] H)
    (a : A) (T : H →L[ℂ] H)
    (hT : ∀ b : A, T (V (gnsVector f b)) = V (gnsVector f (a * b)))
    (x : gnsHilbert f) : T (V x) = V (f.gnsStarAlgHom a x) := by
  apply gnsVector_induction_on f x
  · exact isClosed_eq (T.continuous.comp V.continuous)
      (V.continuous.comp (f.gnsStarAlgHom a).continuous)
  · intro b
    rw [gnsVector_left]
    exact hT b

omit [CompleteSpace H] in
lemma gns_right_intertwines (f : A →ₚ[ℂ] ℂ)
    (ht : ∀ a b, f (a * b) = f (b * a)) (V : gnsHilbert f →ₗᵢ[ℂ] H)
    (b : A) (T : H →L[ℂ] H)
    (hT : ∀ a : A, T (V (gnsVector f a)) = V (gnsVector f (a * b)))
    (x : gnsHilbert f) :
    T (V x) = V (NuclearTrace.rightGNS f ht (MulOpposite.op b) x) := by
  apply gnsVector_induction_on f x
  · exact isClosed_eq (T.continuous.comp V.continuous)
      (V.continuous.comp (NuclearTrace.rightGNS f ht (MulOpposite.op b)).continuous)
  · intro a
    rw [gnsVector_right]
    exact hT a

omit [CompleteSpace H] in
lemma gns_left_intertwines_of_vector_formula (f : A →ₚ[ℂ] ℂ)
    (V : gnsHilbert f →ₗᵢ[ℂ] H) (c : ℂ) (v : A → H)
    (hV : ∀ a, V (gnsVector f a) = c • v a)
    (a : A) (T : H →L[ℂ] H) (hv : ∀ b, T (v b) = v (a * b))
    (x : gnsHilbert f) : T (V x) = V (f.gnsStarAlgHom a x) := by
  apply gns_left_intertwines f V a T
  intro b
  calc
    T (V (gnsVector f b)) = T (c • v b) := congrArg T (hV b)
    _ = c • T (v b) := T.map_smul c (v b)
    _ = c • v (a * b) := congrArg (fun z => c • z) (hv b)
    _ = V (gnsVector f (a * b)) := (hV (a * b)).symm

omit [CompleteSpace H] in
lemma gns_right_intertwines_of_vector_formula (f : A →ₚ[ℂ] ℂ)
    (ht : ∀ a b, f (a * b) = f (b * a))
    (V : gnsHilbert f →ₗᵢ[ℂ] H) (c : ℂ) (v : A → H)
    (hV : ∀ a, V (gnsVector f a) = c • v a)
    (b : A) (T : H →L[ℂ] H) (hv : ∀ a, T (v a) = v (a * b))
    (x : gnsHilbert f) : T (V x) = V (NuclearTrace.rightGNS f ht (MulOpposite.op b) x) := by
  apply gns_right_intertwines f ht V b T
  intro a
  calc
    T (V (gnsVector f a)) = T (c • v a) := congrArg T (hV a)
    _ = c • T (v a) := T.map_smul c (v a)
    _ = c • v (a * b) := congrArg (fun z => c • z) (hv a)
    _ = V (gnsVector f (a * b)) := (hV (a * b)).symm

end WeakPureInfiniteness

end

end OAI
