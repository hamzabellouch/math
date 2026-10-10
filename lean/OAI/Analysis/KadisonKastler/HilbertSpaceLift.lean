import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry

namespace OAI

/-! # The complex Hilbert structure on a universe lift -/

namespace KadisonKastler

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

instance hilbertULiftInner : InnerProductSpace ℂ (ULift.{v} H) where
  toNormedSpace := inferInstance
  inner x y := inner ℂ x.down y.down
  norm_sq_eq_re_inner x := InnerProductSpace.norm_sq_eq_re_inner x.down
  conj_inner_symm x y := InnerProductSpace.conj_inner_symm x.down y.down
  add_left x y z := InnerProductSpace.add_left x.down y.down z.down
  smul_left x y r := InnerProductSpace.smul_left x.down y.down r

theorem hilbertULift_separable [TopologicalSpace.SeparableSpace H] :
    TopologicalSpace.SeparableSpace (ULift.{v} H) :=
  DenseRange.separableSpace (α := H) (β := ULift.{v} H)
    (f := (LinearIsometryEquiv.ulift ℂ H).symm)
    (LinearIsometryEquiv.ulift ℂ H).symm.surjective.denseRange
    (LinearIsometryEquiv.ulift ℂ H).symm.continuous

end

end KadisonKastler

end OAI
