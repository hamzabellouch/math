import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothIndividualRotations

namespace OAI

/-! # The compact rotation has its prescribed tangent action -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
  (β : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H →* MulAut G)
  (hβ : ∀ z (x : T.kernelIdeal) d,
    β z (F.inclusionN (F.ExpN (F.N.equiv x)) * F.inclusionD d) =
      F.inclusionN (F.ExpN (F.N.equiv (T.nilradicalRotation H z x))) * F.inclusionD d)

include hExp hβ in
theorem mfderiv_rotation_nilradical
    (z : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H) (x : T.kernelIdeal) :
    mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (β z) 1 x.1 = (T.nilradicalRotation H z x).1 := by
  apply mfderiv_hom_eq_of_exponential_line hExp (β z).toMonoidHom
    ((F.contMDiff_individual_rotation hExp β hβ z).mdifferentiableAt (by simp))
  intro t
  have hh := F.rotation_exp_nilradical β hβ z (t • x)
  simpa only [MulEquiv.coe_toMonoidHom,map_smul,SetLike.val_smul] using hh

include hExp hβ in
theorem mfderiv_rotation_cartan
    (z : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H) (h : H) :
    mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (β z) 1 h.1 = h.1 := by
  apply mfderiv_hom_eq_of_exponential_line hExp (β z).toMonoidHom
    ((F.contMDiff_individual_rotation hExp β hβ z).mdifferentiableAt (by simp))
  intro t
  exact F.rotation_exp_cartan β hβ z (t • h)

include hExp hβ in
theorem mfderiv_individual_rotation
    (z : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H)
    (x : GroupLieAlgebra (𝓘(ℝ,E)) G) :
    mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (β z) 1 x =
      realTorusOperator (GroupLieAlgebra (𝓘(ℝ,E)) G) H z x := by
  let A : E →L[ℝ] E := mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (β z) 1
  have hn := F.mfderiv_rotation_nilradical hExp β hβ z (T.kernelComponent H x)
  have hh := F.mfderiv_rotation_cartan hExp β hβ z (T.cartanComponent H x)
  have hsplit := (congrArg A (T.factorComponents_add H x).symm).trans
    (A.map_add (T.kernelComponent H x).1 (T.cartanComponent H x).1)
  have hsum := hsplit.trans (congrArg₂ (fun u v : E => u + v) hn hh)
  have hrot : (T.nilradicalRotation H z (T.kernelComponent H x)).1 +
      (T.cartanComponent H x).1 = realTorusOperator (GroupLieAlgebra (𝓘(ℝ,E)) G) H z x := by
    change realTorusOperator _ H z (T.kernelComponent H x).1 + (T.cartanComponent H x).1 = _
    rw [← realTorusOperator_fixes_cartan _ H z (T.cartanComponent H x), ← map_add,
      T.factorComponents_add H]
  exact hsum.trans hrot

include hExp hβ in
theorem rotation_commutes_exponential
    (z : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H)
    (x : GroupLieAlgebra (𝓘(ℝ,E)) G) :
    β z (Exp x) = Exp (realTorusOperator (GroupLieAlgebra (𝓘(ℝ,E)) G) H z x) := by
  have hh := hExp.map_of_mdifferentiable hExp (β z).toMonoidHom
    ((F.contMDiff_individual_rotation hExp β hβ z).mdifferentiable (by simp)) x
  calc
    β z (Exp x) = Exp (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (β z) 1 x) := hh
    _ = Exp (realTorusOperator (GroupLieAlgebra (𝓘(ℝ,E)) G) H z x) :=
      congrArg Exp (F.mfderiv_individual_rotation hExp β hβ z x)

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
