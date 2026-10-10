import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRepresentationDescent
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentAlgebraRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RepresentedAdjoint
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AlgebraRepresentationDerivative

namespace OAI

/-! # Integrating a Lie representation through the Cartan factors

Uniqueness of exponential preimages meeting the root ideal suffices to descend
a nilpotently integrated representation through the factor product. Global
injectivity of the exponential gives a specialization.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G] [LocallyCompactSpace G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G}

omit [SimplyConnectedSpace G] in
theorem CartanFactorModel.exists_integrated_representation_of_root_preimages
    (F : CartanFactorModel H Exp)
    (hExp : IsGroupExponential Exp)
    (hinj : ∀ (x : GroupLieAlgebra (𝓘(ℝ, E)) G), x ∈ cartanRootIdeal H →
      ∀ y, Exp x = Exp y → x = y)
    (hn : LieRing.IsNilpotent (cartanRootIdeal H))
    (hspan : (cartanRootIdeal H).toSubmodule ⊔ H.toSubmodule = ⊤)
    (hsN : Function.Surjective F.ExpN) (hsD : Function.Surjective F.ExpD)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ A) :
    ∃ ρ : G →* Aˣ, Continuous ρ ∧ ∀ x, ρ (Exp x) = algebraExpUnit (j x) := by
  let : IsTopologicalGroup Aˣ := topologicalGroup_of_lieGroup (𝓘(ℝ, A)) ⊤
  obtain ⟨ρN, hρN, heN⟩ := F.N.exists_algebra_representation hn
    (j.comp (cartanRootIdeal H).incl)
  obtain ⟨ρD, hρD, heD⟩ := F.D.exists_algebra_representation inferInstance
    (j.comp H.incl)
  have hN (x : cartanRootIdeal H) :
      ρN (F.ExpN (F.N.equiv x)) = algebraExpUnit (j x) :=
    heN F.ExpN F.isExpN x
  have hD (x : H) : ρD (F.ExpD (F.D.equiv x)) = algebraExpUnit (j x) :=
    heD F.ExpD F.isExpD x
  have coverN (n : F.N.carrier) : ∃ x : cartanRootIdeal H, F.ExpN (F.N.equiv x) = n := by
    obtain ⟨v, rfl⟩ := hsN n
    exact ⟨F.N.equiv.symm v, by rw [F.N.equiv.apply_symm_apply]⟩
  have coverD (d : F.D.carrier) : ∃ x : H, F.ExpD (F.D.equiv x) = d := by
    obtain ⟨v, rfl⟩ := hsD d
    exact ⟨F.D.equiv.symm v, by rw [F.D.equiv.apply_symm_apply]⟩
  have hconj (d : F.D.carrier) (n : F.N.carrier) :
      ρN (F.action d n) = ρD d * ρN n * (ρD d)⁻¹ := by
    obtain ⟨x, rfl⟩ := coverD d
    obtain ⟨y, rfl⟩ := coverN n
    obtain ⟨z, hz⟩ := coverN (F.action (F.ExpD (F.D.equiv x)) (F.ExpN (F.N.equiv y)))
    have heq : (z : GroupLieAlgebra (𝓘(ℝ, E)) G) =
        adjointLinearMap (E := E) (Exp x)
          (y : GroupLieAlgebra (𝓘(ℝ, E)) G) := by
      apply hinj z z.property
      rw [← F.compatibleN z, hz, F.conjugation, F.compatibleD, F.compatibleN]
      exact conjugation_exponential hExp (Exp x) y
    rw [← hz, hN, hD, hN]
    rw [heq, lieHom_adjoint_exponential hExp j x y]
    exact algebraExpUnit_conj (algebraExpUnit (j x)) (j y)
  have hagree (n : F.N.carrier) (d : F.D.carrier)
      (he : F.inclusionN n = F.inclusionD d) : ρN n = ρD d := by
    obtain ⟨x, rfl⟩ := coverN n
    obtain ⟨y, rfl⟩ := coverD d
    rw [F.compatibleN, F.compatibleD] at he
    have hxy := hinj x x.property y he
    rw [hN, hD, hxy]
  obtain ⟨ρ, hρ, hprod⟩ := F.descend_representation ρN ρD
    hρN.continuous hρD.continuous hconj hagree
  have heN' (x : cartanRootIdeal H) : ρ (Exp x) = algebraExpUnit (j x) := by
    have h := hprod (F.ExpN (F.N.equiv x)) 1
    simpa only [map_one, mul_one, F.compatibleN, hN] using h
  have heD' (x : H) : ρ (Exp x) = algebraExpUnit (j x) := by
    have h := hprod 1 (F.ExpD (F.D.equiv x))
    simpa only [map_one, one_mul, F.compatibleD, hD] using h
  have hf := contMDiff_of_continuous_unitsHom hExp ρ (Units.continuous_val.comp hρ)
  have hdiffN (x : cartanRootIdeal H) : unitsHomLieDifferential ρ hf x = j x := by
    apply unitsHomLieDifferential_eq_of_exponential_line hExp ρ hf
    intro t
    have ht := heN' (t • x)
    change ρ (Exp (t • (x : GroupLieAlgebra (𝓘(ℝ, E)) G))) =
      algebraExpUnit (j (t • (x : GroupLieAlgebra (𝓘(ℝ, E)) G))) at ht
    rwa [map_smul] at ht
  have hdiffD (x : H) : unitsHomLieDifferential ρ hf x = j x := by
    apply unitsHomLieDifferential_eq_of_exponential_line hExp ρ hf
    intro t
    have ht := heD' (t • x)
    change ρ (Exp (t • (x : GroupLieAlgebra (𝓘(ℝ, E)) G))) =
      algebraExpUnit (j (t • (x : GroupLieAlgebra (𝓘(ℝ, E)) G))) at ht
    rwa [map_smul] at ht
  have hdiff : unitsHomLieDifferential ρ hf = j := by
    ext x
    have hx : x ∈ (cartanRootIdeal H).toSubmodule ⊔ H.toSubmodule := by
      rw [hspan]
      trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, map_add, hdiffN ⟨y, hy⟩, hdiffD ⟨z, hz⟩]
  refine ⟨ρ, hρ, fun x => ?_⟩
  have he := hom_exp_eq_algebraExpUnit hExp ρ
    (unitsHomLieDifferential ρ hf).toLinearMap.toContinuousLinearMap
    (hasMFDerivAt_unitsHomLieDifferential ρ hf) x
  change ρ (Exp x) = algebraExpUnit (unitsHomLieDifferential ρ hf x) at he
  rwa [hdiff] at he

omit [SimplyConnectedSpace G] in
/-- Global injectivity of the exponential specializes the factor descent theorem. -/
theorem CartanFactorModel.exists_integrated_representation
    (F : CartanFactorModel H Exp)
    (hExp : IsGroupExponential Exp) (hinj : Function.Injective Exp)
    (hn : LieRing.IsNilpotent (cartanRootIdeal H))
    (hspan : (cartanRootIdeal H).toSubmodule ⊔ H.toSubmodule = ⊤)
    (hsN : Function.Surjective F.ExpN) (hsD : Function.Surjective F.ExpD)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ A) :
    ∃ ρ : G →* Aˣ, Continuous ρ ∧ ∀ x, ρ (Exp x) = algebraExpUnit (j x) :=
  F.exists_integrated_representation_of_root_preimages hExp
    (fun _ _ _ he => hinj he) hn hspan hsN hsD j

end PolycyclicRecognition

end

end OAI
