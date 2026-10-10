import OAI.GroupTheory.PolycyclicRecognition.Lattices.KernelCompletionHeight
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorExtensionTopology
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace OAI

/-! # The completion embeds the original topology

The integer quotient is recovered continuously from the real height. On each
fiber a continuous linear left inverse recovers the original kernel coordinate.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
attribute [local instance] factorExtensionTopology
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n : ℕ}
  (R : NonabelianFactorSystem L (IntegralLatticeGroup n))
  (C : NilpotentKernelCompletion (FactorExtension.inl R))
  (π : C.carrier →* AbelianRealSpace n)
  (hπ : ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, AbelianRealSpace n)) ∞ π)
  (he : ∀ a, π (C.embed a) = integralRealHeight a.right)

local instance completionEmbeddingTopologicalGroup : IsTopologicalGroup C.carrier :=
  topologicalGroup_of_lieGroup (𝓘(ℝ, C.carrier)) ⊤

theorem completion_factorization (a : FactorExtension R) :
    C.embed a = C.embed (FactorExtension.inl R a.left) *
      C.embed (⟨1, a.right⟩ : FactorExtension R) := by
  rw [← map_mul]
  apply congrArg C.embed
  apply FactorExtension.ext
  · change a.left = a.left * R.action 1 1 * R.factor 1 a.right
    rw [map_one, R.factor_one_left, mul_one, mul_one]
  · exact (one_mul _).symm

theorem kernelCompletion_continuous : Continuous C.embed := by
  have hs : Continuous (fun q : IntegralLatticeGroup n => C.embed (⟨1, q⟩ : FactorExtension R)) :=
    continuous_of_discreteTopology
  have hc := (C.kernel_smooth.continuous.comp (continuous_factor_left R)).mul
    (hs.comp (continuous_factor_right R))
  exact hc.congr (fun a => (completion_factorization R C a).symm)

include hπ he in
theorem kernelCompletion_isEmbedding : Topology.IsEmbedding C.embed := by
  let j := (polynomialModelLieHom (C.embed.comp (FactorExtension.inl R)) C.kernel_smooth).toLinearMap
  have hj (x : L) : j x = C.embed (FactorExtension.inl R x) :=
    polynomialModelLieHom_apply _ C.kernel_smooth x
  have hji : Function.Injective j := by
    intro x y h
    apply FactorExtension.inl_injective R
    apply C.injective
    exact (hj x).symm.trans (h.trans (hj y))
  obtain ⟨l, hl⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hji)
  let e : FactorExtension R ≃* C.embed.range := MonoidHom.ofInjective C.injective
  have hlat (x : C.embed.range) : π x.val ∈ abelianRealLattice n := by
    obtain ⟨a, ha⟩ := x.property
    rw [← ha, he]
    exact integerVectorMap_mem n a.right.toAdd
  let q : C.embed.range → IntegralLatticeGroup n := fun x =>
    (abelianRealLatticeEquiv n).symm ⟨π x.val, hlat x⟩
  have hq (a : FactorExtension R) : q (e a) = a.right := by
    apply (abelianRealLatticeEquiv n).injective
    apply Subtype.ext
    change ((abelianRealLatticeEquiv n) ((abelianRealLatticeEquiv n).symm
      ⟨π (C.embed a), hlat (e a)⟩) : AbelianRealSpace n) = _
    rw [MulEquiv.apply_symm_apply]
    exact he a
  have hqc : Continuous q := by
    let := (abelianRealLattice_uniform n).1
    exact (continuous_of_discreteTopology : Continuous (abelianRealLatticeEquiv n).symm).comp
      ((hπ.continuous.comp continuous_subtype_val).subtype_mk hlat)
  let r : C.embed.range → L := fun x => l
    (x.val * (C.embed (⟨1, q x⟩ : FactorExtension R))⁻¹)
  have hr (a : FactorExtension R) : r (e a) = a.left := by
    change l (C.embed a * (C.embed (⟨1, q (e a)⟩ : FactorExtension R))⁻¹) = a.left
    rw [hq, completion_factorization R C a, mul_inv_cancel_right, ← hj]
    exact LinearMap.congr_fun hl a.left
  have hrc : Continuous r := by
    have hs : Continuous (fun q : IntegralLatticeGroup n => C.embed (⟨1, q⟩ : FactorExtension R)) :=
      continuous_of_discreteTopology
    exact l.toContinuousLinearMap.continuous.comp
      (continuous_subtype_val.mul (hs.comp hqc).inv)
  have hinv : (e.symm : C.embed.range → FactorExtension R) = fun x => ⟨r x, q x⟩ := by
    funext x
    obtain ⟨a, rfl⟩ := e.surjective x
    rw [e.symm_apply_apply, hr, hq]
  have hei : Continuous e.symm := by
    rw [hinv]
    exact (factorExtensionHomeomorph R).symm.continuous.comp (hrc.prodMk hqc)
  let homeo : FactorExtension R ≃ₜ C.embed.range :=
    { e.toEquiv with
      continuous_toFun := (kernelCompletion_continuous R C).subtype_mk _
      continuous_invFun := hei }
  exact Topology.IsEmbedding.subtypeVal.comp homeo.isEmbedding

end PolycyclicRecognition

end

end OAI
