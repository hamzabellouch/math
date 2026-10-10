import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentKernelCompletion
import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentCyclicHomExtension
import OAI.GroupTheory.PolycyclicRecognition.Lattices.IntegerSemidirectLattice

namespace OAI

/-! # Extending homomorphisms after one cyclic completion step -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {K H M : Type} [RealNormedLieAlgebra K] [FiniteDimensional ℝ K]
  [PK : PolynomialExponentialCoordinates K] [Group H]
  [RealNormedLieAlgebra M] [FiniteDimensional ℝ M]
  [PM : PolynomialExponentialCoordinates M] [LieRing.IsNilpotent M]
  {i : K →* H} (C : NilpotentKernelCompletion i)

theorem kernelCompletion_cyclic_hom (a : MulAut H)
    (A : C.carrier ≃ₗ⁅ℝ⁆ C.carrier) (hA : IsNilpotent (A.toLinearMap - 1))
    (hAe : ∀ h, A (C.embed h) = C.embed (a h))
    (F : (H ⋊[integerPowerAction a] Multiplicative ℤ) →* M)
    (hF : ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, M)) ∞ ((F.comp SemidirectProduct.inl).comp i)) :
    let D := unipotentLieLogarithm A hA
    let hD := unipotentLieLogarithm_nilpotent A hA
    letI := derivationSemidirectGroup D hD
    letI : MulOneClass (C.carrier × ℝ) := (derivationSemidirectGroup D hD).toMulOneClass
    ∃ φ : (C.carrier × ℝ) →* M,
      ContMDiff (𝓘(ℝ, C.carrier × ℝ)) (𝓘(ℝ, M)) ∞ φ ∧
      ∀ (h : H) (n : ℤ), φ (C.embed h, (n : ℝ)) = F ⟨h, Multiplicative.ofAdd n⟩ := by
  obtain ⟨f, hf, hfe⟩ := C.extend M (F.comp SemidirectProduct.inl) hF
  simp only [MonoidHom.comp_apply] at hfe
  let t : H ⋊[integerPowerAction a] Multiplicative ℤ :=
    SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ))
  let u := F t
  have hconj (h : H) : F (SemidirectProduct.inl (a h)) =
      u * F (SemidirectProduct.inl h) * u⁻¹ := by
    have hh := SemidirectProduct.inl_aut (φ := integerPowerAction a)
      (Multiplicative.ofAdd (1 : ℤ)) h
    rw [map_inv] at hh
    change SemidirectProduct.inl ((a ^ (1 : ℤ)) h) = t * SemidirectProduct.inl h * t⁻¹ at hh
    simpa only [zpow_one, map_mul, map_inv] using congrArg F hh
  let B := PolynomialExponentialCoordinates.groupAutomorphism A
  have hb : ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, C.carrier)) ∞ B :=
    A.toLinearMap.toContinuousLinearMap.contDiff.contMDiff
  have hu : ContMDiff (𝓘(ℝ, M)) (𝓘(ℝ, M)) ∞ (MulAut.conj u) :=
    (contMDiff_conjugation u).of_le (by simp)
  have heq : f.comp B.toMonoidHom = (MulAut.conj u).toMonoidHom.comp f := by
    apply C.hom_ext M (f.comp B.toMonoidHom) ((MulAut.conj u).toMonoidHom.comp f)
      (hf.comp hb) (hu.comp hf)
    intro h
    change f (A (C.embed h)) = u * f (C.embed h) * u⁻¹
    rw [hAe, hfe, hfe]
    exact hconj h
  let fL := polynomialModelLieHom f hf
  have hL (x : C.carrier) : fL (A x) = u * fL x * u⁻¹ := by
    rw [polynomialModelLieHom_apply, polynomialModelLieHom_apply]
    exact DFunLike.congr_fun heq x
  obtain ⟨φ, hφ, hφx⟩ := nilpotent_cyclic_hom_extension A hA fL u hL
  refine ⟨φ, hφ, ?_⟩
  intro h n
  rw [hφx, polynomialModelLieHom_apply, hfe, ← model_zpow, ← map_zpow, ← map_mul]
  congr 1
  have ht : t ^ n = SemidirectProduct.inr (Multiplicative.ofAdd n) := by
    rw [← map_zpow]
    congr 1
    apply Multiplicative.ext
    change n • (1 : ℤ) = n
    simp
  rw [ht]
  exact (SemidirectProduct.mk_eq_inl_mul_inr _ _).symm

end PolycyclicRecognition

end

end OAI
