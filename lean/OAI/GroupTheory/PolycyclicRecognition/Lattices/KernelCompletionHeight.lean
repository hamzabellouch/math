import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentIntegralKernelCompletion
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianRealSpace
import OAI.GroupTheory.PolycyclicRecognition.Lattices.IntegralLatticeGenerators
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace OAI

/-! # The real quotient of a nilpotent kernel completion

The quotient homomorphism extends to the constructed completion. Its kernel
is exactly the original real kernel, by the dimension retained in the cyclic
construction. No exactness property is postulated for the completion.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {K G : Type} [RealNormedLieAlgebra K] [FiniteDimensional ℝ K]
  [PK : PolynomialExponentialCoordinates K] [Group G] {n : ℕ}

def integralRealHeight : IntegralLatticeGroup n →* AbelianRealSpace n where
  toFun z := integerVectorMap n z.toAdd
  map_one' := (integerVectorMap n).map_zero
  map_mul' z w := (integerVectorMap n).map_add z.toAdd w.toAdd

theorem integralRealHeight_injective : Function.Injective (integralRealHeight (n := n)) := by
  intro z w h
  exact Multiplicative.ext (integerVectorMap_injective n h)

theorem integralRealHeight_range :
    (integralRealHeight (n := n)).range = abelianRealLattice n := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact integerVectorMap_mem n z.toAdd
  · intro hx
    obtain ⟨z, hz⟩ := (abelianRealLatticeEquiv n).surjective ⟨x, hx⟩
    exact ⟨z, congrArg Subtype.val hz⟩

namespace NilpotentKernelCompletion
variable (E : GroupExtension K G (IntegralLatticeGroup n))
  (C : NilpotentKernelCompletion E.inl)

theorem exists_height :
    ∃ π : C.carrier →* AbelianRealSpace n,
      ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, AbelianRealSpace n)) ∞ π ∧
      ∀ g, π (C.embed g) = integralRealHeight (E.rightHom g) := by
  apply C.extend (AbelianRealSpace n) (integralRealHeight.comp E.rightHom)
  have he : (integralRealHeight.comp E.rightHom).comp E.inl =
      (1 : K →* AbelianRealSpace n) := by
    ext x
    simp only [MonoidHom.comp_apply, E.rightHom_inl, map_one, MonoidHom.one_apply]
  rw [he]
  exact contMDiff_const

variable (π : C.carrier →* AbelianRealSpace n)
  (hπ : ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, AbelianRealSpace n)) ∞ π)
  (he : ∀ g, π (C.embed g) = integralRealHeight (E.rightHom g))

include hπ he in
theorem height_surjective : Function.Surjective π := by
  let f := (polynomialModelLieHom π hπ).toLinearMap
  have hr : LinearMap.range f = ⊤ := by
    apply top_unique
    have hb : Submodule.span ℝ (Set.range (Pi.basisFun ℝ (Fin n))) =
        (⊤ : Submodule ℝ (AbelianRealSpace n)) := (Pi.basisFun ℝ (Fin n)).span_eq
    rw [← hb]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    obtain ⟨g, hg⟩ := E.rightHom_surjective (integralLatticeGenerator n j)
    refine ⟨C.embed g, ?_⟩
    change polynomialModelLieHom π hπ (C.embed g) = _
    rw [polynomialModelLieHom_apply, he, hg]
    exact integerVectorMap_basis j
  intro x
  obtain ⟨y, hy⟩ := (LinearMap.range_eq_top.mp hr) x
  exact ⟨y, (polynomialModelLieHom_apply π hπ y).symm.trans hy⟩

include hπ he in
theorem height_kernel_eq
    (hdim : C.dimension = Module.finrank ℝ K + n) :
    π.ker = (C.embed.comp E.inl).range := by
  let f := (polynomialModelLieHom π hπ).toLinearMap
  let k := (polynomialModelLieHom (C.embed.comp E.inl) C.kernel_smooth).toLinearMap
  have hk : Function.Injective k := by
    intro x y h
    apply E.inl_injective
    apply C.injective
    exact (polynomialModelLieHom_apply _ C.kernel_smooth x).symm.trans
      (h.trans (polynomialModelLieHom_apply _ C.kernel_smooth y))
  have hle : LinearMap.range k ≤ LinearMap.ker f := by
    rintro _ ⟨x, rfl⟩
    change polynomialModelLieHom π hπ (polynomialModelLieHom _ C.kernel_smooth x) = 0
    rw [polynomialModelLieHom_apply, polynomialModelLieHom_apply]
    change π (C.embed (E.inl x)) = 0
    rw [he, E.rightHom_inl, map_one]
    rfl
  have hfdim : Module.finrank ℝ (LinearMap.ker f) = Module.finrank ℝ K := by
    have hsurj : Function.Surjective f := by
      intro x
      obtain ⟨y, hy⟩ := C.height_surjective E π hπ he x
      exact ⟨y, (polynomialModelLieHom_apply π hπ y).trans hy⟩
    have hr := LinearMap.finrank_range_add_finrank_ker f
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hr
    have hn : Module.finrank ℝ (AbelianRealSpace n) = n := by
      change Module.finrank ℝ (Fin n → ℝ) = n
      simp
    have hc : Module.finrank ℝ C.carrier = C.dimension := by
      simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis C.basis
    rw [hn, hc, hdim] at hr
    omega
  have hkr : LinearMap.range k = LinearMap.ker f :=
    Submodule.eq_of_le_of_finrank_eq hle
      ((LinearMap.finrank_range_of_inj hk).trans hfdim.symm)
  ext y
  change π y = 1 ↔ ∃ x, C.embed (E.inl x) = y
  constructor
  · intro hy
    have hy' : y ∈ LinearMap.ker f := by
      change polynomialModelLieHom π hπ y = 0
      rw [polynomialModelLieHom_apply, hy]
      rfl
    rw [← hkr] at hy'
    obtain ⟨x, hx⟩ := hy'
    exact ⟨x, (polynomialModelLieHom_apply _ C.kernel_smooth x).symm.trans hx⟩
  · rintro ⟨x, rfl⟩
    rw [he, E.rightHom_inl, map_one]

include hπ he in
theorem embed_range_eq_height_lattice
    (hdim : C.dimension = Module.finrank ℝ K + n) :
    C.embed.range = (abelianRealLattice n).comap π := by
  rw [← integralRealHeight_range]
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨E.rightHom g, (he g).symm⟩
  · rintro ⟨q, hq⟩
    obtain ⟨g, hg⟩ := E.rightHom_surjective q
    have hk : x * (C.embed g)⁻¹ ∈ π.ker := by
      change π (x * (C.embed g)⁻¹) = 1
      rw [map_mul, map_inv, he, hg, ← hq, mul_inv_cancel]
    rw [C.height_kernel_eq E π hπ he hdim] at hk
    obtain ⟨k, hk⟩ := hk
    refine ⟨E.inl k * g, ?_⟩
    rw [map_mul, show C.embed (E.inl k) = x * (C.embed g)⁻¹ from hk]
    exact inv_mul_cancel_right x (C.embed g)

end NilpotentKernelCompletion
end PolycyclicRecognition

end

end OAI
