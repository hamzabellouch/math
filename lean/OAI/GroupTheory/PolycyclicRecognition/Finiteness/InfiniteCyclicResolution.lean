import OAI.GroupTheory.PolycyclicRecognition.Algebra.InfiniteCyclicDifference
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteIntegralRepresentations
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

namespace OAI

/-! # A finite free resolution for an infinite cyclic group -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits ZeroObject
open scoped MonoidAlgebra

-- Use the scalar structure stored in a representation, including for integer scalars.
attribute [local instance 2000] Rep.hV2

variable (G : Type) [CommGroup G]

def cyclicDifference (g : G) : Rep.leftRegular ℤ G ⟶ Rep.leftRegular ℤ G :=
  (Rep.leftRegular ℤ G).applyAsHom g - 𝟙 _

def cyclicAugmentation : Rep.leftRegular ℤ G ⟶ trivialIntegral G :=
  Rep.leftRegularHom _ 1

theorem cyclicDifference_augmentation (g : G) :
    cyclicDifference G g ≫ cyclicAugmentation G = 0 := by
  apply Rep.hom_ext
  apply DFunLike.ext
  intro x
  change integralAugmentation G (Representation.leftRegular ℤ G g x - x) = 0
  rw [map_sub, integralAugmentation_leftRegular, sub_self]

def infiniteCyclicObjects : ℕ → Rep ℤ G
  | 0 => Rep.leftRegular ℤ G
  | 1 => Rep.leftRegular ℤ G
  | _ + 2 => 0

def infiniteCyclicDifferentials (g : G) :
    ∀ i, infiniteCyclicObjects G (i + 1) ⟶ infiniteCyclicObjects G i
  | 0 => cyclicDifference G g
  | _ + 1 => 0

def infiniteCyclicComplex (g : G) : ChainComplex (Rep ℤ G) ℕ :=
  ChainComplex.of (infiniteCyclicObjects G) (infiniteCyclicDifferentials G g)
    (fun i => by cases i <;> exact zero_comp)

def infiniteCyclicAugmentation (g : G) :
    infiniteCyclicComplex G g ⟶ (ChainComplex.single₀ (Rep ℤ G)).obj (trivialIntegral G) :=
  ((infiniteCyclicComplex G g).toSingle₀Equiv _).symm
    ⟨cyclicAugmentation G, by
      change (𝟙 (Rep.leftRegular ℤ G) ≫ cyclicDifference G g) ≫ cyclicAugmentation G = 0
      simpa only [Category.id_comp] using cyclicDifference_augmentation G g⟩

instance (g : G) (i : ℕ) : Projective ((infiniteCyclicComplex G g).X i) := by
  rcases i with _ | _ | i
  · change Projective (Rep.leftRegular ℤ G)
    infer_instance
  · change Projective (Rep.leftRegular ℤ G)
    infer_instance
  · change Projective (0 : Rep ℤ G)
    infer_instance

theorem infiniteCyclicComplex_exactAt [Infinite G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (i : ℕ) :
    (infiniteCyclicComplex G g).ExactAt (i + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (i + 2) (i + 1) i (by simp) (by simp)]
  cases i with
  | zero =>
      apply (forget₂ (Rep ℤ G) (ModuleCat ℤ)).reflects_exact_of_faithful
      rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
      simp only [infiniteCyclicComplex]
      change LinearMap.range (0 : (0 : Rep ℤ G) →ₗ[ℤ] ℤ[G]) =
        LinearMap.ker (Representation.leftRegular ℤ G g - LinearMap.id)
      rw [LinearMap.range_zero, LinearMap.ker_eq_bot.mpr
        (leftRegular_difference_injective g hg)]
  | succ i =>
      exact ShortComplex.exact_of_isZero_X₂ _
        (isZero_zero _)

theorem infiniteCyclicAugmentation_quasiIso [Infinite G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    QuasiIso (infiniteCyclicAugmentation G g) where
  quasiIsoAt i := by
    cases i with
    | zero =>
        rw [ChainComplex.quasiIsoAt₀_iff,
          ShortComplex.quasiIso_iff_of_zeros' _ (by rfl) rfl rfl]
        constructor
        · apply (forget₂ (Rep ℤ G) (ModuleCat ℤ)).reflects_exact_of_faithful
          rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
          change LinearMap.range (Representation.leftRegular ℤ G g - LinearMap.id) =
            LinearMap.ker (integralAugmentation G)
          exact (integralAugmentation_ker_of_cyclic G g hg).symm
        · rw [Rep.epi_iff_surjective]
          intro r
          use MonoidAlgebra.single 1 r
          change integralAugmentation G (MonoidAlgebra.single 1 r) = r
          exact integralAugmentation_single G 1 r
    | succ i =>
        rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..)]
        exact infiniteCyclicComplex_exactAt G g hg i

def infiniteCyclicResolution [Infinite G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) : ProjectiveResolution (trivialIntegral G) where
  complex := infiniteCyclicComplex G g
  π := infiniteCyclicAugmentation G g
  quasiIso := infiniteCyclicAugmentation_quasiIso G g hg

end PolycyclicRecognition

end

end OAI
