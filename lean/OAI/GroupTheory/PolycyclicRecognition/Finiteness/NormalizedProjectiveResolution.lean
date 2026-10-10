import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CompletedCohomologyProjective
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RepCofiber

namespace OAI

/-! # The projective resolution determined by normalized free covers

Its quotient syzygy in degree n is the actual n-fold normalized kernel used
in the complete-cohomology construction.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

def normalizedFreeStep (A : Rep.{0} ℤ G) :
    normalizedFreeRepresentation (normalizedSyzygy A) ⟶ normalizedFreeRepresentation A :=
  normalizedFreeAugmentation (normalizedSyzygy A) ≫ kernel.ι (normalizedFreeAugmentation A)

theorem normalizedFreeStep_comp (A : Rep.{0} ℤ G) :
    normalizedFreeStep A ≫ normalizedFreeAugmentation A = 0 := by
  simp [normalizedFreeStep]

theorem normalizedFreeStep_exact (A : Rep.{0} ℤ G) :
    (ShortComplex.mk (normalizedFreeStep A) (normalizedFreeAugmentation A)
      (normalizedFreeStep_comp A)).Exact := by
  apply (rep_shortComplex_exact_iff _).mpr
  intro x hx
  obtain ⟨k, hk⟩ := (rep_shortComplex_exact_iff _).mp
    (normalizedSyzygySequence_shortExact A).exact x hx
  obtain ⟨p, hp⟩ := (Rep.epi_iff_surjective
    (normalizedFreeAugmentation (normalizedSyzygy A))).mp inferInstance k
  refine ⟨p, ?_⟩
  change (kernel.ι (normalizedFreeAugmentation A)).hom
    ((normalizedFreeAugmentation (normalizedSyzygy A)).hom p) = x
  rw [hp]
  exact hk

def normalizedResolutionTerm (A : Rep.{0} ℤ G) (n : ℕ) : Rep.{0} ℤ G :=
  normalizedFreeRepresentation ((iteratedNormalizedSyzygy n).obj A)

def normalizedResolutionDifferential (A : Rep.{0} ℤ G) (n : ℕ) :
    normalizedResolutionTerm A (n + 1) ⟶ normalizedResolutionTerm A n :=
  normalizedFreeStep ((iteratedNormalizedSyzygy n).obj A)

def normalizedResolutionComplex (A : Rep.{0} ℤ G) : ChainComplex (Rep.{0} ℤ G) ℕ :=
  ChainComplex.of (normalizedResolutionTerm A) (normalizedResolutionDifferential A) (by
    intro n
    let B := (iteratedNormalizedSyzygy n).obj A
    change normalizedFreeStep (normalizedSyzygy B) ≫
      (normalizedFreeAugmentation (normalizedSyzygy B) ≫
        kernel.ι (normalizedFreeAugmentation B)) = 0
    rw [← Category.assoc, normalizedFreeStep_comp, zero_comp])

@[simp]
theorem normalizedResolutionComplex_d (A : Rep.{0} ℤ G) (n : ℕ) :
    (normalizedResolutionComplex A).d (n + 1) n =
      normalizedFreeStep ((iteratedNormalizedSyzygy n).obj A) := by
  exact ChainComplex.of_d (normalizedResolutionTerm A) (normalizedResolutionDifferential A) n

instance normalizedResolutionComplex_projective (A : Rep.{0} ℤ G) (n : ℕ) :
    Projective ((normalizedResolutionComplex A).X n) :=
  inferInstanceAs (Projective (normalizedFreeRepresentation ((iteratedNormalizedSyzygy n).obj A)))

theorem normalizedResolutionComplex_exact (A : Rep.{0} ℤ G) (n : ℕ) :
    (normalizedResolutionComplex A).ExactAt (n + 1) := by
  rw [exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  apply (rep_shortComplex_exact_iff _).mpr
  intro x hx
  change ((normalizedResolutionComplex A).d (n + 1) n).hom x = 0 at hx
  rw [normalizedResolutionComplex_d] at hx
  have hx' : (normalizedFreeAugmentation ((iteratedNormalizedSyzygy (n + 1)).obj A)).hom x = 0 := by
    apply (Rep.mono_iff_injective
      (kernel.ι (normalizedFreeAugmentation ((iteratedNormalizedSyzygy n).obj A)))).mp
      inferInstance
    change (kernel.ι (normalizedFreeAugmentation ((iteratedNormalizedSyzygy n).obj A))).hom
      ((normalizedFreeAugmentation ((iteratedNormalizedSyzygy (n + 1)).obj A)).hom x) = 0 at hx
    exact hx.trans (map_zero (kernel.ι (normalizedFreeAugmentation
      ((iteratedNormalizedSyzygy n).obj A))).hom).symm
  change ∃ y, ((normalizedResolutionComplex A).d (n + 2) (n + 1)).hom y = x
  rw [show n + 2 = (n + 1) + 1 by omega, normalizedResolutionComplex_d]
  exact (rep_shortComplex_exact_iff _).mp
    (normalizedFreeStep_exact ((iteratedNormalizedSyzygy (n + 1)).obj A)) x hx'

def normalizedResolutionAugmentation (A : Rep.{0} ℤ G) :
    normalizedResolutionComplex A ⟶ (ChainComplex.single₀ (Rep.{0} ℤ G)).obj A :=
  ((normalizedResolutionComplex A).toSingle₀Equiv A).symm
    ⟨normalizedFreeAugmentation A, by
      rw [normalizedResolutionComplex_d]
      exact normalizedFreeStep_comp A⟩

theorem normalizedResolutionAugmentation_quasiIso (A : Rep.{0} ℤ G) :
    QuasiIso (normalizedResolutionAugmentation A) where
  quasiIsoAt i := by
    cases i with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,
        ShortComplex.quasiIso_iff_of_zeros' _ (by rfl) rfl rfl]
      constructor
      · exact normalizedFreeStep_exact A
      · exact normalizedFreeAugmentation_epi A
    | succ n =>
      rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..)]
      exact normalizedResolutionComplex_exact A n

def normalizedProjectiveResolution (A : Rep.{0} ℤ G) : ProjectiveResolution A where
  complex := normalizedResolutionComplex A
  projective := normalizedResolutionComplex_projective A
  π := normalizedResolutionAugmentation A
  quasiIso := normalizedResolutionAugmentation_quasiIso A

end PolycyclicRecognition

end

end OAI
