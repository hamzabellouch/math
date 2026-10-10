import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteProjectivePresentations
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.IntegralAugmentation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RepCofiber

namespace OAI

/-! # A resolution with finitely generated covers whenever available

The initial free term is the regular module. Every subsequent term covers the
kernel of the preceding differential. The chosen presentation retains finite
generation whenever that kernel is finitely generated.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
variable {G : Type} [Group G]

abbrev integralFreeAugmentation : Rep.leftRegular ℤ G ⟶ trivialIntegral G :=
  Rep.leftRegularHom (trivialIntegral G) 1

def chosenIntegralKernelCover {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    ProjectivePresentation (kernel f) := chosenIntegralPresentation (kernel f)

def chosenIntegralStep {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    (chosenIntegralKernelCover f).p ⟶ A :=
  (chosenIntegralKernelCover f).f ≫ kernel.ι f

@[simp] theorem chosenIntegralStep_comp {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    chosenIntegralStep f ≫ f = 0 := by
  simp [chosenIntegralStep]

theorem chosenIntegralStep_exact {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    (ShortComplex.mk (chosenIntegralStep f) f (chosenIntegralStep_comp f)).Exact := by
  let S := ShortComplex.mk (chosenIntegralStep f) f (chosenIntegralStep_comp f)
  let T := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  let φ : S ⟶ T :=
    { τ₁ := (chosenIntegralKernelCover f).f
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [S, T, chosenIntegralStep]
      comm₂₃ := by simp [S, T] }
  have : Epi φ.τ₁ := (chosenIntegralKernelCover f).epi
  have : IsIso φ.τ₂ := by change IsIso (𝟙 _); infer_instance
  have : Mono φ.τ₃ := by change Mono (𝟙 _); infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel f))

def chosenIntegralSuccessor {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    Σ' (C : Rep.{0} ℤ G) (d : C ⟶ A), d ≫ f = 0 :=
  ⟨(chosenIntegralKernelCover f).p, chosenIntegralStep f, chosenIntegralStep_comp f⟩

def chosenIntegralResolutionComplex (G : Type) [Group G] : ChainComplex (Rep ℤ G) ℕ :=
  ChainComplex.mk' (Rep.leftRegular ℤ G)
    (chosenIntegralKernelCover (integralFreeAugmentation (G := G))).p
    (chosenIntegralStep (integralFreeAugmentation (G := G))) chosenIntegralSuccessor

def chosenIntegralResolutionSuccessorIso (n : ℕ) :
    (chosenIntegralResolutionComplex G).X (n + 2) ≅
      (chosenIntegralKernelCover ((chosenIntegralResolutionComplex G).d (n + 1) n)).p :=
  ChainComplex.mk'XIso _ _ _ _ n

theorem chosenIntegralResolution_step_finite (n : ℕ)
    (h : IntegralRepresentationFinite G
      (kernel ((chosenIntegralResolutionComplex G).d (n + 1) n))) :
    IntegralRepresentationFinite G ((chosenIntegralResolutionComplex G).X (n + 2)) :=
  (chosenIntegralPresentation_finite _ h).of_iso (chosenIntegralResolutionSuccessorIso n).symm

theorem chosenIntegralResolution_projective (n : ℕ) :
    Projective ((chosenIntegralResolutionComplex G).X n) := by
  rcases n with _ | (_ | n)
  · change Projective (Rep.leftRegular ℤ G)
    infer_instance
  · exact (chosenIntegralKernelCover (integralFreeAugmentation (G := G))).projective
  · exact Projective.of_iso (chosenIntegralResolutionSuccessorIso n).symm
      (chosenIntegralKernelCover ((chosenIntegralResolutionComplex G).d (n + 1) n)).projective

theorem chosenIntegralResolution_d_succ (n : ℕ) :
    (chosenIntegralResolutionComplex G).d (n + 2) (n + 1) =
      (chosenIntegralResolutionSuccessorIso n).hom ≫
        chosenIntegralStep ((chosenIntegralResolutionComplex G).d (n + 1) n) :=
  ChainComplex.mk'_d _ _ _ _ n

theorem chosenIntegralResolution_exact (n : ℕ) :
    (chosenIntegralResolutionComplex G).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  apply (rep_shortComplex_exact_iff _).mpr
  intro x hx
  obtain ⟨y, hy⟩ := (rep_shortComplex_exact_iff _).mp
    (chosenIntegralStep_exact ((chosenIntegralResolutionComplex G).d (n + 1) n)) x hx
  let e := chosenIntegralResolutionSuccessorIso (G := G) n
  refine ⟨e.inv.hom y, ?_⟩
  change ((chosenIntegralResolutionComplex G).d (n + 2) (n + 1)).hom (e.inv.hom y) = x
  rw [chosenIntegralResolution_d_succ]
  change (chosenIntegralStep ((chosenIntegralResolutionComplex G).d (n + 1) n)).hom
    (e.hom.hom (e.inv.hom y)) = x
  have he : e.hom.hom (e.inv.hom y) = y := congrArg (fun f => f.hom y) e.inv_hom_id
  rwa [he]

def chosenIntegralResolutionAugmentation :
    chosenIntegralResolutionComplex G ⟶ (ChainComplex.single₀ (Rep ℤ G)).obj (trivialIntegral G) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨integralFreeAugmentation, by
      change chosenIntegralStep (integralFreeAugmentation (G := G)) ≫
        integralFreeAugmentation = 0
      exact chosenIntegralStep_comp _⟩

theorem chosenIntegralResolutionAugmentation_quasiIso :
    QuasiIso (chosenIntegralResolutionAugmentation (G := G)) where
  quasiIsoAt i := by
    cases i with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,
        ShortComplex.quasiIso_iff_of_zeros' _ (by rfl) rfl rfl]
      constructor
      · exact chosenIntegralStep_exact (integralFreeAugmentation (G := G))
      · rw [Rep.epi_iff_surjective]
        change Function.Surjective (integralFreeAugmentation (G := G)).hom
        intro z
        refine ⟨MonoidAlgebra.single 1 z, ?_⟩
        exact (Rep.leftRegularHom_hom_single 1 1 z).trans (by simp)
    | succ n =>
      rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..)]
      exact chosenIntegralResolution_exact n

def chosenIntegralResolution (G : Type) [Group G] : ProjectiveResolution (trivialIntegral G) where
  complex := chosenIntegralResolutionComplex G
  projective := chosenIntegralResolution_projective
  π := chosenIntegralResolutionAugmentation
  quasiIso := chosenIntegralResolutionAugmentation_quasiIso

end PolycyclicRecognition

end

end OAI
