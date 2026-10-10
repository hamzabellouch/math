import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedCubicCover
import OAI.Algebra.AuslanderReiten.Resolutions.ResolutionCokernel

namespace OAI

noncomputable section
namespace ArExplicit.TwoCone
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (D : Data (R ⊗[k] Rᵐᵒᵖ)) (hf : ∀ n, Module.Finite k (D.term n))
variable (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
variable (hr : ∀ n, Module.Projective Rᵐᵒᵖ
  (EnvelopingBimodule k R (baseCokernelModule D hf n).carrier))
variable (X : FiniteLeftModule k R)

abbrev evaluatedRawTerm (n : ℕ) := (X.evaluated (termModule D hf n)).carrier

def evaluatedBaseDifferential (n : ℕ) :
    evaluatedRawTerm D hf X (n+1) →ₗ[R] evaluatedRawTerm D hf X n :=
  FiniteLeftModule.evaluationMap X (D.d n)

def evaluatedBaseQuotient (n : ℕ) : evaluatedRawTerm D hf X n →ₗ[R]
    (X.evaluated (baseCokernelModule D hf n)).carrier :=
  FiniteLeftModule.evaluationMap X (LinearMap.range (D.d n)).mkQ

def evaluatedBaseInclusion (n : ℕ) :
    (X.evaluated (baseCokernelModule D hf (n+1))).carrier →ₗ[R] evaluatedRawTerm D hf X n :=
  FiniteLeftModule.evaluationMap X (baseStepInclusion D hex n)

theorem baseDifferential_factor (n : ℕ) :
    (baseStepInclusion D hex n).comp (LinearMap.range (D.d (n+1))).mkQ = D.d n := by
  ext z
  exact baseStepInclusion_mk D hex n z

theorem evaluatedBaseDifferential_factor (n : ℕ) :
    evaluatedBaseDifferential D hf X n =
      (evaluatedBaseInclusion D hf hex X n).comp (evaluatedBaseQuotient D hf X (n+1)) := by
  dsimp only [evaluatedBaseDifferential, evaluatedBaseInclusion, evaluatedBaseQuotient]
  rw [← FiniteLeftModule.evaluationMap_comp, baseDifferential_factor D hex n]

include hr in

theorem evaluatedBaseCover_exact (n : ℕ) :
    Function.Injective (evaluatedBaseInclusion D hf hex X n) ∧
    Function.Surjective (evaluatedBaseQuotient D hf X n) ∧
    Function.Exact (evaluatedBaseInclusion D hf hex X n) (evaluatedBaseQuotient D hf X n) := by
  let := hr n
  have h := FiniteLeftModule.evaluation_shortExact X
    (M := baseCokernelModule D hf (n+1)) (N := termModule D hf n)
    (P := baseCokernelModule D hf n)
    (baseStepInclusion D hex n) (LinearMap.range (D.d n)).mkQ
    (baseStepInclusion_injective D hex n) (Submodule.mkQ_surjective _) (baseStep_exact D hex n)
  exact h

include hex hr in

theorem evaluatedBase_range_eq_ker (n : ℕ) :
    LinearMap.range (evaluatedBaseDifferential D hf X n) =
      LinearMap.ker (evaluatedBaseQuotient D hf X n) := by
  have he := (evaluatedBaseCover_exact D hf hex hr X n).2.2
  have hs := (evaluatedBaseCover_exact D hf hex hr X (n+1)).2.1
  rw [evaluatedBaseDifferential_factor D hf hex X n]
  ext z
  constructor
  · rintro ⟨w,rfl⟩
    exact (he _).2 ⟨evaluatedBaseQuotient D hf X (n+1) w,rfl⟩
  · intro hz
    obtain ⟨w,hw⟩ := (he z).1 hz
    obtain ⟨v,rfl⟩ := hs w
    exact ⟨v,hw⟩

def evaluatedBaseCokernelEquiv (n : ℕ) :
    (evaluatedRawTerm D hf X n ⧸ LinearMap.range (evaluatedBaseDifferential D hf X n)) ≃ₗ[R]
      (X.evaluated (baseCokernelModule D hf n)).carrier :=
  (Submodule.quotEquivOfEq _ _ (evaluatedBase_range_eq_ker D hf hex hr X n)).trans
    ((evaluatedBaseQuotient D hf X n).quotKerEquivOfSurjective
      (evaluatedBaseCover_exact D hf hex hr X n).2.1)

@[simp] theorem evaluatedBaseCokernelEquiv_mk (n : ℕ) (z : evaluatedRawTerm D hf X n) :
    evaluatedBaseCokernelEquiv D hf hex hr X n (Submodule.Quotient.mk z) =
      evaluatedBaseQuotient D hf X n z := rfl

end ArExplicit.TwoCone

end

end OAI
