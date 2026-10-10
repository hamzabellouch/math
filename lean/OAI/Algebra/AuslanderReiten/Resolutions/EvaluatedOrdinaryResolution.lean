import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedBaseQuotient
import Mathlib.Algebra.Homology.Single

namespace OAI

noncomputable section
namespace ArExplicit.TwoCone
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (D : Data (R ⊗[k] Rᵐᵒᵖ)) (hf : ∀ n, Module.Finite k (D.term n))
variable (X : FiniteLeftModule k R)

private theorem evaluation_zero {M N : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ)} :
    FiniteLeftModule.evaluationMap X (0 : M.carrier →ₗ[_] N.carrier) = 0 :=
  EnvelopingBimodule.tensorMap_zero X.carrier

theorem evaluatedBaseDifferential_square (n : ℕ) :
    (evaluatedBaseDifferential D hf X n).comp (evaluatedBaseDifferential D hf X (n+1)) = 0 := by
  dsimp only [evaluatedBaseDifferential]
  rw [← FiniteLeftModule.evaluationMap_comp, D.square]
  exact evaluation_zero X

def evaluatedOrdinaryComplex : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (evaluatedRawTerm D hf X)
    (fun n => ModuleCat.ofHom (evaluatedBaseDifferential D hf X n))
    (fun n => ModuleCat.hom_ext (evaluatedBaseDifferential_square D hf X n))

@[simp] theorem evaluatedOrdinaryComplex_d (n : ℕ) :
    (evaluatedOrdinaryComplex D hf X).d (n+1) n =
      ModuleCat.ofHom (evaluatedBaseDifferential D hf X n) := by
  simp only [evaluatedOrdinaryComplex, ChainComplex.of.d]
  apply Category.id_comp

variable (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
variable (hr : ∀ n, Module.Projective Rᵐᵒᵖ
  (EnvelopingBimodule k R (baseCokernelModule D hf n).carrier))

include hex hr in
theorem evaluatedBaseDifferential_ker (n : ℕ) :
    LinearMap.ker (evaluatedBaseDifferential D hf X n) =
      LinearMap.ker (evaluatedBaseQuotient D hf X (n+1)) := by
  rw [evaluatedBaseDifferential_factor D hf hex X n]
  ext z
  change evaluatedBaseInclusion D hf hex X n (evaluatedBaseQuotient D hf X (n+1) z) = 0 ↔ _
  have hi := (evaluatedBaseCover_exact D hf hex hr X n).1
  constructor
  · intro h
    apply hi
    simpa using h
  · intro h
    rw [show evaluatedBaseQuotient D hf X (n+1) z = 0 from h, map_zero]

include hex hr in
theorem evaluatedOrdinaryComplex_exact (n : ℕ) :
    (evaluatedOrdinaryComplex D hf X).ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range ((evaluatedOrdinaryComplex D hf X).d (n+2) (n+1)).hom =
    LinearMap.ker ((evaluatedOrdinaryComplex D hf X).d (n+1) n).hom
  rw [evaluatedOrdinaryComplex_d, evaluatedOrdinaryComplex_d]
  exact (evaluatedBase_range_eq_ker D hf hex hr X (n+1)).trans
    (evaluatedBaseDifferential_ker D hf X hex hr n).symm

theorem evaluatedBaseQuotient_comp_d_zero (n : ℕ) :
    (evaluatedBaseQuotient D hf X n).comp (evaluatedBaseDifferential D hf X n) = 0 := by
  have h : ((LinearMap.range (D.d n)).mkQ).comp (D.d n) = 0 := by
    ext y
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y,rfl⟩
  have he := congrArg (fun f => FiniteLeftModule.evaluationMap X
    (M := termModule D hf (n+1)) (N := baseCokernelModule D hf n) f) h
  erw [FiniteLeftModule.evaluationMap_comp X
    (M := termModule D hf (n+1)) (N := termModule D hf n)
    (P := baseCokernelModule D hf n) (D.d n) (LinearMap.range (D.d n)).mkQ,
    evaluation_zero X (M := termModule D hf (n+1)) (N := baseCokernelModule D hf n)] at he
  exact he

def evaluatedOrdinaryAugmentation : evaluatedOrdinaryComplex D hf X ⟶
    (ChainComplex.single₀ (ModuleCat.{u} R)).obj (X.evaluated (baseCokernelModule D hf 0)).carrier :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom (evaluatedBaseQuotient D hf X 0), by
      rw [evaluatedOrdinaryComplex_d]
      exact ModuleCat.hom_ext (evaluatedBaseQuotient_comp_d_zero D hf X 0)⟩

theorem evaluatedOrdinaryAugmentation_zero : (evaluatedOrdinaryAugmentation D hf X).f 0 =
    ModuleCat.ofHom (evaluatedBaseQuotient D hf X 0) :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

variable (hp : ∀ n, Module.Projective (R ⊗[k] Rᵐᵒᵖ) (D.term n))

def evaluatedOrdinaryResolution :
    ProjectiveResolution (X.evaluated (baseCokernelModule D hf 0)).carrier where
  complex := evaluatedOrdinaryComplex D hf X
  projective n := by
    let := hp n
    let := FiniteLeftModule.evaluated_projective X (M := termModule D hf n)
    change CategoryTheory.Projective (evaluatedRawTerm D hf X n)
    infer_instance
  π := evaluatedOrdinaryAugmentation D hf X
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · constructor
        · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
          change LinearMap.range ((evaluatedOrdinaryComplex D hf X).d 1 0).hom =
            LinearMap.ker ((evaluatedOrdinaryAugmentation D hf X).f 0).hom
          rw [evaluatedOrdinaryComplex_d, evaluatedOrdinaryAugmentation_zero]
          exact evaluatedBase_range_eq_ker D hf hex hr X 0
        · rw [ModuleCat.epi_iff_surjective]
          exact (evaluatedBaseCover_exact D hf hex hr X 0).2.1
      · exact (evaluatedOrdinaryComplex D hf X).shape _ _ (by simp)
      · rfl
      · rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact evaluatedOrdinaryComplex_exact D hf X hex hr n
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

end ArExplicit.TwoCone

end

end OAI
