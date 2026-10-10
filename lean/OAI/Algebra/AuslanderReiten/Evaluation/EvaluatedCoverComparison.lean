import OAI.Algebra.AuslanderReiten.Resolutions.EvaluatedOrdinaryResolution
import OAI.Algebra.AuslanderReiten.Coordinates.FiniteExtSourceCoordinates

namespace OAI

noncomputable section
namespace ArExplicit.TwoCone
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (D : Data (R ⊗[k] Rᵐᵒᵖ)) (hf : ∀ n, Module.Finite k (D.term n))
variable (X : FiniteLeftModule k R)
variable (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
variable (hr : ∀ n, Module.Projective Rᵐᵒᵖ
  (EnvelopingBimodule k R (baseCokernelModule D hf n).carrier))
variable (hp : ∀ n, Module.Projective (R ⊗[k] Rᵐᵒᵖ) (D.term n))
variable (τ : FrobeniusTrace k R)
local notation "M₀" => FiniteLeftModule.evaluated X (baseCokernelModule D hf 0)
variable (S : FiniteLeftModule k R)
variable (e : S.carrier →ₗ[R] (X.evaluated (baseCokernelModule D hf 0)).carrier)
local notation "K" => FiniteLeftModule.completeCochain τ S
local notation "P" => evaluatedOrdinaryResolution D hf X hex hr hp
local notation "Q" => completeExtResolution (TotallyAcyclicCochain.to_chain (FiniteLeftModule.completeCochain_totallyAcyclic τ S))

abbrev EvaluatedCompleteComparison := ProjectiveResolution.Hom Q P
  (ModuleCat.ofHom (e.comp (FiniteLeftModule.fullCokernelEquiv τ S).toLinearMap))

def evaluatedCompleteComparison : EvaluatedCompleteComparison D hf X hex hr hp τ S e where
  hom := ProjectiveResolution.lift
    (ModuleCat.ofHom (e.comp (FiniteLeftModule.fullCokernelEquiv τ S).toLinearMap)) Q P
  hom_f_zero_comp_π_f_zero := by
    erw [ChainComplex.single₀_map_f_zero]
    exact ProjectiveResolution.lift_commutes_zero
      (ModuleCat.ofHom (e.comp (FiniteLeftModule.fullCokernelEquiv τ S).toLinearMap)) Q P

variable (φ : EvaluatedCompleteComparison D hf X hex hr hp τ S e)

def evaluatedComparisonTerm (n : ℕ) : (K).X (-(n : ℤ)) →ₗ[R] evaluatedRawTerm D hf X n :=
  (φ.hom.f n).hom.comp (tailTermIso K n).inv.hom

theorem evaluatedComparisonTerm_comm (n : ℕ) :
    (evaluatedBaseDifferential D hf X n).comp
      (evaluatedComparisonTerm D hf X hex hr hp τ S e φ (n+1)) =
    (evaluatedComparisonTerm D hf X hex hr hp τ S e φ n).comp
      ((K).d (-((n+1 : ℕ) : ℤ)) (-(n : ℤ))).hom := by
  have h := φ.hom.comm (n+1) n
  change φ.hom.f (n+1) ≫ (evaluatedOrdinaryComplex D hf X).d (n+1) n =
    (nonnegativeTail (chainOfCochain K)).d (n+1) n ≫ φ.hom.f n at h
  rw [evaluatedOrdinaryComplex_d, tailTerm_d K (n+1) n rfl] at h
  have hh := congrArg (fun f => (tailTermIso K (n+1)).inv ≫ f) h
  erw [Category.assoc, Iso.inv_hom_id_assoc] at hh
  exact congrArg ModuleCat.Hom.hom hh

theorem evaluatedComparisonTerm_closed (n : ℕ) :
    ((evaluatedBaseQuotient D hf X n).comp (evaluatedComparisonTerm D hf X hex hr hp τ S e φ n)).comp
      ((K).d (-((n : ℤ)+1)) (-(n : ℤ))).hom = 0 := by
  have hc := evaluatedComparisonTerm_comm D hf X hex hr hp τ S e φ n
  change (evaluatedBaseDifferential D hf X n).comp
    (evaluatedComparisonTerm D hf X hex hr hp τ S e φ (n+1)) =
    (evaluatedComparisonTerm D hf X hex hr hp τ S e φ n).comp
      ((K).d (-((n : ℤ)+1)) (-(n : ℤ))).hom at hc
  rw [LinearMap.comp_assoc, ← hc,
    ← LinearMap.comp_assoc, evaluatedBaseQuotient_comp_d_zero, LinearMap.zero_comp]

def evaluatedComparisonCokernel (n : ℕ) : RawCokernelAt K (n : ℤ) →ₗ[R]
    (X.evaluated (baseCokernelModule D hf n)).carrier :=
  (LinearMap.range ((K).d (-((n : ℤ)+1)) (-(n : ℤ))).hom).liftQ
    ((evaluatedBaseQuotient D hf X n).comp (evaluatedComparisonTerm D hf X hex hr hp τ S e φ n))
    (LinearMap.range_le_ker_iff.mpr (evaluatedComparisonTerm_closed D hf X hex hr hp τ S e φ n))

@[simp]
theorem evaluatedComparisonCokernel_mk (n : ℕ) (z : (K).X (-(n : ℤ))) :
    evaluatedComparisonCokernel D hf X hex hr hp τ S e φ n (Submodule.Quotient.mk z) =
      evaluatedBaseQuotient D hf X n (evaluatedComparisonTerm D hf X hex hr hp τ S e φ n z) := rfl

theorem evaluatedComparisonCokernel_inclusion (n : ℕ) :
    (evaluatedBaseInclusion D hf hex X n).comp
      (evaluatedComparisonCokernel D hf X hex hr hp τ S e φ (n+1)) =
    (evaluatedComparisonTerm D hf X hex hr hp τ S e φ n).comp
      (rawCokernelAtInclusion K (n : ℤ)) := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range ((K).d (-(((n+1 : ℕ) : ℤ)+1)) (-((n+1 : ℕ) : ℤ))).hom) z
  change (evaluatedBaseInclusion D hf hex X n)
    (evaluatedBaseQuotient D hf X (n+1) (evaluatedComparisonTerm D hf X hex hr hp τ S e φ (n+1) z)) = _
  rw [← LinearMap.comp_apply, ← evaluatedBaseDifferential_factor D hf hex X n]
  exact LinearMap.congr_fun (evaluatedComparisonTerm_comm D hf X hex hr hp τ S e φ n) z

end ArExplicit.TwoCone

end

end OAI
