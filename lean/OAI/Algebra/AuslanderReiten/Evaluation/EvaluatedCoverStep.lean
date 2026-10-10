import OAI.Algebra.AuslanderReiten.Resolutions.CoverStepFullHom
import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedMiddleShift

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R₀" => A k q
local notation "X₀" => A.simpleFiniteModule q
local notation "τ₀" => AFrobeniusTrace k q
local notation "Q₀" => HomotopyCategory.quotient (ModuleCat R₀) (ComplexShape.up ℤ)
local notation "H₀" => fun d => CohomologyClass (A.simpleComplete q) (A.simpleComplete q) d

theorem evaluatedBaseFullHomEquiv_step (n : ℕ) (a : ℤ)
    (v : evaluatedSimpleObject q ⟶ (evaluatedBaseResolution q n)⟦a⟧) :
    evaluatedBaseFullHomEquiv q (n+1) (a+1)
      (ShiftedHom.comp v (evaluatedBaseStepIso q n).hom (add_comm 1 a)) =
    TateKoszul.degreeEquiv (k := k) H₀ (by omega : a-(n:ℤ)=(a+1)-((n+1:ℕ):ℤ))
      (evaluatedBaseFullHomEquiv q n a v) := by
  exact coverStepFullHom k _ _ (n:ℤ) ((n+1:ℕ):ℤ) (by omega)
    (simpleToEvaluatedBaseShiftIso q n) (evaluatedBaseStepIso q n)
    (simpleToEvaluatedBaseShiftIso q (n+1)) (simpleToEvaluatedBaseShiftIso_succ q n) a v

theorem evaluatedSingletonFullHomEquiv_fst (n : ℕ) (a : ℤ)
    (v : evaluatedSimpleObject q ⟶ (evaluatedSingletonResolution q n)⟦a⟧) :
    (evaluatedSingletonFullHomEquiv q n a v).1 =
      evaluatedBaseFullHomEquiv q (n+2) a
        (v ≫ ((Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedSingletonFst q n)))⟦a⟧') := by
  simp only [evaluatedSingletonFullHomEquiv, LinearEquiv.trans_apply,
    LinearEquiv.prodCongr_apply, evaluatedSingletonHomEquiv,
    mappedBiproductHomEquiv_fst, mappedBiproductHomEquiv_snd,
    Linear.homCongr_apply, Iso.refl_inv, Category.id_comp, Functor.mapIso_hom]
  change evaluatedBaseFullHomEquiv q (n+2) a
    ((v ≫ (evaluatedSingletonProductIso q n).hom⟦a⟧') ≫ biprod.fst⟦a⟧') = _
  rw [Category.assoc, ← Functor.map_comp, evaluatedSingletonProductIso_fst]

theorem evaluatedSingletonFullHomEquiv_snd (n : ℕ) (a : ℤ)
    (v : evaluatedSimpleObject q ⟶ (evaluatedSingletonResolution q n)⟦a⟧) :
    (evaluatedSingletonFullHomEquiv q n a v).2 =
      evaluatedBaseFullHomEquiv q (n+2) a
        (v ≫ ((Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedSingletonSnd q n)))⟦a⟧') := by
  simp only [evaluatedSingletonFullHomEquiv, LinearEquiv.trans_apply,
    LinearEquiv.prodCongr_apply, evaluatedSingletonHomEquiv,
    mappedBiproductHomEquiv_fst, mappedBiproductHomEquiv_snd,
    Linear.homCongr_apply, Iso.refl_inv, Category.id_comp, Functor.mapIso_hom]
  change evaluatedBaseFullHomEquiv q (n+2) a
    ((v ≫ (evaluatedSingletonProductIso q n).hom⟦a⟧') ≫ biprod.snd⟦a⟧') = _
  rw [Category.assoc, ← Functor.map_comp, evaluatedSingletonProductIso_snd]

end ArExplicit.T

end

end OAI
