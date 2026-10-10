import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalModuleFunctor
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteIntegralHomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NoetherianResolutionHomology
import Mathlib.LinearAlgebra.TensorProduct.Pi

namespace OAI

/-! # FP finiteness with rationally finite coefficient modules

The integral coefficient module need not be finitely generated. Finiteness of
its rationalization suffices: finite free covers give finite rational chain
terms, and exact rationalization computes their rational homology.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory MonoidalCategory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2200] TensorProduct.instModule
attribute [local instance 2300] Representation.Coinvariants.instModule Finsupp.module Pi.module
variable {G : Type} [Group G]

theorem rational_coinvariantsTensor_finite (A B : Rep ℤ G)
    [Module.Finite ℚ (ℚ ⊗[ℤ] A)] (hB : IntegralRepresentationFinite G B) :
    Module.Finite ℚ (ℚ ⊗[ℤ] (((Rep.coinvariantsTensor ℤ G).obj A).obj B)) := by
  classical
  obtain ⟨ι, hι, f, hf⟩ := finiteIntegralFreeCover_exists B hB
  let := hι
  let := hf
  let : Fintype ι := Fintype.ofFinite ι
  let F := (Rep.coinvariantsTensor ℤ G).obj A
  let e := (Rep.coinvariantsTensorFreeLEquiv A ι).baseChange ℤ ℚ _ _ ≪≫ₗ
    (Finsupp.linearEquivFunOnFinite ℤ A ι).baseChange ℤ ℚ _ _ ≪≫ₗ
    TensorProduct.piRight ℤ ℚ ℚ (fun _ : ι => A)
  let : Module.Finite ℚ (ℚ ⊗[ℤ] F.obj (Rep.free ℤ G ι)) :=
    Module.Finite.equiv e.symm
  have ht : Epi (𝟙 A ⊗ₘ f) := by
    apply (Rep.epi_iff_surjective _).mpr
    exact TensorProduct.map_surjective Function.surjective_id
      ((Rep.epi_iff_surjective f).mp hf)
  have hm : Epi (F.map f) := by
    change Epi ((Rep.coinvariantsFunctor ℤ G).map (𝟙 A ⊗ₘ f))
    infer_instance
  exact Module.Finite.of_surjective ((F.map f).hom.baseChange ℚ)
    ((F.map f).hom.baseChange_surjective ℚ
      ((ModuleCat.epi_iff_surjective _).mp hm))

theorem rational_homology_finite_of_term (C : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i : ℕ)
    [h : Module.Finite ℚ (ℚ ⊗[ℤ] C.X i)] :
    Module.Finite ℚ (ℚ ⊗[ℤ] C.homology i) := by
  let D := (rationalModuleFunctor.mapHomologicalComplex (ComplexShape.down ℕ)).obj C
  let : Module.Finite ℚ (D.sc i).X₂ := by exact h
  let : Module.Finite ℚ (D.homology i) := module_finite_shortComplex_homology (D.sc i)
  exact Module.Finite.equiv (rationalModuleHomologyIso C i).toLinearEquiv

theorem TypeFP.rational_homology_finite {n : ℕ} (hG : TypeFP G n)
    (A : Rep ℤ G) [Module.Finite ℚ (ℚ ⊗[ℤ] A)] :
    Module.Finite ℚ (ℚ ⊗[ℤ] groupHomology A n) := by
  classical
  obtain ⟨P, hP⟩ := hG
  let C := P.complex.coinvariantsTensorObj A
  let : Module.Finite ℚ (ℚ ⊗[ℤ] C.X n) :=
    rational_coinvariantsTensor_finite A _ (hP n le_rfl)
  let e := rationalModuleFunctor.mapIso (groupHomologyIso A n P).symm
  let : Module.Finite ℚ (rationalModuleFunctor.obj (C.homology n)) := by
    exact rational_homology_finite_of_term C n
  exact Module.Finite.equiv e.toLinearEquiv

end PolycyclicRecognition

end

end OAI
