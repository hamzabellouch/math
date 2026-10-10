import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteProjectivePresentations
import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
import Mathlib.RingTheory.Noetherian.Basic

namespace OAI

/-! # Integral homology finiteness from FP finiteness

Finite group-ring generators become finite integral generators after tensoring
with a finite integral coefficient module and taking coinvariants. Since the
integers are Noetherian, cycles and homology inherit finite generation.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory
attribute [local instance 2000] Rep.hV2
variable {G : Type} [Group G]

theorem finite_coinvariantsTensor (A B : Rep ℤ G) [Module.Finite ℤ A]
    (hB : IntegralRepresentationFinite G B) :
    Module.Finite ℤ (((Rep.coinvariantsTensor ℤ G).obj A).obj B) := by
  classical
  obtain ⟨ι, hι, f, hf⟩ := finiteIntegralFreeCover_exists B hB
  let := hι
  let := hf
  let F := (Rep.coinvariantsTensor ℤ G).obj A
  let : Module ℤ (ι →₀ A) := Finsupp.module _ _
  have hfree : Module.Finite ℤ (F.obj (Rep.free ℤ G ι)) :=
    Module.Finite.equiv (Rep.coinvariantsTensorFreeLEquiv A ι).symm
  let := hfree
  have ht : Epi (𝟙 A ⊗ₘ f) := by
    apply (Rep.epi_iff_surjective _).mpr
    exact TensorProduct.map_surjective Function.surjective_id
      ((Rep.epi_iff_surjective f).mp hf)
  have hm : Epi (F.map f) := by
    change Epi ((Rep.coinvariantsFunctor ℤ G).map (𝟙 A ⊗ₘ f))
    infer_instance
  exact Module.Finite.of_surjective (F.map f).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

theorem finite_homology_of_finite_term (C : ChainComplex (ModuleCat ℤ) ℕ) (i : ℕ)
    [Module.Finite ℤ (C.X i)] : Module.Finite ℤ (C.homology i) := by
  have hcycles : Module.Finite ℤ (C.cycles i) :=
    Module.Finite.of_injective (C.iCycles i).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  let := hcycles
  exact Module.Finite.of_surjective (C.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

theorem TypeFP.homology_finite {n : ℕ} (hG : TypeFP G n)
    (A : Rep ℤ G) [Module.Finite ℤ A] : Module.Finite ℤ (groupHomology A n) := by
  classical
  obtain ⟨P, hP⟩ := hG
  let C := P.complex.coinvariantsTensorObj A
  have hX : Module.Finite ℤ (C.X n) := finite_coinvariantsTensor A _ (hP n le_rfl)
  let := hX
  have hH : Module.Finite ℤ (C.homology n) := finite_homology_of_finite_term C n
  let := hH
  exact Module.Finite.equiv (groupHomologyIso A n P).symm.toLinearEquiv

end PolycyclicRecognition

end

end OAI
