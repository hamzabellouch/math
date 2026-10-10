import OAI.GroupTheory.PolycyclicRecognition.Analysis.CofiberChainConnecting

namespace OAI

/-! # Top homology of a chain mapping cone -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {P Q : ChainComplex (ModuleCat ℤ) ℕ} (φ : P ⟶ Q)

def cofiberChainHomologyKernelIso (i : ℕ) (hQ : IsZero (Q.homology (i + 1))) :
    (homotopyCofiber φ).homology (i + 1) ≅
      kernel (HomologicalComplex.homologyMap φ i) := by
  let S := cofiberChainSequence φ
  let hS := cofiberChainSequence_shortExact φ
  have hm : Mono (HomologicalComplex.homologyMap S.g (i + 1)) :=
    (hS.homology_exact₂ (i + 1)).mono_g (hQ.eq_of_src _ _)
  let := hm
  let e := kernel.mapIso (hS.δ (i + 1) i rfl)
    (HomologicalComplex.homologyMap φ i) (chainSuccessorHomologyIso P i) (Iso.refl _)
    (by
      rw [← cofiberChain_connecting φ i]
      simp only [Iso.refl_hom, Iso.hom_inv_id_assoc, Category.comp_id])
  exact (hS.homology_exact₃ (i + 1) i rfl).fIsKernel.conePointUniqueUpToIso
    (kernelIsKernel _) ≪≫ e

end PolycyclicRecognition

end

end OAI
