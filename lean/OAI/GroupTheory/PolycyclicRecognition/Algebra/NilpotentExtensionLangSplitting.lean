import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentExtensionLattice
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorExtensionConjugation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralizerExtensionSplitting
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentLangMap

namespace OAI

/-! # A genuine nonsplit-kernel extension becomes split after completion

The sufficient hypothesis is the invertibility of A - 1 for one quotient
lift. It is checked on the actual linear action, not assumed as a splitting.
-/

noncomputable section
namespace PolycyclicRecognition.NilpotentLatticeCoordinates
open scoped IsMulCommutative Manifold ContDiff
variable {N G Q : Type} [Group N] [Group G] [Group Q]
  (C : NilpotentLatticeCoordinates N) (S : GroupExtension N G Q)
  (σ : S.Section) (hσ : σ 1 = 1)

/-- The completed extension splits if one lift has no fixed infinitesimal
vector in the nilpotent kernel. -/
def completedExtensionSplitting [IsMulCommutative Q] (q : Q)
    (hA : Function.Bijective
      (fun x : C.carrier => C.automorphismLinear (S.conjAct (σ q)) x - x)) :
    (FactorExtension.groupExtension (C.extensionFactorSystem S σ hσ)).Splitting := by
  let T := C.extensionFactorSystem S σ hσ
  let E := FactorExtension.groupExtension T
  let t : FactorExtension T := ⟨1, q⟩
  apply centralizerSplitting E t (fun r => Commute.all _ _)
  have h := polynomial_lang_bijective (C.automorphismLieEquiv (S.conjAct (σ q))) hA
  have heq : extensionLangMap E t =
      (fun x : C.carrier => x⁻¹ * C.automorphismLieEquiv (S.conjAct (σ q)) x) := by
    funext x
    change x⁻¹ * E.conjAct t x = _
    rw [FactorExtension.conjugation_section]
    rw [C.automorphismLieEquiv_apply]
    rfl
  rwa [heq]

/-- Every action obtained from a splitting of this completed extension is
smooth on its nilpotent kernel. -/
theorem completedExtensionSplitting_action_smooth
    (s : (FactorExtension.groupExtension (C.extensionFactorSystem S σ hσ)).Splitting)
    (q : Q) :
    ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, C.carrier)) ∞ (s.conjAct q) := by
  change ContMDiff _ _ _ ((FactorExtension.groupExtension _).conjAct (s q))
  rw [FactorExtension.conjugation_eq]
  have hi : ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, C.carrier)) ∞
      (MulAut.conj (s q).left) := (contMDiff_conjugation (s q).left).of_le (by simp)
  exact hi.comp (C.extensionFactorSystem_smooth S σ hσ _)

end PolycyclicRecognition.NilpotentLatticeCoordinates

end

end OAI
