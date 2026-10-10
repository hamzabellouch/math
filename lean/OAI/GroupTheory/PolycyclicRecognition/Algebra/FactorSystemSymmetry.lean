import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorExtensionMap
import OAI.GroupTheory.PolycyclicRecognition.Algebra.EquivariantCentralizerSplitting
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorExtensionConjugation

namespace OAI

/-! # Symmetries preserve the canonical projected section -/

noncomputable section
namespace PolycyclicRecognition
variable {K Q : Type*} [Group K] [Group Q]

theorem factorSystem_centralizing_section_fixed
    (R : NonabelianFactorSystem K Q) (q₀ : Q) (hq₀ : ∀ q, Commute q₀ q)
    (hLang : Function.Bijective (fun x : K => x⁻¹ * R.action q₀ x))
    (T : K →* K) (hact : ∀ q x, T (R.action q x) = R.action q (T x))
    (hfactor : ∀ q r, T (R.factor q r) = R.factor q r) (q : Q) :
    let E := FactorExtension.groupExtension R
    let t : FactorExtension R := ⟨1, q₀⟩
    let heq : extensionLangMap E t = fun x : K => x⁻¹ * R.action q₀ x := by
      funext x
      change x⁻¹ * E.conjAct t x = x⁻¹ * R.action q₀ x
      rw [FactorExtension.conjugation_section]
    let s := centralizerSplitting E t hq₀ (heq.symm ▸ hLang)
    T (s q).left = (s q).left := by
  dsimp only
  let E := FactorExtension.groupExtension R
  let t : FactorExtension R := ⟨1, q₀⟩
  have heq : extensionLangMap E t = fun x : K => x⁻¹ * R.action q₀ x := by
    funext x
    change x⁻¹ * E.conjAct t x = x⁻¹ * R.action q₀ x
    rw [FactorExtension.conjugation_section]
  let f := FactorExtension.map R R T hact hfactor
  have hft : f t = t := by
    apply FactorExtension.ext
    · exact T.map_one
    · rfl
  have hh := centralizerSplitting_fixed E t hq₀ (heq.symm ▸ hLang) f hft
    (fun _ => rfl) q
  exact congrArg FactorExtension.left hh

end PolycyclicRecognition

end

end OAI
