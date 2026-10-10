import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorSystemGauge
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorExtensionMap
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralizerExtensionSplitting
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorExtensionConjugation

namespace OAI

/-! # Removing the split part of a kernel cocycle

A splitting after projection of the kernel gives explicit corrections of the
original quotient section. The corrected cocycle lies in the kernel of that
projection. This retains the original extension through its gauge isomorphism.
-/

noncomputable section
namespace PolycyclicRecognition
variable {N K Q : Type*} [Group N] [Group K] [Group Q]

theorem factorSystem_cocycle_reduction
    (S : NonabelianFactorSystem N Q) (R : NonabelianFactorSystem K Q)
    (p : N →* K) (j : K →* N) (hpj : ∀ x, p (j x) = x)
    (hact : ∀ q x, p (S.action q x) = R.action q (p x))
    (hfactor : ∀ q r, p (S.factor q r) = R.factor q r)
    (s : (FactorExtension.groupExtension R).Splitting) :
    ∃ b : Q → N, ∃ hb : b 1 = 1, ∀ q r, p ((S.gauge b hb).factor q r) = 1 := by
  let b : Q → N := fun q => j (s q).left
  have hb : b 1 = 1 := by
    change j (s 1).left = 1
    rw [map_one]
    exact j.map_one
  refine ⟨b, hb, ?_⟩
  intro q r
  have hq : (s q).right = q := s.rightInverse_rightHom q
  have hr : (s r).right = r := s.rightInverse_rightHom r
  have hm := congrArg FactorExtension.left (s.map_mul q r)
  change (s (q * r)).left =
    (s q).left * R.action (s q).right (s r).left * R.factor (s q).right (s r).right at hm
  rw [hq, hr] at hm
  change p (b q * S.action q (b r) * S.factor q r * (b (q * r))⁻¹) = 1
  simp only [map_mul, map_inv, hact, hfactor, b, hpj]
  have hs : (s (q * r)).left = (s q * s r).left :=
    congrArg FactorExtension.left (s.map_mul q r)
  rw [← hm, hs, mul_inv_cancel]

theorem factorSystem_cocycle_reduction_of_bijective_lang
    (S : NonabelianFactorSystem N Q) (R : NonabelianFactorSystem K Q)
    (p : N →* K) (j : K →* N) (hpj : ∀ x, p (j x) = x)
    (hact : ∀ q x, p (S.action q x) = R.action q (p x))
    (hfactor : ∀ q r, p (S.factor q r) = R.factor q r)
    (q₀ : Q) (hq₀ : ∀ q, Commute q₀ q)
    (hLang : Function.Bijective (fun x : K => x⁻¹ * R.action q₀ x)) :
    ∃ b : Q → N, ∃ hb : b 1 = 1, ∀ q r, p ((S.gauge b hb).factor q r) = 1 := by
  let E := FactorExtension.groupExtension R
  let t : FactorExtension R := ⟨1, q₀⟩
  have heq : extensionLangMap E t = fun x : K => x⁻¹ * R.action q₀ x := by
    funext x
    change x⁻¹ * E.conjAct t x = x⁻¹ * R.action q₀ x
    rw [FactorExtension.conjugation_section]
  have hb : Function.Bijective (extensionLangMap E t) := by rwa [heq]
  exact factorSystem_cocycle_reduction S R p j hpj hact hfactor
    (centralizerSplitting E t hq₀ hb)

end PolycyclicRecognition

end

end OAI
