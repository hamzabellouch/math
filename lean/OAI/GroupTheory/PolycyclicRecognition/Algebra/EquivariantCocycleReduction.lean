import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorSystemCocycleReduction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorSystemSymmetry

namespace OAI

/-! # A single canonical cocycle correction preserves all compatible symmetries -/

noncomputable section
namespace PolycyclicRecognition
variable {N K Q : Type*} [Group N] [Group K] [Group Q]

theorem factorSystem_cocycle_reduction_equivariant
    (S : NonabelianFactorSystem N Q) (R : NonabelianFactorSystem K Q)
    (p : N →* K) (j : K →* N) (hpj : ∀ x, p (j x) = x)
    (hact : ∀ q x, p (S.action q x) = R.action q (p x))
    (hfactor : ∀ q r, p (S.factor q r) = R.factor q r)
    (q₀ : Q) (hq₀ : ∀ q, Commute q₀ q)
    (hLang : Function.Bijective (fun x : K => x⁻¹ * R.action q₀ x)) :
    ∃ b : Q → N, ∃ hb : b 1 = 1,
      (∀ q r, p ((S.gauge b hb).factor q r) = 1) ∧
      (∀ q, ∃ x, b q = j x) ∧
      ∀ (T : N →* N) (U : K →* K), (∀ x, T (j x) = j (U x)) →
        (∀ q x, U (R.action q x) = R.action q (U x)) →
        (∀ q r, U (R.factor q r) = R.factor q r) → ∀ q, T (b q) = b q := by
  let E := FactorExtension.groupExtension R
  let t : FactorExtension R := ⟨1, q₀⟩
  have heq : extensionLangMap E t = fun x : K => x⁻¹ * R.action q₀ x := by
    funext x
    change x⁻¹ * E.conjAct t x = x⁻¹ * R.action q₀ x
    rw [FactorExtension.conjugation_section]
  let s := centralizerSplitting E t hq₀ (heq.symm ▸ hLang)
  let b : Q → N := fun q => j (s q).left
  have hb : b 1 = 1 := by
    change j (s 1).left = 1
    rw [map_one]
    exact j.map_one
  refine ⟨b, hb, ?_, fun q => ⟨(s q).left, rfl⟩, ?_⟩
  · intro q r
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
  · intro T U hTU hUa hUf q
    change T (j (s q).left) = j (s q).left
    rw [hTU]
    exact congrArg j (factorSystem_centralizing_section_fixed R q₀ hq₀ hLang U hUa hUf q)

end PolycyclicRecognition

end

end OAI
