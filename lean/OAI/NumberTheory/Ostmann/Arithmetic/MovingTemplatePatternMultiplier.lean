import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternTemplateEnumeration
import OAI.NumberTheory.Ostmann.Arithmetic.MovingMaskedMultiplierReindex

namespace OAI

/-! # The exact masked multiplier in the finite arithmetic pattern -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingTemplate_pattern_multiplier {C : Type*} {N : ℕ} (n r m : ℕ)
    (e : Fin (N + 1) ≃ MovingRegularSlot n r m ⊕ C)
    (value : Fin (N + 1) → ℕ) (hprime : ∀ i, (value i).Prime)
    (active : MovingRegularSlot n r m → Bool) (outside : List ℕ)
    (g : ∀ q : ℕ, ZMod q → ℂ) (XL XR : ℕ) (s : ℤ) :
    let L := movingPatternRegularSlots e n m (movingTemplateSmall n r m) (movingTemplateBulk n r m)
    let p := fun i : Fin L.length => value (L.get i)
    let q := fun i => value (e.symm (.inl i))
    let _ : ∀ i, Fact (p i).Prime := fun _ => ⟨hprime _⟩
    let _ : ∀ i, Fact (q i).Prime := fun _ => ⟨hprime _⟩
    naturalRegularMultiplier p (fun i => active (movingPatternTemplateEquiv n r m e i)) s
      (fun i => (movingRegularOther value outside L i : ZMod (p i)))
      (fun i => g (p i)) XL XR =
    naturalRegularMultiplier q active s
      (fun i => ((outside.prod * tupleCofactor q i : ℕ) : ZMod (q i)))
      (fun i => g (q i)) XL XR := by
  intro L p q ip iq
  simp only [movingRegularOther_eq_cofactor, Int.cast_natCast]
  let E := movingPatternTemplateEquiv n r m e
  have hp : p = fun i => q (E i) := by
    funext i
    exact congrArg value (movingPatternTemplateEquiv_label n r m e i)
  let M (v : Fin L.length → ℕ) : ℝ :=
    ∏ i, if active (E i) then
      ‖g (v i) ((s : ZMod (v i)) *
        (((outside.prod * tupleCofactor v i : ℕ) : ZMod (v i)) *
          (XL : ZMod (v i)) * (XR : ZMod (v i)))⁻¹)‖ ^ 2 else 1
  simp only [naturalRegularMultiplier, div_eq_mul_inv]
  change M p = _
  rw [hp]
  have h := naturalRegularMultiplier_equiv E q (fun i => hprime _) active g outside.prod XL XR s
  simpa only [naturalRegularMultiplier, div_eq_mul_inv, M] using h

end Ostmann

end OAI
