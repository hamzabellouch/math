import OAI.NumberTheory.Ostmann.Characters.QuartetBadCoordinates

namespace OAI

/-! # All free/held orientations in the local quartet value -/

namespace Ostmann

open scoped ComplexConjugate

noncomputable def orientedPairBase {p : ℕ} (g : ZMod p → ℂ) (friendly : Bool) : ZMod p → ℂ :=
  if friendly then g else fun x => conj (g (-x))

noncomputable def quartetLeftParameter {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ) (XL XR P : (ZMod p)ˣ)
    (friendly : Bool) (m₁ m₂ : (ZMod p)ˣ) : (ZMod p)ˣ :=
  if friendly then quartetLeftHeld D Q XL * m₂ ^ 2
  else quartetLeftBadHeld D Q XL XR P * m₁ ^ 2

noncomputable def quartetRightParameter {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ) (XL XR P : (ZMod p)ˣ)
    (friendly : Bool) (m₃ m₄ : (ZMod p)ˣ) : (ZMod p)ˣ :=
  if friendly then quartetRightHeld D Q XR * m₄ ^ 2
  else quartetRightBadHeld D Q XL XR P * m₃ ^ 2

/-- Both choices on the left use the same child difference and exactly the
friendly/bad parameter table of the Fourier calculation. -/
theorem quartet_left_oriented_value {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (V XL XR m₁ m₂ m₃ m₄ : (ZMod p)ˣ) (friendly : Bool) :
    fieldBottomPairValue g (rationalTreeArgument Q.sL (Q.u * Q.CL) D V XL (m₁ * m₂))
      (((Q.s₁ / Q.s₂) * ((XL * Q.C₂ * m₂) / (V * Q.C₁ * m₁)) : (ZMod p)ˣ) : ZMod p) =
    fieldBottomPairValue (orientedPairBase g friendly)
      (rationalTreeArgument Q.sL (Q.u * Q.CL) D V XL (m₁ * m₂))
      (quartetLeftRatio friendly
        (quartetLeftParameter D Q XL XR ((m₁ * m₂) * (m₃ * m₄)) friendly m₁ m₂)
        (rationalTreeArgument Q.sL (Q.u * Q.CL) D V XL (m₁ * m₂))
        (rationalTreeArgument Q.sR (Q.u * Q.CR) D V XR (m₃ * m₄))) := by
  cases friendly
  · simp only [orientedPairBase, quartetLeftParameter, quartetLeftRatio, Bool.false_eq_true, ite_false]
    rw [← fieldBottomPairValue_reflect_reverse g]
    congr 1
    rw [← Units.val_inv_eq_inv_val, ← Units.val_div_eq_div_val]
    exact congrArg (fun x : (ZMod p)ˣ => (x : ZMod p))
      (rationalQuartet_left_bad_ratio D Q V XL XR m₁ m₂ m₃ m₄)
  · simp only [orientedPairBase, quartetLeftParameter, quartetLeftRatio, ite_true]
    have h := pair_ratio_friendly D Q.sL Q.s₁ Q.s₂ Q.C₁ Q.C₂ V XL m₁ m₂
    rw [Q.left_product] at h
    congr 1
    rw [← Units.val_mul]
    exact congrArg (fun x : (ZMod p)ˣ => (x : ZMod p)) h

theorem quartet_right_oriented_value {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (V XL XR m₁ m₂ m₃ m₄ : (ZMod p)ˣ) (friendly : Bool) :
    fieldBottomPairValue g (rationalTreeArgument Q.sR (Q.u * Q.CR) D V XR (m₃ * m₄))
      (((Q.s₃ / Q.s₄) * ((XR * Q.C₄ * m₄) / (V * Q.C₃ * m₃)) : (ZMod p)ˣ) : ZMod p) =
    fieldBottomPairValue (orientedPairBase g friendly)
      (rationalTreeArgument Q.sR (Q.u * Q.CR) D V XR (m₃ * m₄))
      (quartetRightRatio friendly
        (quartetRightParameter D Q XL XR ((m₁ * m₂) * (m₃ * m₄)) friendly m₃ m₄)
        (rationalTreeArgument Q.sL (Q.u * Q.CL) D V XL (m₁ * m₂))
        (rationalTreeArgument Q.sR (Q.u * Q.CR) D V XR (m₃ * m₄))) := by
  cases friendly
  · simp only [orientedPairBase, quartetRightParameter, quartetRightRatio, Bool.false_eq_true, ite_false]
    rw [← fieldBottomPairValue_reflect_reverse g]
    congr 1
    rw [← Units.val_inv_eq_inv_val, ← Units.val_div_eq_div_val]
    exact congrArg (fun x : (ZMod p)ˣ => (x : ZMod p))
      (rationalQuartet_right_bad_ratio D Q V XL XR m₁ m₂ m₃ m₄)
  · simp only [orientedPairBase, quartetRightParameter, quartetRightRatio, ite_true]
    have h := pair_ratio_friendly D Q.sR Q.s₃ Q.s₄ Q.C₃ Q.C₄ V XR m₃ m₄
    rw [Q.right_product] at h
    congr 1
    rw [← Units.val_mul]
    exact congrArg (fun x : (ZMod p)ˣ => (x : ZMod p)) h

/-- All four orientation rows identify the actual local diagram, including
its zero at an invalid reconstruction, with the same ratio function whose
coefficient bounds were proved above. -/
theorem rationalQuartetValue_oriented {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR m₁ m₂ m₃ m₄ : (ZMod p)ˣ) (left right : Bool) :
    rationalQuartetValue g D Q XL XR m₁ m₂ m₃ m₄ =
      quartetRatioValue (orientedPairBase g left) (orientedPairBase g right) left right
        (rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR ((m₁ * m₂) * (m₃ * m₄)))
        (quartetLeftParameter D Q XL XR ((m₁ * m₂) * (m₃ * m₄)) left m₁ m₂)
        (quartetRightParameter D Q XL XR ((m₁ * m₂) * (m₃ * m₄)) right m₃ m₄)
        ((Q.sL / Q.sR) * ((XR * Q.CR * (m₃ * m₄)) / (XL * Q.CL * (m₁ * m₂)))) := by
  let HL := XL * Q.CL * (m₁ * m₂)
  let HR := XR * Q.CR * (m₃ * m₄)
  let v := reconstructedEntry (Q.s : ZMod p) Q.sL Q.sR Q.u HL HR
  let y := rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR ((m₁ * m₂) * (m₃ * m₄))
  let t := (Q.sL / Q.sR) * (HR / HL)
  have ht : ((Q.sL : ZMod p) / Q.sR) * ((HR : ZMod p) / HL) = (t : ZMod p) := by
    simp only [t, Units.val_mul, Units.val_div_eq_div_val]
  have hparent : parentArgument (Q.s : ZMod p) D HL HR = (y : ZMod p) := by
    simp only [parentArgument, y, rationalTreeArgument, HL, HR,
      Units.val_div_eq_div_val, Units.val_mul]
    congr 1
    ring
  have hzero : v = 0 ↔ t = 1 := by
    have hz := reconstructedEntry_zero_iff_ratio_one (Q.s : ZMod p) Q.sL Q.sR Q.u HL HR
      (Units.ne_zero Q.s) (Units.ne_zero Q.sR) (Units.ne_zero Q.u) (Units.ne_zero HL)
    rw [ht] at hz
    exact ⟨fun h => Units.ext (hz.mp h),
      fun h => hz.mpr (congrArg (fun x : (ZMod p)ˣ => (x : ZMod p)) h)⟩
  change (if hv : v = 0 then 0 else _) =
    quartetRatioValue (orientedPairBase g left) (orientedPairBase g right) left right y _ _ t
  by_cases hv : v = 0
  · simp [hv, quartetRatioValue, ratioTest, hzero.mp hv]
  · simp only [hv, dite_false]
    let V : (ZMod p)ˣ := Units.mk0 v hv
    let d := rationalTreeArgument Q.sL (Q.u * Q.CL) D V XL (m₁ * m₂)
    let e := rationalTreeArgument Q.sR (Q.u * Q.CR) D V XR (m₃ * m₄)
    have hdiff : (d : ZMod p) - e = y := by
      dsimp [d, e]
      rw [rationalTreeArgument_child, rationalTreeArgument_child]
      rw [tree_child_difference (Q.s : ZMod p) Q.sL Q.sR D Q.u HL HR V
        (Units.ne_zero D) (Units.ne_zero Q.u) (Units.ne_zero HL) (Units.ne_zero HR)
        (Units.ne_zero V) (reconstructedEntry_relation (Q.s : ZMod p) Q.sL Q.sR Q.u HL HR
          (Units.ne_zero Q.s) (Units.ne_zero Q.u))]
      exact hparent
    have hde : d / e = t := by
      apply Units.ext
      rw [Units.val_div_eq_div_val]
      dsimp [d, e]
      rw [rationalTreeArgument_child, rationalTreeArgument_child]
      exact (tree_child_ratio (Q.sL : ZMod p) Q.sR D Q.u HL HR V
        (Units.ne_zero Q.sR) (Units.ne_zero D) (Units.ne_zero Q.u) (Units.ne_zero HL)
        (Units.ne_zero HR) (Units.ne_zero V)).trans ht
    change fieldBottomPairValue g d _ * fieldBottomPairValue g e _ = _
    rw [quartet_left_oriented_value g D Q V XL XR m₁ m₂ m₃ m₄ left,
      quartet_right_oriented_value g D Q V XL XR m₁ m₂ m₃ m₄ right]
    have h := quartetRatioValue_at_difference (orientedPairBase g left) (orientedPairBase g right)
      left right y d e
      (quartetLeftParameter D Q XL XR ((m₁ * m₂) * (m₃ * m₄)) left m₁ m₂)
      (quartetRightParameter D Q XL XR ((m₁ * m₂) * (m₃ * m₄)) right m₃ m₄) hdiff
    rw [hde] at h
    exact h.symm

end Ostmann

end OAI
