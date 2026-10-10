import OAI.NumberTheory.Ostmann.Characters.QuartetConjugation

namespace OAI

/-! # Quartet ratio coordinates with independent tests in the sibling pairs -/

namespace Ostmann

theorem rationalQuartetPairsValue_oriented {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR m₁ m₂ m₃ m₄ : (ZMod p)ˣ) (left right : Bool) :
    rationalQuartetPairsValue g h D Q XL XR m₁ m₂ m₃ m₄ =
      quartetRatioValue (orientedPairBase g left) (orientedPairBase h right) left right
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
    quartetRatioValue (orientedPairBase g left) (orientedPairBase h right) left right y _ _ t
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
    change fieldBottomPairValue g d _ * fieldBottomPairValue h e _ = _
    rw [quartet_left_oriented_value g D Q V XL XR m₁ m₂ m₃ m₄ left,
      quartet_right_oriented_value h D Q V XL XR m₁ m₂ m₃ m₄ right]
    have h := quartetRatioValue_at_difference (orientedPairBase g left) (orientedPairBase h right)
      left right y d e
      (quartetLeftParameter D Q XL XR ((m₁ * m₂) * (m₃ * m₄)) left m₁ m₂)
      (quartetRightParameter D Q XL XR ((m₁ * m₂) * (m₃ * m₄)) right m₃ m₄) hdiff
    rw [hde] at h
    exact h.symm

end Ostmann

end OAI
