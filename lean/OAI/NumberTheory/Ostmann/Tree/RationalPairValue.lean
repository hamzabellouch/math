import OAI.NumberTheory.Ostmann.Tree.RationalTreeLeaves
import OAI.NumberTheory.Ostmann.Characters.FieldPairMoment

namespace OAI

/-! # Exact bottom-pair identification in a reconstructed rational tree -/

namespace Ostmann

open scoped ComplexConjugate

/-- A bottom node with the usual alternating conjugation is exactly the pair
function used in the Fourier and Mellin estimates, including invalid nodes. -/
theorem rationalTreeAmplitude_pair {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D s sL sR CL CR u XL XR mL mR : (ZMod p)ˣ) :
    rationalTreeAmplitude g D
      (.node s CL CR u (.leaf sL (u * CL)) (.leaf sR (u * CR)))
      XL XR (false, true) (mL, mR) =
      fieldBottomPairValue g
        (rationalTreeArgument s (CL * CR) D XL XR (mL * mR))
        (((sL / sR) * ((XR * CR * mR) / (XL * CL * mL)) : (ZMod p)ˣ) : ZMod p) := by
  let HL := XL * CL * mL
  let HR := XR * CR * mR
  let v := reconstructedEntry (s : ZMod p) sL sR u HL HR
  let d := rationalTreeArgument s (CL * CR) D XL XR (mL * mR)
  let t := (sL / sR) * (HR / HL)
  have hdiff : parentArgument (s : ZMod p) D HL HR = (d : ZMod p) := by
    simp only [parentArgument, d, rationalTreeArgument, HL, HR,
      Units.val_div_eq_div_val, Units.val_mul]
    congr 1
    ring
  have ht : ((sL : ZMod p) / sR) * ((HR : ZMod p) / HL) = (t : ZMod p) := by
    simp only [t, Units.val_mul, Units.val_div_eq_div_val]
  have hzero : v = 0 ↔ t = 1 := by
    have hz := reconstructedEntry_zero_iff_ratio_one (s : ZMod p) sL sR u HL HR
      (Units.ne_zero s) (Units.ne_zero sR) (Units.ne_zero u) (Units.ne_zero HL)
    rw [ht] at hz
    constructor
    · intro h
      exact Units.ext (hz.mp h)
    · intro h
      exact hz.mpr (congrArg (fun a : (ZMod p)ˣ => (a : ZMod p)) h)
  change (if hv : v = 0 then 0 else
    g (rationalTreeArgument sL (u * CL) D (Units.mk0 v hv) XL mL) *
      star (g (rationalTreeArgument sR (u * CR) D (Units.mk0 v hv) XR mR))) =
    fieldBottomPairValue g d t
  rw [fieldBottomPairValue_units]
  by_cases hv : v = 0
  · simp [hv, bottomPairValue, hzero.mp hv]
  · have ht1 : t ≠ 1 := fun h => hv (hzero.mpr h)
    simp only [hv, dite_false, bottomPairValue, ht1, ite_false]
    let V : (ZMod p)ˣ := Units.mk0 v hv
    have hc := tree_children_eq_pair_coordinates (s : ZMod p) sL sR D u HL HR V
      (Units.ne_zero s) (Units.ne_zero sR) (Units.ne_zero D) (Units.ne_zero u)
      (Units.ne_zero HL) (Units.ne_zero HR) (Units.ne_zero V)
      (reconstructedEntry_relation (s : ZMod p) sL sR u HL HR
        (Units.ne_zero s) (Units.ne_zero u))
    rw [hdiff, ht] at hc
    have hL : (rationalTreeArgument sL (u * CL) D V XL mL : ZMod p) =
        (d : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1) := by
      rw [rationalTreeArgument_child]
      exact congrArg Prod.fst hc
    have hR : (rationalTreeArgument sR (u * CR) D V XR mR : ZMod p) =
        (d : ZMod p) / ((t : ZMod p) - 1) := by
      rw [rationalTreeArgument_child]
      exact congrArg Prod.snd hc
    change g (rationalTreeArgument sL (u * CL) D V XL mL) *
      star (g (rationalTreeArgument sR (u * CR) D V XR mR)) = _
    rw [hL, hR]
    rfl

end Ostmann

end OAI
