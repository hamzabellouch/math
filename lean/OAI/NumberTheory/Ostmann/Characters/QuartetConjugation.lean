import OAI.NumberTheory.Ostmann.Characters.QuartetOrientedValue

namespace OAI

/-! # Independent opposite conjugations on the two bottom sibling pairs -/

namespace Ostmann

open scoped ComplexConjugate

noncomputable def pairConjugate {p : ℕ} (g : ZMod p → ℂ) (c : Bool) : ZMod p → ℂ :=
  if c then fun x => conj (g x) else g

theorem rationalTreeAmplitude_pair_conjugation {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D s sL sR CL CR u XL XR mL mR : (ZMod p)ˣ) (c : Bool) :
    rationalTreeAmplitude g D
      (.node s CL CR u (.leaf sL (u * CL)) (.leaf sR (u * CR)))
      XL XR (c, !c) (mL, mR) =
      fieldBottomPairValue (pairConjugate g c)
        (rationalTreeArgument s (CL * CR) D XL XR (mL * mR))
        (((sL / sR) * ((XR * CR * mR) / (XL * CL * mL)) : (ZMod p)ˣ) : ZMod p) := by
  cases c
  · exact rationalTreeAmplitude_pair g D s sL sR CL CR u XL XR mL mR
  · have h := rationalTreeAmplitude_pair (fun x => conj (g x)) D s sL sR CL CR u XL XR mL mR
    simp only [pairConjugate, ite_true, Bool.not_true]
    convert h using 1
    simp [rationalTreeAmplitude]

noncomputable def rationalQuartetPairsValue {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR m₁ m₂ m₃ m₄ : (ZMod p)ˣ) : ℂ :=
  let HL := XL * Q.CL * (m₁ * m₂)
  let HR := XR * Q.CR * (m₃ * m₄)
  let v := reconstructedEntry (Q.s : ZMod p) Q.sL Q.sR Q.u HL HR
  if hv : v = 0 then 0 else
    let V := Units.mk0 v hv
    fieldBottomPairValue g (rationalTreeArgument Q.sL (Q.u * Q.CL) D V XL (m₁ * m₂))
      (((Q.s₁ / Q.s₂) * ((XL * Q.C₂ * m₂) / (V * Q.C₁ * m₁)) : (ZMod p)ˣ) : ZMod p) *
    fieldBottomPairValue h (rationalTreeArgument Q.sR (Q.u * Q.CR) D V XR (m₃ * m₄))
      (((Q.s₃ / Q.s₄) * ((XR * Q.C₄ * m₄) / (V * Q.C₃ * m₃)) : (ZMod p)ˣ) : ZMod p)

/-- Both opposite-conjugation choices in each sibling pair are identified
with the actual diagram, independently of the choices in the other pair. -/
theorem rationalTreeAmplitude_quartet_conjugation {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR m₁ m₂ m₃ m₄ : (ZMod p)ˣ) (cL cR : Bool) :
    rationalTreeAmplitude g D Q.tree XL XR ((cL, !cL), (cR, !cR))
      ((m₁, m₂), (m₃, m₄)) =
      rationalQuartetPairsValue (pairConjugate g cL) (pairConjugate g cR)
        D Q XL XR m₁ m₂ m₃ m₄ := by
  unfold RationalQuartetData.tree
  simp only [rationalTreeAmplitude]
  simp only [rationalTreeFrequency_cast]
  simp only [RationalTreeData.frequency, treeLeafProduct]
  unfold rationalQuartetPairsValue
  dsimp only
  by_cases hv : reconstructedEntry (Q.s : ZMod p) Q.sL Q.sR Q.u
      ((XL * Q.CL * (m₁ * m₂) : (ZMod p)ˣ) : ZMod p)
      ((XR * Q.CR * (m₃ * m₄) : (ZMod p)ˣ) : ZMod p) = 0
  · simp only [hv, dite_true]
  · simp only [hv, dite_false]
    let V : (ZMod p)ˣ := Units.mk0 _ hv
    have hL := rationalTreeAmplitude_cast g D Q.left_product
      (.node Q.sL Q.C₁ Q.C₂ Q.uL (.leaf Q.s₁ (Q.uL * Q.C₁))
        (.leaf Q.s₂ (Q.uL * Q.C₂))) V XL (cL, !cL) (m₁, m₂)
    have hR := rationalTreeAmplitude_cast g D Q.right_product
      (.node Q.sR Q.C₃ Q.C₄ Q.uR (.leaf Q.s₃ (Q.uR * Q.C₃))
        (.leaf Q.s₄ (Q.uR * Q.C₄))) V XR (cR, !cR) (m₃, m₄)
    change rationalTreeAmplitude g D (n := 1) _ V XL (cL, !cL) (m₁, m₂) *
      rationalTreeAmplitude g D (n := 1) _ V XR (cR, !cR) (m₃, m₄) = _
    rw [hL, hR, rationalTreeAmplitude_pair_conjugation, rationalTreeAmplitude_pair_conjugation]
    have hargL := congrArg
      (fun C => (rationalTreeArgument Q.sL C D V XL (m₁ * m₂) : ZMod p)) Q.left_product
    have hargR := congrArg
      (fun C => (rationalTreeArgument Q.sR C D V XR (m₃ * m₄) : ZMod p)) Q.right_product
    rw [hargL, hargR]

end Ostmann

end OAI
