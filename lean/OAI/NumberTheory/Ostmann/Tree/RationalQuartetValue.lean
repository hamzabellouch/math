import OAI.NumberTheory.Ostmann.Tree.RationalPairValue

namespace OAI

/-! # Bottom quartets in the actual rational-tree recursion -/

namespace Ostmann

open scoped BigOperators

@[simp] theorem rationalTreeFrequency_cast {U : Type*} [CommGroup U]
    {n : ℕ} {C C' : U} (h : C = C') (T : RationalTreeData U n C) :
    (h ▸ T).frequency = T.frequency := by
  cases h
  rfl

@[simp] theorem rationalTreeAmplitude_cast {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) {n : ℕ} {C C' : (ZMod p)ˣ}
    (h : C = C') (T : RationalTreeData (ZMod p)ˣ n C)
    (XL XR : (ZMod p)ˣ) (c : TreeLeafTuple Bool n) (m : TreeLeafTuple (ZMod p)ˣ n) :
    rationalTreeAmplitude g D (h ▸ T) XL XR c m =
      rationalTreeAmplitude g D T XL XR c m := by
  cases h
  rfl

/-- The fixed data above a bottom quartet; its four leaf products remain free. -/
structure RationalQuartetData (U : Type*) [CommGroup U] where
  s : U
  sL : U
  sR : U
  u : U
  CL : U
  CR : U
  s₁ : U
  s₂ : U
  s₃ : U
  s₄ : U
  uL : U
  uR : U
  C₁ : U
  C₂ : U
  C₃ : U
  C₄ : U
  left_product : C₁ * C₂ = u * CL
  right_product : C₃ * C₄ = u * CR

def RationalQuartetData.tree {U : Type*} [CommGroup U] (Q : RationalQuartetData U) :
    RationalTreeData U 2 (Q.CL * Q.CR) :=
  .node Q.s Q.CL Q.CR Q.u
    (Q.left_product ▸ (.node Q.sL Q.C₁ Q.C₂ Q.uL
      (.leaf Q.s₁ (Q.uL * Q.C₁)) (.leaf Q.s₂ (Q.uL * Q.C₂))))
    (Q.right_product ▸ (.node Q.sR Q.C₃ Q.C₄ Q.uR
      (.leaf Q.s₃ (Q.uR * Q.C₃)) (.leaf Q.s₄ (Q.uR * Q.C₄))))

noncomputable def rationalQuartetValue {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR m₁ m₂ m₃ m₄ : (ZMod p)ˣ) : ℂ :=
  let HL := XL * Q.CL * (m₁ * m₂)
  let HR := XR * Q.CR * (m₃ * m₄)
  let v := reconstructedEntry (Q.s : ZMod p) Q.sL Q.sR Q.u HL HR
  if hv : v = 0 then 0 else
    let V := Units.mk0 v hv
    fieldBottomPairValue g (rationalTreeArgument Q.sL (Q.u * Q.CL) D V XL (m₁ * m₂))
      (((Q.s₁ / Q.s₂) * ((XL * Q.C₂ * m₂) / (V * Q.C₁ * m₁)) : (ZMod p)ˣ) : ZMod p) *
    fieldBottomPairValue g (rationalTreeArgument Q.sR (Q.u * Q.CR) D V XR (m₃ * m₄))
      (((Q.s₃ / Q.s₄) * ((XR * Q.C₄ * m₄) / (V * Q.C₃ * m₃)) : (ZMod p)ˣ) : ZMod p)

/-- This local value is the depth-two instance of the same tree amplitude
used in the global cycle projection, rather than a new surrogate diagram. -/
theorem rationalTreeAmplitude_quartet {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR m₁ m₂ m₃ m₄ : (ZMod p)ˣ) :
    rationalTreeAmplitude g D Q.tree XL XR ((false, true), (false, true))
      ((m₁, m₂), (m₃, m₄)) = rationalQuartetValue g D Q XL XR m₁ m₂ m₃ m₄ := by
  unfold RationalQuartetData.tree
  simp only [rationalTreeAmplitude]
  simp only [rationalTreeFrequency_cast]
  simp only [RationalTreeData.frequency, treeLeafProduct]
  unfold rationalQuartetValue
  dsimp only
  by_cases hv : reconstructedEntry (Q.s : ZMod p) Q.sL Q.sR Q.u
      ((XL * Q.CL * (m₁ * m₂) : (ZMod p)ˣ) : ZMod p)
      ((XR * Q.CR * (m₃ * m₄) : (ZMod p)ˣ) : ZMod p) = 0
  · simp only [hv, dite_true]
  · simp only [hv, dite_false]
    let V : (ZMod p)ˣ := Units.mk0 _ hv
    have hL := rationalTreeAmplitude_cast g D Q.left_product
      (.node Q.sL Q.C₁ Q.C₂ Q.uL (.leaf Q.s₁ (Q.uL * Q.C₁))
        (.leaf Q.s₂ (Q.uL * Q.C₂))) V XL (false, true) (m₁, m₂)
    have hR := rationalTreeAmplitude_cast g D Q.right_product
      (.node Q.sR Q.C₃ Q.C₄ Q.uR (.leaf Q.s₃ (Q.uR * Q.C₃))
        (.leaf Q.s₄ (Q.uR * Q.C₄))) V XR (false, true) (m₃, m₄)
    change rationalTreeAmplitude g D (n := 1) _ V XL (false, true) (m₁, m₂) *
      rationalTreeAmplitude g D (n := 1) _ V XR (false, true) (m₃, m₄) = _
    rw [hL, hR, rationalTreeAmplitude_pair, rationalTreeAmplitude_pair]
    have hargL := congrArg
      (fun C => (rationalTreeArgument Q.sL C D V XL (m₁ * m₂) : ZMod p)) Q.left_product
    have hargR := congrArg
      (fun C => (rationalTreeArgument Q.sR C D V XR (m₃ * m₄) : ZMod p)) Q.right_product
    rw [hargL, hargR]

end Ostmann

end OAI
