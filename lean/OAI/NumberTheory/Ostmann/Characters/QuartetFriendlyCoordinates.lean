import OAI.NumberTheory.Ostmann.Tree.RationalQuartetValue
import OAI.NumberTheory.Ostmann.Tree.CrossPairHeldAverage

namespace OAI

/-! # The two-friendly orientation of an actual rational quartet -/

namespace Ostmann

open scoped BigOperators

theorem pair_ratio_friendly {p : ℕ} [Fact p.Prime]
    (D s s₁ s₂ C₁ C₂ V X m₁ m₂ : (ZMod p)ˣ) :
    (s₁ / s₂) * ((X * C₂ * m₂) / (V * C₁ * m₁)) =
      ((D * s₁ / (s₂ * s)) * (X * C₂) ^ 2 * m₂ ^ 2) *
        rationalTreeArgument s (C₁ * C₂) D V X (m₁ * m₂) := by
  unfold rationalTreeArgument
  apply Units.ext
  simp only [Units.val_mul, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
  field_simp

noncomputable def quartetLeftHeld {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ) (XL : (ZMod p)ˣ) : (ZMod p)ˣ :=
  (D * Q.s₁ / (Q.s₂ * Q.sL)) * (XL * Q.C₂) ^ 2

noncomputable def quartetRightHeld {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ) (XR : (ZMod p)ˣ) : (ZMod p)ˣ :=
  (D * Q.s₃ / (Q.s₄ * Q.sR)) * (XR * Q.C₄) ^ 2

noncomputable def quartetMovingMultiplier {p : ℕ} [Fact p.Prime]
    (Q : RationalQuartetData (ZMod p)ˣ) (XL XR P a : (ZMod p)ˣ) : (ZMod p)ˣ :=
  (Q.sL / Q.sR) * (XR * Q.CR * P / (XL * Q.CL)) * (a⁻¹) ^ 2

/-- Reciprocal coordinates on the two moving leaves preserve the quartet product. -/
theorem quartet_friendly_product {G : Type*} [CommGroup G] (P a b r : G) :
    (r⁻¹ * a) * (P * r / (a * b) * b) = P := by
  calc
    _ = P * (r⁻¹ * r) * (a * a⁻¹) * (b⁻¹ * b) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ac_rfl
    _ = P := by simp

/-- The ratio at the quartet root is a fixed multiple of the moving square. -/
theorem quartet_friendly_ratio {p : ℕ} [Fact p.Prime]
    (Q : RationalQuartetData (ZMod p)ˣ) (XL XR P a b r : (ZMod p)ˣ) :
    (Q.sL / Q.sR) * ((XR * Q.CR * (P * r / (a * b) * b)) /
      (XL * Q.CL * (r⁻¹ * a))) = quartetMovingMultiplier Q XL XR P a * r ^ 2 := by
  unfold quartetMovingMultiplier
  apply Units.ext
  simp only [Units.val_mul, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val,
    Units.val_inv_eq_inv_val]
  field_simp

/-- The actual depth-two diagram, with residual entries held on both sides,
is exactly the quartet ratio function used in the coefficient majorant. -/
theorem rationalQuartetValue_friendly {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR P a b r : (ZMod p)ˣ) :
    rationalQuartetValue g D Q XL XR r⁻¹ a (P * r / (a * b)) b =
      quartetRatioValue g g true true
        (rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P)
        (quartetLeftHeld D Q XL * a ^ 2) (quartetRightHeld D Q XR * b ^ 2)
        (quartetMovingMultiplier Q XL XR P a * r ^ 2) := by
  let HL := XL * Q.CL * (r⁻¹ * a)
  let HR := XR * Q.CR * (P * r / (a * b) * b)
  let v := reconstructedEntry (Q.s : ZMod p) Q.sL Q.sR Q.u HL HR
  let y := rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P
  let t := quartetMovingMultiplier Q XL XR P a * r ^ 2
  have hratio : ((Q.sL : ZMod p) / Q.sR) * ((HR : ZMod p) / HL) = (t : ZMod p) := by
    rw [← Units.val_div_eq_div_val, ← Units.val_div_eq_div_val, ← Units.val_mul]
    exact congrArg (fun x : (ZMod p)ˣ => (x : ZMod p)) (quartet_friendly_ratio Q XL XR P a b r)
  have hparent : parentArgument (Q.s : ZMod p) D HL HR = (y : ZMod p) := by
    have hprod := quartet_friendly_product P a b r
    have hunit : Q.s / (D * HL * HR) = y := by
      dsimp [y, rationalTreeArgument, HL, HR]
      rw [show D * (XL * Q.CL * (r⁻¹ * a)) *
          (XR * Q.CR * (P * r / (a * b) * b)) =
          D * XL * XR * (Q.CL * Q.CR) * ((r⁻¹ * a) * (P * r / (a * b) * b)) by
        simp [mul_assoc, mul_left_comm, mul_comm]]
      rw [hprod]
    simpa only [parentArgument, Units.val_div_eq_div_val, Units.val_mul] using
      congrArg (fun x : (ZMod p)ˣ => (x : ZMod p)) hunit
  have hzero : v = 0 ↔ t = 1 := by
    have hz := reconstructedEntry_zero_iff_ratio_one (Q.s : ZMod p) Q.sL Q.sR Q.u HL HR
      (Units.ne_zero Q.s) (Units.ne_zero Q.sR) (Units.ne_zero Q.u) (Units.ne_zero HL)
    rw [hratio] at hz
    exact ⟨fun h => Units.ext (hz.mp h),
      fun h => hz.mpr (congrArg (fun x : (ZMod p)ˣ => (x : ZMod p)) h)⟩
  change (if hv : v = 0 then 0 else _) = quartetRatioValue g g true true y _ _ t
  by_cases hv : v = 0
  · simp [hv, quartetRatioValue, ratioTest, hzero.mp hv]
  · simp only [hv, dite_false]
    let V : (ZMod p)ˣ := Units.mk0 v hv
    let d := rationalTreeArgument Q.sL (Q.u * Q.CL) D V XL (r⁻¹ * a)
    let e := rationalTreeArgument Q.sR (Q.u * Q.CR) D V XR (P * r / (a * b) * b)
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
        (Units.ne_zero HR) (Units.ne_zero V)).trans hratio
    have hleft := pair_ratio_friendly D Q.sL Q.s₁ Q.s₂ Q.C₁ Q.C₂ V XL r⁻¹ a
    have hright := pair_ratio_friendly D Q.sR Q.s₃ Q.s₄ Q.C₃ Q.C₄ V XR (P * r / (a * b)) b
    rw [Q.left_product] at hleft
    rw [Q.right_product] at hright
    have hh := quartetRatioValue_at_difference g g true true y d e
      (quartetLeftHeld D Q XL * a ^ 2) (quartetRightHeld D Q XR * b ^ 2) hdiff
    rw [hde] at hh
    rw [hh]
    change fieldBottomPairValue g d _ * fieldBottomPairValue g e _ = _
    rw [hleft, hright]
    rfl

end Ostmann

end OAI
