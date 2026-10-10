import OAI.NumberTheory.Ostmann.Characters.TreeCoordinates
import OAI.NumberTheory.Ostmann.ZeroDensity.PairDensity

namespace OAI

/-!
# The density bound for an actual reconstructed node

The fixed parent product makes its argument independent of the split.
The reconstructed entry vanishes exactly when the child ratio is one.
Thus the inverse-square density estimate applies to the actual formulas,
with the manuscript's invalid-node convention.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def rationalNodeArgument {p : ℕ} [Fact p.Prime]
    (s D XL XR CL CR P : (ZMod p)ˣ) : (ZMod p)ˣ :=
  s / (D * XL * CL * XR * CR * P)

noncomputable def rationalNodeRatioConstant {p : ℕ} [Fact p.Prime]
    (sL sR XL XR CL CR P : (ZMod p)ˣ) : (ZMod p)ˣ :=
  (sL / sR) * (XR * CR * P / (XL * CL))

noncomputable def rationalNodeValue {p : ℕ} [Fact p.Prime]
    (s sL sR D u XL XR CL CR P : (ZMod p)ˣ)
    (f g : ZMod p → ℝ) (m : (ZMod p)ˣ) : ℝ :=
  let HL : (ZMod p)ˣ := XL * CL * m
  let HR : (ZMod p)ˣ := XR * CR * (P / m)
  let v := reconstructedEntry (s : ZMod p) sL sR u HL HR
  if v = 0 then 0 else
    f (childArgument sL D u HL v) * g (childArgument sR D u HR v)

theorem rationalNodeValue_eq_ratio {p : ℕ} [Fact p.Prime]
    (s sL sR D u XL XR CL CR P : (ZMod p)ˣ)
    (f g : ZMod p → ℝ) (m : (ZMod p)ˣ) :
    rationalNodeValue s sL sR D u XL XR CL CR P f g m =
      let d := rationalNodeArgument s D XL XR CL CR P
      let t := rationalNodeRatioConstant sL sR XL XR CL CR P * (m⁻¹) ^ 2
      if t = 1 then 0 else
        f ((d : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1)) *
          g ((d : ZMod p) / ((t : ZMod p) - 1)) := by
  classical
  let HL : (ZMod p)ˣ := XL * CL * m
  let HR : (ZMod p)ˣ := XR * CR * (P / m)
  let v := reconstructedEntry (s : ZMod p) sL sR u HL HR
  let d := rationalNodeArgument s D XL XR CL CR P
  let t := rationalNodeRatioConstant sL sR XL XR CL CR P * (m⁻¹) ^ 2
  have ht : (sL : ZMod p) / sR * ((HR : ZMod p) / HL) = (t : ZMod p) := by
    have h : (sL / sR) * (HR / HL) = t :=
      tree_product_ratio sL sR XL XR CL CR P m
    exact_mod_cast h
  have hd : parentArgument (s : ZMod p) D HL HR = (d : ZMod p) := by
    dsimp [HL, HR, d, rationalNodeArgument]
    simp only [Units.val_mul, Units.val_div_eq_div_val]
    exact tree_parent_fixed_product (s : ZMod p) D XL XR CL CR P m (Units.ne_zero m)
  have hv : v = 0 ↔ t = 1 := by
    have h := reconstructedEntry_zero_iff_ratio_one (s : ZMod p) sL sR u HL HR
      (Units.ne_zero s) (Units.ne_zero sR) (Units.ne_zero u) (Units.ne_zero HL)
    rw [ht] at h
    constructor
    · intro hz
      exact Units.ext (h.mp hz)
    · intro h1
      apply h.mpr
      simp only [h1, Units.val_one]
  change (if v = 0 then 0 else
    f (childArgument sL D u HL v) * g (childArgument sR D u HR v)) =
      if t = 1 then 0 else
        f ((d : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1)) *
          g ((d : ZMod p) / ((t : ZMod p) - 1))
  by_cases hv0 : v = 0
  · simp only [hv0, hv.mp hv0, ite_true]
  · have ht1 : t ≠ 1 := fun h => hv0 (hv.mpr h)
    simp only [hv0, ht1, ite_false]
    have hpair := tree_children_eq_pair_coordinates (s : ZMod p) sL sR D u HL HR v
      (Units.ne_zero s) (Units.ne_zero sR) (Units.ne_zero D) (Units.ne_zero u)
      (Units.ne_zero HL) (Units.ne_zero HR) hv0
      (reconstructedEntry_relation (s : ZMod p) sL sR u HL HR (Units.ne_zero s) (Units.ne_zero u))
    rw [ht, hd] at hpair
    exact congrArg (fun xz : ZMod p × ZMod p => f xz.1 * g xz.2) hpair

/-- Conditional counting density of one actual rational tree split. -/
theorem rationalNodeValue_sum_le {p : ℕ} [Fact p.Prime]
    (s sL sR D u XL XR CL CR P : (ZMod p)ˣ)
    (f g : ZMod p → ℝ) (hf : f 0 = 0) (hg : g 0 = 0)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) :
    (∑ m : (ZMod p)ˣ, rationalNodeValue s sL sR D u XL XR CL CR P f g m) ≤
      2 * ∑ x : ZMod p, f x * g (x - rationalNodeArgument s D XL XR CL CR P) := by
  simp_rw [rationalNodeValue_eq_ratio]
  exact pair_inverse_square_density _ _ f g hf hg hfn hgn

end Ostmann

end OAI
