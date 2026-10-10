import OAI.Analysis.LipschitzHilbert.Packets.UnitPacketSelector

namespace OAI

/-! The actual selectors at angular scale `d`: measurability, unit
size, support away from the label, and the required scaled Lipschitz bound. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

def scaledUnitSelector (chi : SchwartzMap ℝ ℝ) (C : ℝ) (S : SchwartzMap SymbolSpace ℂ)
    (q : ℕ) (nu : SymbolSpace) (d theta s : ℝ) : ℂ :=
  unitPacketSelector chi C S q nu ((s-theta)/d)

theorem scaledUnitSelector_measurable (chi : SchwartzMap ℝ ℝ) (C : ℝ)
    (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (nu : SymbolSpace) (d theta : ℝ) :
    Measurable (scaledUnitSelector chi C S q nu d theta) :=
  ((unitPacketSelector_differentiable chi C S q nu).continuous.comp (by fun_prop)).measurable

theorem scaledUnitSelector_bound (chi : SchwartzMap ℝ ℝ) (hchi : ∀ U, |chi U|≤1)
    (C : ℝ) (hC : 0<C) (S : SchwartzMap SymbolSpace ℂ) (q : ℕ)
    (hS : symbolCoefficientBound S q≤C) (nu : SymbolSpace) (d theta s : ℝ) :
    ‖scaledUnitSelector chi C S q nu d theta s‖≤1 :=
  unitPacketSelector_bound chi hchi C hC S q hS nu ((s-theta)/d)

theorem scaledUnitSelector_lipschitz (chi : SchwartzMap ℝ ℝ) (hchi : ∀ U, |chi U|≤1)
    (C : ℝ) (hC : 0<C) (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (hq : 1≤q)
    (hS : symbolCoefficientBound S q≤C) (nu : SymbolSpace) (d theta : ℝ) (hd : 0<d)
    (s t : ℝ) :
    ‖scaledUnitSelector chi C S q nu d theta s-scaledUnitSelector chi C S q nu d theta t‖≤
      |s-t|/d := by
  have h := (unitPacketSelector_lipschitz chi hchi C hC S q hq hS nu).dist_le_mul
    ((s-theta)/d) ((t-theta)/d)
  change ‖unitPacketSelector chi C S q nu ((s-theta)/d)-
    unitPacketSelector chi C S q nu ((t-theta)/d)‖≤_
  calc
    _ ≤ dist ((s-theta)/d) ((t-theta)/d) := by simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using h
    _ = _ := by
      rw [Real.dist_eq, show (s-theta)/d-(t-theta)/d=(s-t)/d by ring, abs_div, abs_of_pos hd]

theorem scaledUnitSelector_annular_support (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (C : ℝ) (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (nu : SymbolSpace)
    (d theta s : ℝ) (hd : 0<d)
    (h : scaledUnitSelector (annularCutoff a b ha hb) C S q nu d theta s≠0) :
    (a/2)*d≤|s-theta| ∧ |s-theta|≤(2*b)*d := by
  have hl : localizedSelector (annularCutoff a b ha hb) S q nu ((s-theta)/d)≠0 := by
    intro hz
    apply h
    simp only [scaledUnitSelector, unitPacketSelector, hz, mul_zero]
  have hs := localizedSelector_support a b ha hb S q nu ((s-theta)/d) hl
  rw [abs_div, abs_of_pos hd] at hs
  exact ⟨((lt_div_iff₀ hd).mp hs.1).le, ((div_lt_iff₀ hd).mp hs.2).le⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
