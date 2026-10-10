import OAI.NumberTheory.Ostmann.Dirichlet.SmoothedExplicitIntegrand
import OAI.NumberTheory.Ostmann.Dirichlet.SmoothedExplicitRectangle

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Dirichlet
open Complex Set Filter MeasureTheory
open scoped Topology BigOperators SchwartzMap

def smoothExplicitKernel (ρ : 𝓢(ℝ, ℂ)) (X : ℝ) (s : ℂ) : ℂ :=
  mellin (ρ : ℝ → ℂ) s * (X : ℂ)^s

theorem analyticAt_smoothExplicitKernel (ρ : 𝓢(ℝ, ℂ)) {X : ℝ} (hX : 0 < X)
    {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ (smoothExplicitKernel ρ X) s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with z hz
  have hXC : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (X : ℂ)^z) z := by
    simp_rw [Complex.cpow_def_of_ne_zero hXC]
    fun_prop
  exact (schwartz_mellin_differentiableAt ρ hz).mul hpow

theorem smooth_rectangle_residues {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : 𝓢(ℝ, ℂ))
    {X : ℝ} (hX : 0 < X) {z w : ℂ} (hz : 0 < z.re)
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hboundary : ∀ p ∈ Erdos970.RectangleBorder z w, χ.LFunction p ≠ 0) :
    Erdos970.RectangleIntegral' (characterSmoothIntegrand ρ χ X) z w =
      -∑ p ∈ zerosInRectangle χ hχ z w,
        (zeroMultiplicity χ p : ℂ)*smoothExplicitKernel ρ X p := by
  have hK : AnalyticOnNhd ℂ (smoothExplicitKernel ρ X) (Rectangle z w) := by
    intro s hs
    have hsre := ((mem_Rect hre him s).mp hs).1
    exact analyticAt_smoothExplicitKernel ρ hX (hz.trans_le hsre)
  have h := rectangle_integral_neg_LFunction_logDeriv_mul χ hχ hre him hK hboundary
  have he : characterSmoothIntegrand ρ χ X =
      (fun s => -logDeriv χ.LFunction s*smoothExplicitKernel ρ X s) := by
    funext s
    unfold characterSmoothIntegrand smoothExplicitKernel
    ring
  rw [he]
  exact h

theorem contourFactor_mul_I : (1/(2*(Real.pi : ℂ)*Complex.I))*Complex.I = mellinFactor := by
  unfold mellinFactor
  push_cast
  field_simp

theorem character_smooth_five_edges {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : 𝓢(ℝ, ℂ))
    {X left right lo hi : ℝ} (hX : 0 < X) (hleft : 0 < left)
    (hright : 1 < right) (hlr : left ≤ right) (hlohi : lo ≤ hi)
    (hboundary : ∀ p ∈ Erdos970.RectangleBorder ((left:ℂ)+lo*Complex.I) ((right:ℂ)+hi*Complex.I),
      χ.LFunction p ≠ 0) :
    (∑' n : ℕ, χ n*(ArithmeticFunction.vonMangoldt n : ℂ)*ρ ((n:ℝ)/X)) =
      -(∑ p ∈ zerosInRectangle χ hχ ((left:ℂ)+lo*Complex.I) ((right:ℂ)+hi*Complex.I),
        (zeroMultiplicity χ p : ℂ)*smoothExplicitKernel ρ X p) +
      (1/(2*(Real.pi : ℂ)*Complex.I)) *
        (Erdos970.VIntegral (characterSmoothIntegrand ρ χ X) left lo hi -
          Erdos970.HIntegral (characterSmoothIntegrand ρ χ X) left right lo +
          Erdos970.HIntegral (characterSmoothIntegrand ρ χ X) left right hi +
          Complex.I*(∫ t in Iic lo, characterSmoothIntegrand ρ χ X ((right:ℂ)+t*Complex.I)) +
          Complex.I*(∫ t in Ici hi, characterSmoothIntegrand ρ χ X ((right:ℂ)+t*Complex.I))) := by
  let F := characterSmoothIntegrand ρ χ X
  have hrep := character_smooth_mellin ρ χ hright hX
  have hrep' : (∑' n : ℕ, χ n*(ArithmeticFunction.vonMangoldt n : ℂ)*ρ ((n:ℝ)/X)) =
      (1/(2*(Real.pi : ℂ)*Complex.I))*Erdos970.VerticalIntegral F right := by
    rw [Erdos970.VerticalIntegral, smul_eq_mul, ← mul_assoc, contourFactor_mul_I]
    simpa only [F, characterSmoothIntegrand, logDeriv_apply, neg_div] using hrep
  have hrect := smooth_rectangle_residues χ hχ ρ hX
    (z := ((left:ℂ)+lo*Complex.I)) (w := ((right:ℂ)+hi*Complex.I))
    (by simpa using hleft) (by simpa using hlr) (by simpa using hlohi) hboundary
  change Erdos970.RectangleIntegral' F _ _ = _ at hrect
  simp only [Erdos970.RectangleIntegral', Erdos970.RectangleIntegral,
    add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    sub_zero, add_zero, add_im, mul_im, mul_one, zero_add,
    smul_eq_mul] at hrect
  rw [hrep', Erdos970.verticalIntegral_split_three lo hi
    (integrable_characterSmooth_right ρ χ hχ hright hX)]
  simp only [smul_eq_mul]
  calc
    _ = (1/(2*(Real.pi : ℂ)*Complex.I)) *
        (Erdos970.HIntegral F left right lo - Erdos970.HIntegral F left right hi +
          Erdos970.VIntegral F right lo hi - Erdos970.VIntegral F left lo hi) +
      (1/(2*(Real.pi : ℂ)*Complex.I)) *
        (Erdos970.VIntegral F left lo hi - Erdos970.HIntegral F left right lo +
          Erdos970.HIntegral F left right hi +
          Complex.I*(∫ t in Iic lo, F ((right:ℂ)+t*Complex.I)) +
          Complex.I*(∫ t in Ici hi, F ((right:ℂ)+t*Complex.I))) := by ring
    _ = _ := by rw [hrect]

end Ostmann.Dirichlet

end

end OAI
