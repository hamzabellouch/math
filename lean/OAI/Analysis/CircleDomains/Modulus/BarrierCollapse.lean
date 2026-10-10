import OAI.Analysis.CircleDomains.Modulus.LinePayment
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.Compact

namespace OAI

/-!
# Collapse forced by barriers of vanishing energy

The line-payment inequality prevents barriers of vanishing energy from
crossing every horizontal line over a fixed interval of positive length.
Applied to both coordinate projections, this forces a compact connected
planar set to be a singleton. The hypotheses specify barrier existence,
crossings, and absolute continuity of the restrictions.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace CircleDomainRigidity

/-- A sequence of actual rectangle barriers, each crossing almost every
horizontal line over `(a,b]`, whose squared horizontal derivative energies
tend to zero. The supporting horizontal interval is fixed for the sequence. -/
def HasVanishingRectangleBarriers (a b : ℝ) : Prop :=
  ∃ L : ℝ, 0 < L ∧ ∃ v : ℕ → ℝ → ℝ → ℝ,
    (∀ n, Integrable (fun p : ℝ × ℝ => deriv (v n p.1) p.2 ^ 2)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc (-L) L)))) ∧
    (∀ n, ∀ᵐ y ∂volume.restrict (Ioc a b),
      AbsolutelyContinuousOnInterval (v n y) (-L) L ∧ v n y (-L) = 0 ∧
        ∃ c ∈ Icc (-L) L, v n y c = 1) ∧
    Tendsto (fun n => ∫ p : ℝ × ℝ, deriv (v n p.1) p.2 ^ 2
      ∂((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc (-L) L))))
      atTop (𝓝 0)

/-- A nondegenerate interval cannot support crossings by barriers whose
energies tend to zero. This is the contradiction step after line payment. -/
theorem eq_of_vanishing_rectangle_barriers {a b : ℝ} (hab : a ≤ b)
    (hbar : HasVanishingRectangleBarriers a b) : a = b := by
  obtain ⟨L, hL, v, hEnergy, hSlices, hlimit⟩ := hbar
  have hbound : (b - a) / (2 * L) ≤ 0 :=
    ge_of_tendsto hlimit (Filter.Eventually.of_forall (fun n =>
      integrated_line_payment_of_absolutelyContinuous hL hab (hEnergy n) (hSlices n)))
  have hlength : b - a ≤ 0 := by
    simpa using (div_le_iff₀ (mul_pos (by norm_num) hL)).mp hbound
  linarith

/-- If both coordinate projection intervals of a compact connected planar
set admit the barriers above, then every two points of the set coincide.
Compactness and connectedness identify the projections with the full
closed intervals between their extrema. -/
theorem subsingleton_of_vanishing_projection_barriers {K : Set ℂ}
    (hcompact : IsCompact K) (hconnected : IsConnected K)
    (hre : HasVanishingRectangleBarriers
      (sInf (Complex.re '' K)) (sSup (Complex.re '' K)))
    (him : HasVanishingRectangleBarriers
      (sInf (Complex.im '' K)) (sSup (Complex.im '' K))) :
    K.Subsingleton := by
  have hReInterval : Complex.re '' K =
      Icc (sInf (Complex.re '' K)) (sSup (Complex.re '' K)) :=
    eq_Icc_of_connected_compact
      (hconnected.image Complex.re Complex.continuous_re.continuousOn)
      (hcompact.image Complex.continuous_re)
  have hImInterval : Complex.im '' K =
      Icc (sInf (Complex.im '' K)) (sSup (Complex.im '' K)) :=
    eq_Icc_of_connected_compact
      (hconnected.image Complex.im Complex.continuous_im.continuousOn)
      (hcompact.image Complex.continuous_im)
  have hReNonempty :
      (Icc (sInf (Complex.re '' K)) (sSup (Complex.re '' K))).Nonempty :=
    hReInterval ▸ hconnected.nonempty.image Complex.re
  have hImNonempty :
      (Icc (sInf (Complex.im '' K)) (sSup (Complex.im '' K))).Nonempty :=
    hImInterval ▸ hconnected.nonempty.image Complex.im
  have hReEq := eq_of_vanishing_rectangle_barriers (nonempty_Icc.mp hReNonempty) hre
  have hImEq := eq_of_vanishing_rectangle_barriers (nonempty_Icc.mp hImNonempty) him
  intro z hz w hw
  have hzre : z.re ∈ Icc (sInf (Complex.re '' K)) (sSup (Complex.re '' K)) :=
    hReInterval ▸ mem_image_of_mem Complex.re hz
  have hwre : w.re ∈ Icc (sInf (Complex.re '' K)) (sSup (Complex.re '' K)) :=
    hReInterval ▸ mem_image_of_mem Complex.re hw
  have hzim : z.im ∈ Icc (sInf (Complex.im '' K)) (sSup (Complex.im '' K)) :=
    hImInterval ▸ mem_image_of_mem Complex.im hz
  have hwim : w.im ∈ Icc (sInf (Complex.im '' K)) (sSup (Complex.im '' K)) :=
    hImInterval ▸ mem_image_of_mem Complex.im hw
  apply Complex.ext
  · exact le_antisymm (hzre.2.trans (hReEq ▸ hwre.1))
      (hwre.2.trans (hReEq ▸ hzre.1))
  · exact le_antisymm (hzim.2.trans (hImEq ▸ hwim.1))
      (hwim.2.trans (hImEq ▸ hzim.1))

end CircleDomainRigidity

end OAI
