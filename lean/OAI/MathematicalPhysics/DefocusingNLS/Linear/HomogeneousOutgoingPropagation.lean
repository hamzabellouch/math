import OAI.MathematicalPhysics.DefocusingNLS.Linear.HarmonicRadialNonvanishing
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularRank
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRobinPlane

namespace OAI

/-! # Propagating the outgoing plane back from a mode-dependent far radius

The ODE is linear on every positive closed annulus. A representation by
the two outgoing columns at one far point therefore holds at the fixed
radius used by the canonical boundary operator.
-/

open Set Filter Topology

namespace DefocusingNLS

local notation "V₄" => (ℂ × ℂ) × (ℂ × ℂ)

private theorem physicalField_combination (νp νm eta : ℂ) (m : ℕ) (q : ℂ)
    (r : ℝ) (a b : ℂ) (Zp Zm : V₄) :
    spectralPhysicalCircularField νp νm eta m q r (a • Zp + b • Zm) =
      a • spectralPhysicalCircularField νp νm eta m q r Zp +
        b • spectralPhysicalCircularField νp νm eta m q r Zm := by
  simp only [spectralPhysicalCircularField_regular, spectralRegularField_add,
    spectralRegularField_smul]

private theorem physicalField_sub (νp νm eta : ℂ) (m : ℕ) (q : ℂ)
    (r : ℝ) (Z W : V₄) :
    spectralPhysicalCircularField νp νm eta m q r (Z - W) =
      spectralPhysicalCircularField νp νm eta m q r Z -
        spectralPhysicalCircularField νp νm eta m q r W := by
  simpa only [one_smul, neg_one_smul, sub_eq_add_neg] using
    physicalField_combination νp νm eta m q r 1 (-1) Z W

theorem homogeneousPhysicalOutgoingPlane_backward
    (νp νm eta : ℂ) (m : ℕ) (Q : ℝ → ℂ) (Z Zp Zm : ℝ → V₄)
    (R T : ℝ) (hR : 0 < R) (hRT : R ≤ T)
    (hQ : ContinuousOn Q (Icc R T))
    (hZ : ∀ r ∈ Icc R T, HasDerivAt Z
      (spectralPhysicalCircularField νp νm eta m (Q r) r (Z r)) r)
    (hZp : ∀ r ∈ Icc R T, HasDerivAt Zp
      (spectralPhysicalCircularField νp νm eta m (Q r) r (Zp r)) r)
    (hZm : ∀ r ∈ Icc R T, HasDerivAt Zm
      (spectralPhysicalCircularField νp νm eta m (Q r) r (Zm r)) r)
    (c : ℂ × ℂ) (hc : Z T = c.1 • Zp T + c.2 • Zm T) :
    Z R = c.1 • Zp R + c.2 • Zm R := by
  let D := fun r => Z r - (c.1 • Zp r + c.2 • Zm r)
  have hd (r : ℝ) (hr : r ∈ Icc R T) : HasDerivAt D
      (spectralPhysicalCircularField νp νm eta m (Q r) r (D r)) r := by
    apply ((hZ r hr).sub (((hZp r hr).const_smul c.1).add
      ((hZm r hr).const_smul c.2))).congr_deriv
    dsimp only [D]
    rw [physicalField_sub, physicalField_combination]
  obtain ⟨C, hC⟩ := spectralPhysicalCircularField_bounded_on νp νm eta m Q R T hR hQ
  have hzero := spectral_zero_on_annulus D
    (fun r => spectralPhysicalCircularField νp νm eta m (Q r) r (D r)) R T C
    (fun r hr => (hd r hr).continuousAt.continuousWithinAt) hd
    (fun r hr => hC r hr (D r)) (by simp only [D, hc, sub_self]) R ⟨le_rfl, hRT⟩
  exact sub_eq_zero.mp hzero

theorem homogeneousPhysicalOutgoingPlane_of_eventually
    (νp νm eta : ℂ) (m : ℕ) (Q : ℝ → ℂ) (Z Zp Zm : ℝ → V₄)
    (R₀ : ℝ) (hR₀ : 0 < R₀) (hQ : ContinuousOn Q (Ioi 0))
    (hZ : ∀ r, R₀ ≤ r → HasDerivAt Z
      (spectralPhysicalCircularField νp νm eta m (Q r) r (Z r)) r)
    (hZp : ∀ r, R₀ ≤ r → HasDerivAt Zp
      (spectralPhysicalCircularField νp νm eta m (Q r) r (Zp r)) r)
    (hZm : ∀ r, R₀ ≤ r → HasDerivAt Zm
      (spectralPhysicalCircularField νp νm eta m (Q r) r (Zm r)) r)
    (hout : ∀ᶠ r in atTop, ∃ c : ℂ × ℂ, Z r = c.1 • Zp r + c.2 • Zm r)
    (R : ℝ) (hR : R₀ ≤ R) :
    ∃ c : ℂ × ℂ, Z R = c.1 • Zp R + c.2 • Zm R := by
  obtain ⟨T, ⟨c, hc⟩, hT⟩ := (hout.and (eventually_ge_atTop R)).exists
  refine ⟨c, homogeneousPhysicalOutgoingPlane_backward νp νm eta m Q Z Zp Zm R T
    (hR₀.trans_le hR) hT ?_ ?_ ?_ ?_ c hc⟩
  · exact hQ.mono (fun r hr => (hR₀.trans_le hR).trans_le hr.1)
  · exact fun r hr => hZ r (hR.trans hr.1)
  · exact fun r hr => hZp r (hR.trans hr.1)
  · exact fun r hr => hZm r (hR.trans hr.1)

end DefocusingNLS

end OAI
