import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCanonicalParameterPower

namespace OAI

/-! Smoothness of the physical parameter values on a sufficiently large exterior interval. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem canonicalPhysicalParameterValues_smooth_tail (ν η b : ℂ) (n : ℕ) (hn : 1≤n)
    (L : ℝ) (hX : HasRadialExterior ν n b L) (hb : b ≠ 0)
    (c : ℂ × ℂ) (Y : ℂ → ℝ → E₄)
    (hY : IsCanonicalHolomorphicColumn ν η b n L c Y) (z : ℂ) :
    ∃ R : ℝ, 1<R ∧ ContDiffOn ℝ ∞ (canonicalPhysicalParameterValues ν Y z) (Ioi R) := by
  let f := fun t => (circularParameterShear t (Y z t) (deriv (fun lam => Y lam t) z)).1.1
  let g := fun t => (circularParameterShear t (Y z t) (deriv (fun lam => Y lam t) z)).2.1
  have hj := canonical_parameterShear_value_logJets ν η b n hn L hX hb c Y hY z 1 zero_lt_one
  obtain ⟨Lf,hfs⟩ := hj.1.smooth
  obtain ⟨Lg,hgs⟩ := hj.2.smooth
  let T := max Lf Lg
  let R := max (Real.exp T) 1+1
  have hR : 1<R := by dsimp only [R]; linarith [le_max_right (Real.exp T) 1]
  have hER : Real.exp T≤R := by dsimp only [R]; linarith [le_max_left (Real.exp T) 1]
  have hp := spectralPowerValues_smooth (ν-2*z) (star ν-2*z) f g T
    (hfs.mono (Ioi_subset_Ioi (le_max_left _ _)))
    (hgs.mono (Ioi_subset_Ioi (le_max_right _ _)))
  refine ⟨R,hR,(hp.mono (Ioi_subset_Ioi hER)).congr ?_⟩
  intro r hr
  exact canonicalPhysicalParameterValues_eq ν η b n L c Y hY z r (hR.trans hr)

end DefocusingNLS

end OAI
