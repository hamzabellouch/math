import OAI.Analysis.KadisonKastler.Algebra
import OAI.Analysis.FactorGeneration.SpectralPinching

namespace OAI

/-! A nonzero operator supported on a projection has a nonzero spectral
subprojection on which its square is uniformly bounded below. -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance cornerWitnessOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance cornerWitnessPreorder : Preorder (Algebra M) :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance cornerWitnessLE : LE (Algebra M) :=
  (CStarAlgebra.spectralOrder _).toLE
local instance cornerWitnessStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

theorem exists_corner_spectral_lower_bound (e : AlgebraProjection M)
    (b : Algebra M) (hb : b * e.val = b) (hbn : b ≠ 0) :
    ∃ (p : AlgebraProjection M) (t : ℝ), p ≤ e ∧ p.val ≠ 0 ∧ 0 < t ∧
      t • p.val ≤ p.val * (star b * b) * p.val := by
  let a : Algebra M := star b * b
  let t : ℝ := ‖a‖ / 2
  have ha : 0 ≤ a := star_mul_self_nonneg b
  have han : 0 < ‖a‖ := norm_pos_iff.mpr (fun h =>
    hbn ((CStarRing.star_mul_self_eq_zero_iff b).mp h))
  have ht : 0 < t := by dsimp [t]; positivity
  have hea : e.val * a * e.val = a := by
    have hs : e.val * star b = star b := by
      simpa only [star_mul, e.property.isSelfAdjoint.star_eq] using congrArg star hb
    dsimp [a]
    rw [← mul_assoc, hs, mul_assoc, hb]
  let p := cornerSpectralCut e a t
  have hp : p ≤ e := cornerSpectralCut_le e a (IsSelfAdjoint.star_mul_self b) t
  have hpn : p.val ≠ 0 := by
    intro hz
    have hu := cornerSpectralCut_upper e a (IsSelfAdjoint.star_mul_self b) t
    change (e.val - p.val) * a * (e.val - p.val) - (t : ℂ) • (e.val - p.val) ≤ 0 at hu
    rw [hz, sub_zero, hea] at hu
    have hle : a ≤ t • e.val := by
      simpa only [Complex.coe_smul] using sub_nonpos.mp hu
    have het : t • e.val ≤ t • (1 : Algebra M) :=
      smul_le_smul_of_nonneg_left e.property.le_one ht.le
    have hbound : a ≤ algebraMap ℝ (Algebra M) t := by
      simpa only [Algebra.algebraMap_eq_smul_one] using hle.trans het
    have hn := (CStarAlgebra.norm_le_iff_le_algebraMap a ht.le ha).mpr hbound
    dsimp [t] at hn
    change ‖a‖ ≤ ‖a‖ / 2 at hn
    linarith
  refine ⟨p, t, hp, hpn, ht, ?_⟩
  have hl := cornerSpectralCut_lower e a (IsSelfAdjoint.star_mul_self b) t
  exact sub_nonneg.mp (by simpa only [Complex.coe_smul] using hl)

end

end KadisonKastler

end OAI
