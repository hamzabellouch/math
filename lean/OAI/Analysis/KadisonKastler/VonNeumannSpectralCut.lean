import OAI.Analysis.KadisonKastler.PublishedTypeIIIProjection
import OAI.Analysis.FactorGeneration.Supports

namespace OAI

/-! # Positive spectral cuts in a von Neumann algebra

The support of the positive part of `x* x - t` gives the required
projection. The existing concrete range-projection construction supplies
its membership in the von Neumann algebra.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

local instance spectralCutOrder {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) :
    PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance spectralCutPreorder {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) :
    Preorder M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toPreorder
local instance spectralCutLE {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) :
    LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance spectralCutStarOrder {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) :
    StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

/-- Positive support and continuous functional calculus give spectral cuts. -/
theorem publishedVonNeumannSpectralCut : PublishedVonNeumannSpectralCut.{u} := by
  intro H _ _ _ M x t ht hnorm
  let a : Algebra M := star x * x
  have ha : 0 ≤ a := star_mul_self_nonneg x
  have hsa : IsSelfAdjoint a := IsSelfAdjoint.star_mul_self x
  let p := spectralCut a t
  have hp : p.val * p.val = p.val := p.property.isIdempotentElem.eq
  have hpn : p.val ≠ 0 := by
    intro hz
    have hu := spectralCut_upper_complement a hsa t
    change (1 - p.val) * (a - (t : ℂ) • 1) * (1 - p.val) ≤ 0 at hu
    rw [hz, sub_zero, one_mul, mul_one] at hu
    have haBound : a ≤ algebraMap ℝ (Algebra M) t := by
      simpa only [Algebra.algebraMap_eq_smul_one, Complex.coe_smul] using sub_nonpos.mp hu
    have hn := (CStarAlgebra.norm_le_iff_le_algebraMap a ht.le ha).mpr haBound
    exact (not_le_of_gt hnorm) hn
  have hcomm : p.val * a = a * p.val := by
    have hc := (positiveSupport_commutes (a - (t : ℂ) • 1)
      (spectralShift_selfAdjoint a hsa t)).eq
    change p.val * (a - (t : ℂ) • 1) = (a - (t : ℂ) • 1) * p.val at hc
    simpa only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul,
      sub_left_inj] using hc
  have hlow := spectralCut_lower a hsa t
  change 0 ≤ p.val * (a - (t : ℂ) • 1) * p.val at hlow
  have hlow' : 0 ≤ p.val * a * p.val - t • p.val := by
    simpa only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, hp,
      Complex.coe_smul] using hlow
  have hrest : 0 ≤ (1 - p.val) * a * (1 - p.val) := by
    simpa only [star_sub, star_one, p.property.isSelfAdjoint.star_eq] using
      star_left_conjugate_nonneg ha (1 - p.val)
  have he : p.val * a * p.val + (1 - p.val) * a * (1 - p.val) = a := by
    have hpap : p.val * a * p.val = p.val * a := by rw [hcomm, mul_assoc, hp, ← hcomm]
    have hrestEq : (1 - p.val) * a * (1 - p.val) =
        a - a * p.val - p.val * a + p.val * a * p.val := by noncomm_ring
    rw [hrestEq, hpap, hcomm]
    abel
  refine ⟨p.val, p.property, hpn, ?_⟩
  apply sub_nonneg.mp
  have hs := add_nonneg hlow' hrest
  have he' : p.val * a * p.val - t • p.val + (1 - p.val) * a * (1 - p.val) =
      a - t • p.val := by rw [sub_add_eq_add_sub, he]
  rwa [he'] at hs

end

end KadisonKastler

end OAI
