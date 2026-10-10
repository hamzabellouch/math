import OAI.Geometry.SurfaceImmersion.Geometry.OrderedBoundaryInvariant

namespace OAI

/-! At a prepared point, a pure radial second form gives the strict ordered
crossing inequality even for proportional nonzero tangent directions. -/
noncomputable section
open scoped Matrix
namespace ClosedSurfaceR4.VelocityFrame
open RealModes SmallModes NormalFrame

lemma normalize_positive_smul {n : Vec} (hn : n ⬝ᵥ n = 1) {c : ℝ} (hc : 0 < c) :
    normalize (c • n) = n := by
  have hs : Real.sqrt (c*c) = c := by
    nlinarith [Real.sq_sqrt (show 0 ≤ c*c by positivity),Real.sqrt_nonneg (c*c)]
  simp only [normalize,smul_dotProduct,dotProduct_smul,smul_eq_mul,hn,mul_one,hs,smul_smul,
    inv_mul_cancel₀ hc.ne',one_smul]

lemma orderedCrossing_pure_radial {F : RField 4} (p v w : Base) (n : Vec)
    {r : ℝ} (hr : 0 < r) (hn : n ⬝ᵥ n = 1)
    (hv : coordDeriv v F p ≠ 0) (hw : coordDeriv w F p ≠ 0)
    (hvv : realSecondForm F v v p =
      (r⁻¹*(coordDeriv v F p ⬝ᵥ coordDeriv v F p)) • n)
    (hvw : realSecondForm F v w p =
      (r⁻¹*(coordDeriv v F p ⬝ᵥ coordDeriv w F p)) • n) :
    orderedCrossing F v w p ((r⁻¹)^2) =
      (r⁻¹)^2*(coordDeriv v F p ⬝ᵥ coordDeriv v F p)*
        (coordDeriv w F p ⬝ᵥ coordDeriv w F p) ∧
      0 < orderedCrossing F v w p ((r⁻¹)^2) := by
  have hpos : 0 < r⁻¹*(coordDeriv v F p ⬝ᵥ coordDeriv v F p) :=
    mul_pos (inv_pos.mpr hr) (dot_self_pos hv)
  have he : orderedCrossing F v w p ((r⁻¹)^2) =
      (r⁻¹)^2*(coordDeriv v F p ⬝ᵥ coordDeriv v F p)*
        (coordDeriv w F p ⬝ᵥ coordDeriv w F p) := by
    simp only [orderedCrossing,hvv,hvw,normalize_positive_smul hn hpos,smul_dotProduct,
      smul_eq_mul,hn,mul_one,NormalFrame.gramDet]
    ring
  exact ⟨he,he.symm ▸ mul_pos (mul_pos (sq_pos_of_pos (inv_pos.mpr hr))
    (dot_self_pos hv)) (dot_self_pos hw)⟩

end ClosedSurfaceR4.VelocityFrame

end

end OAI
