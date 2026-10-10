import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmetic

namespace OAI

/-! Identification of the normalized Gauss factor in the literal cubic
theta coefficient formula with its finite additive-frequency sum. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaFiniteGauss (c α : Eisenstein) : ℂ :=
  (Real.sqrt (norm c):ℂ)⁻¹*∑' x : Residues c,
    cubicSymbol c (residueRepresentative c x)*additivePhase c (α*residueRepresentative c x)

/-- Multiplication by the invertible additive frequency permutes the
residue ring; no primitive character or analytic input is needed. -/
theorem cubicThetaFiniteGauss_eq {c α : Eisenstein} (hc : primary c)
    (hα : IsCoprime c α) : cubicThetaFiniteGauss c α = cubicThetaTwistedGauss c α := by
  let : Finite (Residues c) := finite_residues (primary_ne_zero hc)
  let : Fintype (Residues c) := Fintype.ofFinite _
  obtain ⟨u,hu⟩ := residue_isUnit_of_isCoprime hα
  let f (v : Residues c) : ℂ :=
    cubicSymbol c (residueRepresentative c v)*additivePhase c (residueRepresentative c v)
  let g (v : Residues c) : ℂ :=
    cubicSymbol c (residueRepresentative c v)*additivePhase c (α*residueRepresentative c v)
  have hrep (v : Residues c) :
      Ideal.Quotient.mk (modulus c) (residueRepresentative c (u.mulLeft v)) =
        Ideal.Quotient.mk (modulus c) (α*residueRepresentative c v) := by
    rw [residueRepresentative_spec,map_mul,residueRepresentative_spec]
    change (u:Residues c)*v = Ideal.Quotient.mk (modulus c) α*v
    rw [hu]
  have hterm (v : Residues c) : f (u.mulLeft v) = cubicSymbol c α*g v := by
    dsimp only [f,g]
    rw [cubicSymbol_congr (hrep v),additivePhase_congr (primary_ne_zero hc) (hrep v),
      cubicSymbol_mul_upper hc]
    ring
  have hsum : (∑ v : Residues c, f v) = cubicSymbol c α*∑ v : Residues c, g v := by
    rw [←Equiv.sum_comp u.mulLeft f]
    simp_rw [hterm]
    rw [Finset.mul_sum]
  have hnorm : star (cubicSymbol c α)*cubicSymbol c α = 1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',norm_cubicSymbol_of_isCoprime hc hα]
    norm_num
  have hg : (∑ v : Residues c, g v) = star (cubicSymbol c α)*∑ v : Residues c, f v := by
    rw [hsum,←mul_assoc,hnorm,one_mul]
  rw [cubicThetaFiniteGauss,tsum_fintype,cubicThetaTwistedGauss,gauss_eq_finite_sum]
  change (Real.sqrt (norm c):ℂ)⁻¹*(∑ v : Residues c, g v) =
    star (cubicSymbol c α)*((Real.sqrt (norm c):ℂ)⁻¹*∑ v : Residues c, f v)
  rw [hg]
  ring

end CubicFirstMoment

end

end OAI
