import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedPrimarySeries

namespace OAI

/-! Multiplication of the frequency by any unit of the actual residue
ring. In particular, primary Fourier rows are invariant under lambda cubed. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaSymbolFourier_mul {c : Eisenstein} (hc : primary c)
    {r : Eisenstein} (hcr : IsCoprime c r) (h : Eisenstein) :
    cubicThetaSymbolFourier c (primary_ne_zero hc) (h*r)=
      star (cubicSymbol c r)*cubicThetaSymbolFourier c (primary_ne_zero hc) h := by
  let : Finite (Residues c) := finite_residues (primary_ne_zero hc)
  let : Fintype (Residues c) := Fintype.ofFinite _
  obtain ⟨u,hu⟩ := residue_isUnit_of_isCoprime hcr
  let ψ := residueFourierChar c (primary_ne_zero hc)
  let f (x : Residues c) : ℂ := cubicSymbol c (residueRepresentative c x)*
    ψ (Ideal.Quotient.mk (modulus c) h*x)
  let g (x : Residues c) : ℂ := cubicSymbol c (residueRepresentative c x)*
    ψ (Ideal.Quotient.mk (modulus c) (h*r)*x)
  have hw (x : Residues c) :
      cubicSymbol c (residueRepresentative c (u.mulLeft x))=
        cubicSymbol c r*cubicSymbol c (residueRepresentative c x) := by
    have he : Ideal.Quotient.mk (modulus c) (residueRepresentative c (u.mulLeft x))=
        Ideal.Quotient.mk (modulus c) (r*residueRepresentative c x) := by
      rw [residueRepresentative_spec,map_mul,residueRepresentative_spec]
      change (u:Residues c)*x=Ideal.Quotient.mk (modulus c) r*x
      rw [hu]
    rw [cubicSymbol_congr he,cubicSymbol_mul_upper hc]
  have hp (x : Residues c) : f (u.mulLeft x)=cubicSymbol c r*g x := by
    dsimp only [f,g]
    rw [hw]
    have he : Ideal.Quotient.mk (modulus c) h*(u.mulLeft x)=
        Ideal.Quotient.mk (modulus c) (h*r)*x := by
      change Ideal.Quotient.mk (modulus c) h*((u:Residues c)*x)=_
      rw [hu,map_mul]
      ring
    rw [he]
    ring
  have hs : (∑ x : Residues c, f x)=cubicSymbol c r*∑ x : Residues c, g x := by
    rw [← Equiv.sum_comp u.mulLeft f]
    simp_rw [hp]
    rw [Finset.mul_sum]
  have hi : star (cubicSymbol c r)*cubicSymbol c r=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',norm_cubicSymbol_of_isCoprime hc hcr]
    norm_num
  change (∑' x : Residues c, g x)=star (cubicSymbol c r)*∑' x : Residues c, f x
  rw [tsum_fintype,tsum_fintype,hs,← mul_assoc,hi,one_mul]

theorem cubicThetaSymbolFourier_lambda_cube {c : Eisenstein} (hc : primary c)
    (h : Eisenstein) :
    cubicThetaSymbolFourier c (primary_ne_zero hc) (lambdaE^3*h)=
      cubicThetaSymbolFourier c (primary_ne_zero hc) h := by
  rw [mul_comm (lambdaE^3) h,
    cubicThetaSymbolFourier_mul hc (primary_coprime_lambda hc).pow_right,
    cubicSymbol_pow_upper hc,cubicSymbol_cube_of_isCoprime hc lambdaE
      (primary_coprime_lambda hc),star_one,one_mul]

theorem cubicThetaPrimaryFourierSeries_lambda_cube (e : Eisensteinˣ) (n : ℕ)
    (s : ℂ) (h : Eisenstein) :
    cubicThetaPrimaryFourierSeries e n s (lambdaE^3*h)=
      cubicThetaPrimaryFourierSeries e n s h := by
  unfold cubicThetaPrimaryFourierSeries
  apply tsum_congr
  intro a
  unfold cubicThetaPrimaryFourierTerm
  rw [cubicThetaSymbolFourier_lambda_cube a.property]

end CubicFirstMoment

end

end OAI
