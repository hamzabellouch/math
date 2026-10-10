import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryFourierTwist
import OAI.NumberTheory.CubicMoment.Estimates.CubicNumeratorNoncube

namespace OAI

/-! Cube support and exact residue-unit count for the primary finite
character sum occurring at the inverted cusp. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaSymbolFourier_zero_noncube {c : Eisenstein} (hc : primary c)
    (hcb : ¬∃ j : Eisenstein, j^3=c) :
    cubicThetaSymbolFourier c (primary_ne_zero hc) 0=0 := by
  obtain ⟨u,hu,hcu,hchi⟩ :=
    (cubicNumeratorChar_ne_one_iff cubicSupplementaryPeriodicity_proved c
      (primary_ne_zero hc)).mp
      (cubicNumeratorChar_noncube cubicSupplementaryPeriodicity_proved (primary_ne_zero hc) hcb)
  have hχ : cubicSymbol c u≠1 := by rwa [cubic_reciprocity hc hu]
  have hs : star (cubicSymbol c u)≠1 := by
    intro he
    apply hχ
    have ht := congrArg star he
    simpa only [star_star,star_one] using ht
  have he := cubicThetaSymbolFourier_mul hc hcu.of_mul_left_right 0
  simp only [zero_mul] at he
  exact eq_zero_of_mul_eq_self_left hs he.symm

theorem cubicThetaSymbol_primary_cube {c : Eisenstein} (hc : primary c)
    (hcb : ∃ j : Eisenstein, j^3=c) (x : Eisenstein) :
    cubicSymbol c x=if IsCoprime c x then 1 else 0 := by
  by_cases hx : IsCoprime c x
  · rw [ite_eq_left hx]
    obtain ⟨u,hux,hu⟩ := residue_crt_one (primary_coprime_three hc) x
    have hcu : IsCoprime c u := isCoprime_of_residue_congr hux hx
    rw [← cubicSymbol_congr (residue_eq_of_dvd_sub hux),cubic_reciprocity hc hu]
    obtain ⟨j,hj⟩ := hcb
    rw [← hj,cubicSymbol_pow_upper hu]
    apply cubicSymbol_cube_of_isCoprime hu j
    rw [← hj] at hcu
    exact hcu.symm.of_isCoprime_of_dvd_right (dvd_pow_self j (by norm_num : (3:ℕ)≠0))
  · rw [ite_eq_right hx,cubicSymbol_eq_zero_of_not_isCoprime hc hx]

theorem cubicThetaSymbolFourier_zero_cube {c : Eisenstein} (hc : primary c)
    (hcb : ∃ j : Eisenstein, j^3=c) :
    cubicThetaSymbolFourier c (primary_ne_zero hc) 0=(Nat.card (Residues c)ˣ:ℂ) := by
  let : Finite (Residues c) := finite_residues (primary_ne_zero hc)
  let : Fintype (Residues c) := Fintype.ofFinite _
  let e : (Residues c)ˣ ≃ {x : Residues c // IsUnit x} := {
    toFun := fun u => ⟨u,u.isUnit⟩
    invFun := fun x => x.property.unit
    left_inv := fun u => Units.ext (IsUnit.unit_spec _)
    right_inv := fun x => Subtype.ext x.property.unit_spec }
  have hu (x : Residues c) : IsCoprime c (residueRepresentative c x) ↔ IsUnit x := by
    constructor
    · intro hx
      have ht := residue_isUnit_of_isCoprime hx
      rwa [residueRepresentative_spec] at ht
    · intro hx
      apply isCoprime_of_residue_isUnit
      rwa [residueRepresentative_spec]
  unfold cubicThetaSymbolFourier
  simp_rw [cubicThetaSymbol_primary_cube hc hcb,hu]
  simp only [map_zero,zero_mul,AddChar.map_zero_eq_one,mul_one,tsum_fintype]
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype]
  simp

def cubicThetaInvertedConstantGauss (c : Eisenstein) : ℂ :=
  ∑' x : Residues c, cubicSymbol c (3*residueRepresentative c x)

theorem cubicThetaInvertedConstantGauss_eq {c : Eisenstein} (hc : primary c) :
    cubicThetaInvertedConstantGauss c=
      if ∃ j : Eisenstein, j^3=c then (Nat.card (Residues c)ˣ:ℂ) else 0 := by
  have he : cubicThetaInvertedConstantGauss c=
      cubicSymbol c 3*cubicThetaSymbolFourier c (primary_ne_zero hc) 0 := by
    unfold cubicThetaInvertedConstantGauss cubicThetaSymbolFourier
    simp_rw [cubicSymbol_mul_upper hc]
    simp only [map_zero,zero_mul,AddChar.map_zero_eq_one,mul_one,tsum_mul_left]
  rw [he]
  split_ifs with hcb
  · rw [cubicThetaSymbolFourier_zero_cube hc hcb,cubicThetaSymbol_primary_cube hc hcb,
      ite_eq_left (primary_coprime_three hc),one_mul]
  · rw [cubicThetaSymbolFourier_zero_noncube hc hcb,mul_zero]

end CubicFirstMoment

end

end OAI
