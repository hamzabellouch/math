import OAI.NumberTheory.DirichletL.PrimeRows.Selected

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

theorem continuedMarkedLocal_unramified (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) (x w z : ℂ)
    (hV : ‖coordV P.val.absNorm z‖<1)
    (hR : ‖coordR P.val.absNorm (actualAPhase η (primaryGenerator P.val)) x z‖<1) :
    continuedMarkedLocal η u P hs x w z=
      unramifiedMarked P.val.absNorm (actualAPhase η (primaryGenerator P.val))
        (idealCoeff η P.val) (idealRowHom u.val P.val) x w z := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hnot : ¬p∣u.val := by
    intro hd
    apply hn
    rw [Ideal.dvd_iff_le,←hspan,Ideal.span_singleton_le_span_singleton]
    exact hd
  have hj := multiplicity_eq_zero_of_not_dvd hnot
  have hb : unitPart u p hp=u.val := by
    have he := (unitPart_spec u p hp).1
    rw [hj,pow_zero,one_mul] at he
    exact he.symm
  have hu : IsCoprime u.val p := by rw [←hb]; exact unitPart_coprime u p hp
  have hρ := actualSextic_unit_six p u.val hg.1 hg.2 hu
  have hQ0 : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) :=
    HeckeDyadic.norm_pos ⟨Ideal.span {p},Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero⟩
  have hr := evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}):ℝ) hQ0 (actualACube η p) x z
  simp only [Complex.ofReal_natCast] at hr
  have hR' : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) (actualACube η p)
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1 := by
    rw [hr,actualACube_sq,hspan]
    exact hR
  have hv' : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1 := by rw [hspan];exact hV
  have hh := rowClosedMarked_unramified p hp hg.1 hg.2 (targetMonoid η p) (actualACube η p)
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))
    (coordV (Ideal.absNorm (Ideal.span {p})) z) _ hρ hv' hR'
  have hk := coordK_eq_geometric (Ideal.absNorm (Ideal.span {p}):ℝ) hQ0 (targetMonoid η p) x w
  simp only [Complex.ofReal_natCast] at hk
  have hi : (actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ u.val))⁻¹=
      star (actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ u.val)) :=
    Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hρ (by decide))
  have heta : idealCoeff η P.val=targetMonoid η p :=
    (targetMonoid_primaryGenerator η P.val hs).symm
  have hphase : idealRowHom u.val P.val=
      actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ u.val) := by
    conv_lhs => rw [←hspan]
    exact idealRowHom_prime u.val (Ideal.span {p}) hg.1
  simp only [hspan] at hh hr hk
  unfold continuedMarkedLocal
  change rowClosedMarked p hp hg.1 (targetMonoid η p) (actualACube η p)
    ((P.val.absNorm:ℂ)^(-x)) ((P.val.absNorm:ℂ)^(-w)) (coordV P.val.absNorm z)
    (actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ (unitPart u p hp))) (multiplicity p u.val)=_
  rw [hj,hb,hh,hr,←hk,actualACube_sq,heta,hphase]
  simp only [unramifiedMarked,coordD,coordW,div_eq_mul_inv,hi,Complex.ofReal_natCast]
  congr 1; ring

theorem continuedCompensatedLocal_unramified (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) (x w z : ℂ)
    (hV : ‖coordV P.val.absNorm z‖<1)
    (hR : ‖coordR P.val.absNorm (actualAPhase η (primaryGenerator P.val)) x z‖<1) :
    continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))=
      unramifiedSelected P.val.absNorm (actualAPhase η (primaryGenerator P.val))
        (idealCoeff η P.val) (idealRowHom u.val P.val) x w z := by
  rw [continuedCompensatedLocal,continuedMarkedLocal_unramified η u P hs hn x w z hV hR]
  rfl

end SevenEighths.ProbeHighRowFamily

end

end OAI
