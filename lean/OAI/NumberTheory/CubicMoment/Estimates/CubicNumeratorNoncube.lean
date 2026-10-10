import OAI.NumberTheory.CubicMoment.Estimates.RamifiedCubicNonprincipal

namespace OAI

/-! Every noncube numerator defines a nonprincipal cubic character.
The proof keeps ramification and cube-factor deletions explicit. -/
noncomputable section
namespace CubicFirstMoment

private lemma nonprincipal_transport (hpub : CubicSupplementaryPeriodicity)
    {v w : Eisenstein} (hv : v ≠ 0) (hw : w ≠ 0) (h : v=w) :
    (cubicNumeratorChar hpub v hv ≠ 1) ↔ (cubicNumeratorChar hpub w hw ≠ 1) := by
  subst w
  rfl

lemma mixed_ramified_cubic_nonprincipal (hpub : CubicSupplementaryPeriodicity)
    {r s t : Eisenstein} (hr : r ≠ 0) (hs : primary s) (ht : primary t)
    (hss : Squarefree s) (hst : Squarefree t) (hcop : IsCoprime s t)
    (hnu : ¬IsUnit (s*t)) (hrst : IsCoprime (s*t) r) :
    cubicNumeratorChar hpub (r*s*t^2)
      (mul_ne_zero (mul_ne_zero hr (primary_ne_zero hs)) (pow_ne_zero _ (primary_ne_zero ht))) ≠ 1 := by
  obtain ⟨y,hy,hyc,hyne⟩ := mixedCubic_nonprincipal hs ht hss hst hcop hnu
  have hst9 : IsCoprime (s*t) (9:Eisenstein) := by
    convert (primary_coprime_three (primary_mul hs ht)).pow_right (n := 2) using 1
    norm_num
  obtain ⟨x,hxy,hxone⟩ := residue_crt_one (hst9.mul_right hrst) y
  have hx : primary x := (show (3:Eisenstein) ∣ 9*r from ⟨3*r,by ring⟩).trans hxone
  have hxst : IsCoprime (s*t) x := isCoprime_of_residue_congr hxy hyc
  have hx9r := isCoprime_of_dvd_sub_one hxone
  have hx9 := hx9r.of_mul_left_left
  have hxr := hx9r.of_mul_left_right
  have hxv : IsCoprime (r*s*t^2) x :=
    (hxr.mul_left hxst.of_mul_left_left).mul_left (hxst.of_mul_left_right.pow_left (m := 2))
  have hxrval : cubicSymbol x r=1 :=
    (hpub r hr x 1 hx primary_one hxone).trans (cubicSymbol_one_lower r)
  have hmix : mixedCubic s t x=mixedCubic s t y := by
    unfold mixedCubic
    rw [cubicSymbol_congr (residue_eq_of_dvd_sub ((dvd_mul_right s t).trans hxy)),
      cubicSymbol_congr (residue_eq_of_dvd_sub ((dvd_mul_left t s).trans hxy))]
  apply (cubicNumeratorChar_ne_one_iff hpub _ _).mpr
  refine ⟨x,hx,hx9.mul_left hxv,?_⟩
  rw [cubicSymbol_mul_upper hx,cubicSymbol_mul_upper hx,hxrval,one_mul,
    cubicSymbol_pow_upper hx,cubicSymbol_sq_eq_star hx,
    cubic_reciprocity hx hs,cubic_reciprocity hx ht]
  change mixedCubic s t x ≠ 1
  rwa [hmix]

/-- Nonprincipality for the full numerator, with no squarefreeness,
primarity, unit, or ramification restrictions. -/
theorem cubicNumeratorChar_noncube (hpub : CubicSupplementaryPeriodicity)
    {v : Eisenstein} (hv : v ≠ 0) (hn : ¬∃ j : Eisenstein, j^3=v) :
    cubicNumeratorChar hpub v hv ≠ 1 := by
  obtain ⟨u,k,a,ha,hva⟩ := unit_ramified_primary_decomposition hv
  obtain ⟨s,t,c,hs,ht,hc,hss,hst,hcop,haeq⟩ := primary_cube_decomposition ha
  let r : Eisenstein := (u:Eisenstein)*lambdaE^k
  have hr : r ≠ 0 := mul_ne_zero u.ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero)
  have he : v=(r*s*t^2)*c^3 := by rw [hva,haeq]; dsimp [r]; ring
  have hbase : r*s*t^2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hr (primary_ne_zero hs)) (pow_ne_zero _ (primary_ne_zero ht))
  have hbasechar : cubicNumeratorChar hpub (r*s*t^2) hbase ≠ 1 := by
    by_cases hunit : IsUnit (s*t)
    · have hs1 := primary_unit_eq_one (isUnit_of_mul_isUnit_left hunit) hs
      have ht1 := primary_unit_eq_one (isUnit_of_mul_isUnit_right hunit) ht
      have hnr : ¬∃ j : Eisenstein, j^3=r := by
        rintro ⟨j,hj⟩
        apply hn
        refine ⟨j*c,?_⟩
        rw [mul_pow,hj,he,hs1,ht1,one_pow,mul_one,mul_one]
      have hunitbase : r*s*t^2=r := by rw [hs1,ht1]; ring
      exact (nonprincipal_transport hpub hbase hr hunitbase).mpr
        (unit_ramified_cubic_nonprincipal hpub u.isUnit k hnr)
    · have hru : IsCoprime (s*t) (u:Eisenstein) :=
        (isCoprime_zero_left.mpr u.isUnit).of_isCoprime_of_dvd_left (dvd_zero (s*t))
      have hrst : IsCoprime (s*t) r :=
        hru.mul_right ((primary_coprime_lambda (primary_mul hs ht)).pow_right (n := k))
      exact mixed_ramified_cubic_nonprincipal hpub hr hs ht hss hst hcop hunit hrst
  have hout := cubicNumeratorChar_mul_cube_ne_one hpub hbase (primary_ne_zero hc) hbasechar
  exact (nonprincipal_transport hpub hv _ he).mpr hout

theorem cubicNumeratorChar_eq_one_iff_cube (hpub : CubicSupplementaryPeriodicity)
    {v : Eisenstein} (hv : v ≠ 0) :
    cubicNumeratorChar hpub v hv=1 ↔ ∃ j : Eisenstein, j^3=v := by
  constructor
  · intro he
    by_contra hn
    exact cubicNumeratorChar_noncube hpub hv hn he
  · exact cubicNumeratorChar_of_cube hpub v hv

end CubicFirstMoment

end

end OAI
