import OAI.NumberTheory.DirichletL.Detector.PairPhase

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates CompletedGauss CubicEisenstein
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

lemma reciprocitySign_star (a b : O) : star (reciprocitySign a b)=reciprocitySign a b := by
  simp only [reciprocitySign, star_intCast]

theorem completed_cubic_pair_cancel (p q : O) (hp : Prime p) (hq : Prime q)
    (hprimaryP : goodLambda^2∣p-1) (hprimaryQ : goodLambda^2∣q-1)
    (hsP : Supported (Ideal.span {p})) (hsQ : Supported (Ideal.span {q}))
    (hcop : IsCoprime (Ideal.span {p} : Ideal O) (Ideal.span {q}))
    (e f l k : ℕ) :
    sexticPair p q ^ ((e+3*l)*(f+3*k)) * sexticPair p q ^ (2*e*f) *
      star (reciprocitySign (p^(e+3*l)) (q^(f+3*k))) = 1 := by
  have hpodd := supported_residue_odd p hsP
  have hqodd := supported_residue_odd q hsQ
  have h3 := sexticPair_cube p q hp hq hprimaryP hprimaryQ hsP hsQ hcop
  have h2 := reciprocitySign_sq p q hpodd hqodd
  rw [reciprocitySign_star, reciprocitySign_pow_left p _ (odd_residue_pow q hqodd _) _,
    reciprocitySign_pow_right p q hpodd, ← pow_mul, ← pow_add]
  have hexp : (e+3*l)*(f+3*k)+2*e*f = 3*(e*f+e*k+f*l+3*l*k) := by ring
  rw [hexp, pow_mul, h3, ← pow_add]
  have hsum : e*f+e*k+f*l+3*l*k+(f+3*k)*(e+3*l) =
      2*(e*f+2*e*k+2*f*l+6*l*k) := by ring
  rw [hsum, pow_mul, h2, one_pow]

lemma sexticPair_mul_left (a b c : O) :
    sexticPair (a*b) c = sexticPair a c * sexticPair b c := by
  simp only [sexticPair, ← Ideal.span_singleton_mul_span_singleton, map_mul,
    idealRowHom_argument_mul]
  ring

lemma sexticPair_mul_right (a b c : O) :
    sexticPair a (b*c) = sexticPair a b * sexticPair a c := by
  simp only [sexticPair, ← Ideal.span_singleton_mul_span_singleton, map_mul,
    idealRowHom_argument_mul]
  ring

lemma sexticPair_cube_left (a b : O) : sexticPair (a^3) b=sexticPair a b^3 := by
  rw [show a^3=a*a*a by ring, sexticPair_mul_left, sexticPair_mul_left]
  ring

lemma sexticPair_cube_right (a b : O) : sexticPair a (b^3)=sexticPair a b^3 := by
  rw [show b^3=b*b*b by ring, sexticPair_mul_right, sexticPair_mul_right]
  ring

theorem sexticPair_cube_supported (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpa : goodLambda^2∣a-1) (hpb : goodLambda^2∣b-1) (hcop : IsCoprime a b) :
    sexticPair a b^3 = reciprocitySign a b := by
  have hr : idealRowHom b (Ideal.span {a}) =
      reciprocitySign a b * idealRowHom a (Ideal.span {b}) :=
    idealRowHom_primary_reciprocity a b hpa hpb ha hb
  have hc : IsCoprime (Ideal.span {b}:Ideal O) (Ideal.span {a}) := by
    exact (Ideal.isCoprime_span_singleton_iff b a).mpr hcop.symm
  have h6 := idealRowHom_sixth_mask a (Ideal.span {b}) hb
  rw [idealRowHom_argument_pow _ _ _ hb, ite_eq_left hc] at h6
  have h2 := reciprocitySign_sq a b (supported_residue_odd a ha) (supported_residue_odd b hb)
  calc
    _ = reciprocitySign a b^3 * idealRowHom a (Ideal.span {b})^6 := by
      unfold sexticPair
      rw [hr]
      ring
    _ = _ := by rw [h6,mul_one,pow_succ,h2,one_mul]

theorem completed_cubic_cross_cancel (c n d m : O)
    (hc : Supported (Ideal.span {c})) (hn : Supported (Ideal.span {n}))
    (hd : Supported (Ideal.span {d})) (hm : Supported (Ideal.span {m}))
    (hpc : goodLambda^2∣c-1) (hpn : goodLambda^2∣n-1)
    (hpd : goodLambda^2∣d-1) (hpm : goodLambda^2∣m-1)
    (hcd : IsCoprime c d) (hcm : IsCoprime c m)
    (hnd : IsCoprime n d) (hnm : IsCoprime n m) :
    sexticPair (c*n^3) (d*m^3) * sexticPair c d^2 *
      star (reciprocitySign (c*n^3) (d*m^3)) = 1 := by
  have hcd3 := sexticPair_cube_supported c d hc hd hpc hpd hcd
  have hcm3 := sexticPair_cube_supported c m hc hm hpc hpm hcm
  have hnd3 := sexticPair_cube_supported n d hn hd hpn hpd hnd
  have hnm3 := sexticPair_cube_supported n m hn hm hpn hpm hnm
  have hRnm := reciprocitySign_sq n m (supported_residue_odd n hn) (supported_residue_odd m hm)
  have he : sexticPair (c*n^3) (d*m^3)*sexticPair c d^2 =
      reciprocitySign (c*n^3) (d*m^3) := by
    calc
      _ = sexticPair c d^3 * sexticPair c m^3 * sexticPair n d^3 *
          (sexticPair n m^3)^3 := by
        rw [sexticPair_mul_left, sexticPair_mul_right, sexticPair_mul_right,
          sexticPair_cube_left, sexticPair_cube_left, sexticPair_cube_right,
          sexticPair_cube_right]
        ring
      _ = reciprocitySign c d * reciprocitySign c m * reciprocitySign n d * reciprocitySign n m := by
        rw [hcd3,hcm3,hnd3,hnm3,pow_succ,hRnm,one_mul]
      _ = _ := by
        rw [reciprocitySign_mul_left, reciprocitySign_mul_right, reciprocitySign_mul_right,
          reciprocitySign_cube_right c m (supported_residue_odd c hc) (supported_residue_odd m hm),
          reciprocitySign_symm (n^3) d,
          reciprocitySign_cube_right d n (supported_residue_odd d hd) (supported_residue_odd n hn),
          reciprocitySign_symm d n,
          reciprocitySign_cube_right (n^3) m (odd_residue_pow n (supported_residue_odd n hn) 3)
            (supported_residue_odd m hm), reciprocitySign_symm (n^3) m,
          reciprocitySign_cube_right m n (supported_residue_odd m hm) (supported_residue_odd n hn),
          reciprocitySign_symm m n]
        ring
  rw [he,reciprocitySign_star,←pow_two]
  exact reciprocitySign_sq _ _
    (by simpa only [ActualEisensteinCoordinates.residue_mul] using
      (EisensteinEPrimaryPhase.odd_mul _ _ (supported_residue_odd c hc)
        (odd_residue_pow n (supported_residue_odd n hn) 3)))
    (by simpa only [ActualEisensteinCoordinates.residue_mul] using
      (EisensteinEPrimaryPhase.odd_mul _ _ (supported_residue_odd d hd)
        (odd_residue_pow m (supported_residue_odd m hm) 3)))

end SevenEighths.ProbePhase
end

end OAI
