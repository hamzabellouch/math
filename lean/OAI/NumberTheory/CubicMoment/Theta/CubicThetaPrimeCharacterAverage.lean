import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDiagonal

namespace OAI

/-! Exact cancellation of the prime-dilated Eisenstein family under the
finite diagonal quotient. Representatives are actual arithmetic matrices;
the multiplier is retained throughout the averaging. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaPrimeDiagonalSection {p : Eisenstein} (hp : primaryPrime p)
    (u : (Residues p)ˣ) : cubicThetaPrimeIwahori p :=
  Classical.choose (cubicThetaPrimeIwahoriDiagonal_surjective hp u)

@[simp] lemma cubicThetaPrimeDiagonalSection_diagonal {p : Eisenstein}
    (hp : primaryPrime p) (u : (Residues p)ˣ) :
    cubicThetaPrimeIwahoriDiagonal hp (cubicThetaPrimeDiagonalSection hp u)=u :=
  Classical.choose_spec (cubicThetaPrimeIwahoriDiagonal_surjective hp u)

lemma cubicThetaPrimeDiagonalSection_character {p : Eisenstein}
    (hp : primaryPrime p) (u : (Residues p)ˣ) :
    cubicThetaPrimeIwahoriCharacter p hp (cubicThetaPrimeDiagonalSection hp u)=
      cubicResidueChar p hp u := by
  rw [cubicThetaPrimeIwahoriCharacter_diagonal,cubicThetaPrimeDiagonalSection_diagonal]

lemma cubicThetaPrimeCharacter_sum_units {p : Eisenstein} (hp : primaryPrime p)
    [Fintype (Residues p)ˣ] :
    (∑ u : (Residues p)ˣ, cubicResidueChar p hp u)=0 := by
  obtain ⟨b,hb⟩ := MulChar.ne_one_iff.mp (cubicResidueChar_ne_one hp)
  apply eq_zero_of_mul_eq_self_left hb
  have he := (Equiv.mulLeft b).bijective.sum_comp
    (fun u : (Residues p)ˣ => cubicResidueChar p hp u)
  change (∑ u : (Residues p)ˣ, cubicResidueChar p hp ((b*u : (Residues p)ˣ) : Residues p))=
    (∑ u : (Residues p)ˣ, cubicResidueChar p hp u) at he
  simpa only [Finset.mul_sum,Units.val_mul,map_mul] using he

theorem cubicThetaEisenstein_prime_character_average {p : Eisenstein}
    (hp : primaryPrime p) {z : ℂ × ℝ} (hz : 0<z.2) (s : ℂ) :
    (∑' u : (Residues p)ˣ,
      star (cubicThetaKubotaValue (cubicThetaPrimeDiagonalSection hp u).val)*
        cubicThetaEisenstein
          (cubicThetaMobius (cubicThetaPrimeDilation hp.2.ne_zero)
            (cubicThetaMobius
              (cubicThetaPrincipalComplex (cubicThetaPrimeDiagonalSection hp u).val) z)) s)=0 := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p)ˣ := Fintype.ofFinite _
  rw [tsum_fintype]
  have hterm (u : (Residues p)ˣ) :
      star (cubicThetaKubotaValue (cubicThetaPrimeDiagonalSection hp u).val)*
        cubicThetaEisenstein
          (cubicThetaMobius (cubicThetaPrimeDilation hp.2.ne_zero)
            (cubicThetaMobius
              (cubicThetaPrincipalComplex (cubicThetaPrimeDiagonalSection hp u).val) z)) s=
      star (cubicResidueChar p hp u)*
        cubicThetaEisenstein (cubicThetaMobius (cubicThetaPrimeDilation hp.2.ne_zero) z) s := by
    rw [cubicThetaEisenstein_prime_dilation_twist hp _ hz,
      cubicThetaPrimeDiagonalSection_character]
    have hk : star (cubicThetaKubotaValue (cubicThetaPrimeDiagonalSection hp u).val)*
        cubicThetaKubotaValue (cubicThetaPrimeDiagonalSection hp u).val=1 := by
      rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
      norm_num
    calc
      _ = (star (cubicThetaKubotaValue (cubicThetaPrimeDiagonalSection hp u).val)*
          cubicThetaKubotaValue (cubicThetaPrimeDiagonalSection hp u).val)*
          (star (cubicResidueChar p hp u)*
          cubicThetaEisenstein (cubicThetaMobius (cubicThetaPrimeDilation hp.2.ne_zero) z) s) := by ring
      _ = _ := by rw [hk,one_mul]
  simp_rw [hterm]
  have hs : (∑ u : (Residues p)ˣ, star (cubicResidueChar p hp u))=0 := by
    simpa only [map_sum,starRingEnd_apply,map_zero] using
      congrArg (starRingEnd ℂ) (cubicThetaPrimeCharacter_sum_units hp)
  rw [←Finset.sum_mul,hs,zero_mul]

end CubicFirstMoment

end

end OAI
