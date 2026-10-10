import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDilation

namespace OAI

/-! At the cubed prime scale the diagonal cubic twist cancels.
This is the actual integral correspondence needed for the cubed Hecke action. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCube_primary {p : Eisenstein} (hp : primaryPrime p) : primary (p^3) := by
  simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using primary_mul hp.1 (primary_mul hp.1 hp.1)

lemma cubicThetaPrimeCubeIwahori_coprime {p : Eisenstein}
    (g : cubicThetaPrimeIwahori (p^3)) : IsCoprime (g.val.val 0 0) p :=
  (cubicThetaPrincipalGroup_column_coprime g.val).of_isCoprime_of_dvd_right
    (dvd_trans (dvd_pow_self p (by norm_num : (3:ℕ)≠0)) g.property)

theorem cubicThetaPrimeCubeConjugate_kubota {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori (p^3)) :
    cubicThetaKubotaValue g.val=
      cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) g) := by
  have ha := (cubicThetaPrincipalGroup_diagonal_primary g.val).1
  rw [cubicThetaKubotaValue_eq_symbol,cubicThetaKubotaValue_eq_symbol]
  change cubicSymbol (g.val.val 0 0) (g.val.val 1 0)=
    cubicSymbol (g.val.val 0 0) (g.val.val 1 0/p^3)
  conv_lhs => rw [←cubicThetaPrimeIwahori_division (pow_ne_zero 3 hp.2.ne_zero) g]
  rw [cubicSymbol_mul_upper ha,cubicSymbol_pow_upper ha,
    cubicSymbol_cube_of_isCoprime ha p (cubicThetaPrimeCubeIwahori_coprime g),one_mul]

theorem cubicThetaEisenstein_primeCube_dilation {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori (p^3)) {z : ℂ × ℝ} (hz : 0<z.2) (s : ℂ) :
    cubicThetaEisenstein
      (cubicThetaMobius (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero))
        (cubicThetaMobius (cubicThetaPrincipalComplex g.val) z)) s=
      cubicThetaKubotaValue g.val*cubicThetaEisenstein
        (cubicThetaMobius (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)) z) s := by
  rw [cubicThetaMobius_comp,
    cubicThetaPrimeDilation_intertwines (cubicThetaPrimeCube_primary hp) g,
    ←cubicThetaMobius_comp,cubicThetaEisenstein_automorphy
      (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) g)
      (cubicThetaMobius_height_pos _ hz),←cubicThetaPrimeCubeConjugate_kubota hp g]
  · exact hz
  · exact hz

end CubicFirstMoment

end

end OAI
