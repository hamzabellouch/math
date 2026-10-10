import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeKloostermanInflation

namespace OAI

/-! Removing a common cubic prime factor from the actual local Kloosterman
kernel. The quotient map retains the inverse term and the zero extension. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaPrimePowerReduction_cube_inverse {p : Eisenstein}
    (_hp : primaryPrime p) (n : ℕ) (x : Residues (p^(n+4))) :
    residueReduction (pow_dvd_pow p (by omega : n+1 ≤ n+4)) (Ring.inverse x)=
      Ring.inverse (residueReduction (pow_dvd_pow p (by omega : n+1 ≤ n+4)) x) := by
  have hi : IsUnit x ↔ IsUnit
      (residueReduction (pow_dvd_pow p (by omega : n+1 ≤ n+4)) x) := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [residueReduction_mk,cubicTheta_residue_mk_isUnit_iff,
      cubicTheta_residue_mk_isUnit_iff,IsCoprime.pow_left_iff (by omega : 0<n+4),
      IsCoprime.pow_left_iff (by omega : 0<n+1)]
  by_cases hx : IsUnit x
  · exact cubicThetaResidueHom_inverse _ hx
  · rw [Ring.inverse_non_unit _ hx,Ring.inverse_non_unit _ (fun hy => hx (hi.mpr hy)),map_zero]

lemma cubicThetaPrimePowerWeight_cube {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (x : Residues (p^(n+4))) :
    cubicSymbol (p^(n+4)) (residueRepresentative (p^(n+4)) x)=
      cubicSymbol (p^(n+1)) (residueRepresentative (p^(n+1))
        (residueReduction (pow_dvd_pow p (by omega : n+1 ≤ n+4)) x)) := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  have hr : residueReduction (dvd_pow_self p (by omega : n+4≠0)) x=
      residueReduction (dvd_pow_self p (by omega : n+1≠0))
        (residueReduction (pow_dvd_pow p (by omega : n+1 ≤ n+4)) x) := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [residueReduction_mk]
  rw [cubicThetaPrimePowerWeight_inflation hp (n+3),
    cubicThetaPrimePowerWeight_inflation hp n,hr]
  have he : (cubicResidueChar p hp)^((n+1)+3)=(cubicResidueChar p hp)^(n+1) := by
    rw [pow_add,cubicResidueChar_cube hp,mul_one]
  have he' := congrArg (fun χ : MulChar (Residues p) ℂ => χ
    (residueReduction (dvd_pow_self p (by omega : n+1≠0))
      (residueReduction (pow_dvd_pow p (by omega : n+1 ≤ n+4)) x))) he
  simpa only [MulChar.pow_apply' _ (by omega : (n+1)+3≠0),
    MulChar.pow_apply' _ (by omega : n+1≠0),show (n+3)+1=(n+1)+3 by omega] using he'

theorem cubicThetaSymbolKloosterman_cubeInflation {p : Eisenstein}
    (hp : primaryPrime p) (n : ℕ) (h k : Eisenstein) :
    cubicThetaSymbolKloosterman (p^(n+4)) (pow_ne_zero _ hp.2.ne_zero)
      (Ideal.Quotient.mk (modulus (p^(n+4))) (p^3*h))
      (Ideal.Quotient.mk (modulus (p^(n+4))) (p^3*k))=
      (norm (p^3):ℂ)*cubicThetaSymbolKloosterman (p^(n+1))
        (pow_ne_zero _ hp.2.ne_zero) (Ideal.Quotient.mk (modulus (p^(n+1))) h)
          (Ideal.Quotient.mk (modulus (p^(n+1))) k) := by
  have hf : p^(n+4)=p^(n+1)*p^3 := by rw [←pow_add]
  let f : Residues (p^(n+1)) → ℂ := fun y =>
    cubicSymbol (p^(n+1)) (residueRepresentative (p^(n+1)) y)*
      residueFourierChar (p^(n+1)) (pow_ne_zero _ hp.2.ne_zero)
        (Ideal.Quotient.mk (modulus (p^(n+1))) h*y+
          Ideal.Quotient.mk (modulus (p^(n+1))) k*Ring.inverse y)
  have he := residue_sum_inflation (pow_ne_zero (n+4) hp.2.ne_zero)
    (pow_ne_zero (n+1) hp.2.ne_zero) (pow_dvd_pow p (by omega : n+1 ≤ n+4)) f
  have hn : norm (p^(n+4))/norm (p^(n+1))=norm (p^3) := by
    rw [hf,norm_mul_eq,mul_div_cancel_left₀ _
      (norm_pos_of_ne_zero (pow_ne_zero _ hp.2.ne_zero)).ne']
  rw [hn] at he
  refine Eq.trans ?_ he
  unfold cubicThetaSymbolKloosterman
  apply tsum_congr
  intro x
  rw [AddChar.map_add_eq_mul,cubicThetaPrimePowerWeight_cube hp,
    cubicThetaResidueFourier_factor (pow_ne_zero _ hp.2.ne_zero)
      (pow_ne_zero _ hp.2.ne_zero) (pow_ne_zero 3 hp.2.ne_zero) hf
      (pow_dvd_pow p (by omega : n+1 ≤ n+4)),
    cubicThetaResidueFourier_factor (pow_ne_zero _ hp.2.ne_zero)
      (pow_ne_zero _ hp.2.ne_zero) (pow_ne_zero 3 hp.2.ne_zero) hf
      (pow_dvd_pow p (by omega : n+1 ≤ n+4)),
    cubicThetaPrimePowerReduction_cube_inverse hp]
  dsimp only [f]
  rw [AddChar.map_add_eq_mul]

theorem cubicThetaSymbolKloosterman_cubeInflation_residue {p : Eisenstein}
    (hp : primaryPrime p) (n : ℕ) (h k : Residues (p^(n+4))) :
    cubicThetaSymbolKloosterman (p^(n+4)) (pow_ne_zero _ hp.2.ne_zero)
      (Ideal.Quotient.mk (modulus (p^(n+4))) (p^3)*h)
      (Ideal.Quotient.mk (modulus (p^(n+4))) (p^3)*k)=
      (norm (p^3):ℂ)*cubicThetaSymbolKloosterman (p^(n+1))
        (pow_ne_zero _ hp.2.ne_zero)
        (residueReduction (pow_dvd_pow p (by omega : n+1 ≤ n+4)) h)
        (residueReduction (pow_dvd_pow p (by omega : n+1 ≤ n+4)) k) := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective h
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective k
  simpa only [map_mul,residueReduction_mk] using
    cubicThetaSymbolKloosterman_cubeInflation hp n a b

end CubicFirstMoment

end

end OAI
