import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedResidueSystem

namespace OAI

/-! Exactly two unit classes can contribute to the middle ramified row
above a frequency congruent to one modulo lambda. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaOmegaUnit : Eisensteinˣ :=
  Units.mkOfMulEqOne omegaE (omegaE^2) (by simpa only [←pow_succ'] using omegaE_cube)

lemma cubicThetaLambda_dvd_omega_pow_sub_one (k : ℕ) : lambdaE∣omegaE^k-1 := by
  have h1 : lambdaE∣omegaE-1 := by
    refine ⟨1+omegaE,?_⟩
    dsimp only [lambdaE]
    linear_combination -2*omegaE_quadratic
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ,show omegaE^k*omegaE-1=omegaE^k*(omegaE-1)+(omegaE^k-1) by ring]
    exact dvd_add (dvd_mul_of_dvd_right h1 _) ih

lemma cubicThetaThree_dvd_lambda_mul (h : Eisenstein) :
    (3:Eisenstein)∣lambdaE*h ↔ lambdaE∣h := by
  rw [show (3:Eisenstein)=-(lambdaE*lambdaE) by rw [←pow_two,lambdaE_sq]; ring,
    neg_dvd,mul_dvd_mul_iff_left lambdaE_prime.ne_zero]

lemma cubicThetaRamifiedMiddleFactor_eq (e : Eisensteinˣ) (r : Fin 3)
    (he : (e:Eisenstein)=omegaE^(r:ℕ) ∨ (e:Eisenstein)=-(omegaE^(r:ℕ)))
    (h : Eisenstein) :
    cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*h)=
      if (3:Eisenstein)∣lambdaE*(-(((e⁻¹:Eisensteinˣ):Eisenstein))*h+(r:ℕ)) then
        (1/3:ℂ)*residueFourierChar 9 (by norm_num)
          (Ideal.Quotient.mk (modulus 9) (-(((e⁻¹:Eisensteinˣ):Eisenstein))*(lambdaE*h)))
      else 0 := by
  have hp : (27:ℂ)^(-(4/3:ℂ))=1/81 := by
    have ht := cubicThetaRamifiedCubeFactor_pole
    unfold cubicThetaRamifiedCubeFactor at ht
    linear_combination (1/27:ℂ)*ht
  have hv := cubicThetaRamifiedFactor_value e r he 1 (4/3) (lambdaE*h)
  simp only [pow_one] at hv
  rw [show lambdaE^2*h=lambdaE*(lambdaE*h) by ring,hv]
  norm_num only [Nat.reduceAdd,Nat.reduceMod,Nat.cast_zero,mul_zero,add_zero,pow_one]
  rw [hp]
  have hc : -(((e⁻¹:Eisensteinˣ):Eisenstein))*(lambdaE*h)+lambdaE*(r:ℕ)=
      lambdaE*(-(((e⁻¹:Eisensteinˣ):Eisenstein))*h+(r:ℕ)) := by ring
  rw [hc]
  split_ifs <;> ring

lemma cubicThetaRamifiedMiddleFactor_norm_le (e : Eisensteinˣ) (h : Eisenstein) :
    ‖cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*h)‖≤1/3 := by
  obtain ⟨r,hr⟩ := cubicThetaUnit_signed_power e
  rw [cubicThetaRamifiedMiddleFactor_eq e r hr h]
  split_ifs
  · rw [norm_mul,residueFourierChar_mk]
    norm_num
  · norm_num

theorem cubicThetaRamifiedMiddleFactor_support (e : Eisensteinˣ) {h : Eisenstein}
    (hh : lambdaE∣h-1)
    (hne : cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*h)≠0) :
    e=cubicThetaOmegaUnit ∨ e=-(cubicThetaOmegaUnit^2) := by
  obtain ⟨r,hr⟩ := cubicThetaUnit_signed_power e
  have hc : (3:Eisenstein)∣lambdaE*(-(((e⁻¹:Eisensteinˣ):Eisenstein))*h+(r:ℕ)) := by
    by_contra hc
    rw [cubicThetaRamifiedMiddleFactor_eq e r hr h,ite_eq_right hc] at hne
    exact hne rfl
  have hd := (cubicThetaThree_dvd_lambda_mul _).mp hc
  have hE : lambdaE∣(e:Eisenstein)*(r:ℕ)-1 := by
    have hm := dvd_mul_of_dvd_right hd (e:Eisenstein)
    have hi : (e:Eisenstein)*((e⁻¹:Eisensteinˣ):Eisenstein)=1 := by simp
    have ht : lambdaE∣-h+(e:Eisenstein)*(r:ℕ) := by
      convert hm using 1
      linear_combination h*hi
    convert dvd_add ht hh using 1
    ring
  have h1 : ¬lambdaE∣(1:Eisenstein) :=
    fun hd => lambdaE_prime.not_isUnit (isUnit_of_dvd_one hd)
  have h2 : ¬lambdaE∣(-2:Eisenstein) := fun hd =>
    lambdaE_prime.not_isUnit ((primary_coprime_lambda primary_neg_two).isRelPrime hd dvd_rfl)
  rcases hr with hr | hr
  · have hu : lambdaE∣(e:Eisenstein)-1 := by
      rw [hr]
      exact cubicThetaLambda_dvd_omega_pow_sub_one r
    have ht : lambdaE∣(r:ℕ)-1 := by
      convert dvd_sub hE (dvd_mul_of_dvd_left hu (r:ℕ)) using 1
      ring
    fin_cases r
    · have ht' : lambdaE∣(-1:Eisenstein) := by simpa using ht
      exact (h1 (by simpa using dvd_neg.mp ht')).elim
    · exact Or.inl (Units.ext (by simpa [cubicThetaOmegaUnit] using hr))
    · exact (h1 (by norm_num at ht ⊢; exact ht)).elim
  · have hu : lambdaE∣(e:Eisenstein)+1 := by
      rw [hr]
      convert dvd_neg.mpr (cubicThetaLambda_dvd_omega_pow_sub_one r) using 1
      ring
    have ht : lambdaE∣-(r:ℕ)-1 := by
      convert dvd_sub hE (dvd_mul_of_dvd_left hu (r:ℕ)) using 1
      ring
    fin_cases r
    · have ht' : lambdaE∣(-1:Eisenstein) := by simpa using ht
      exact (h1 (by simpa using dvd_neg.mp ht')).elim
    · exact (h2 (by norm_num at ht ⊢; exact ht)).elim
    · exact Or.inr (Units.ext (by simpa [cubicThetaOmegaUnit] using hr))

end CubicFirstMoment

end

end OAI
