import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedLowFactor

namespace OAI

/-! The finite Fourier trace in the ramified correction never vanishes.
It equals two on primary frequencies and on lambda cubes. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaRamifiedPhase_one :
    residueFourierChar 3 (by norm_num) (Ideal.Quotient.mk (modulus 3) (1:Eisenstein))=1 := by
  have he := cubicThetaRamifiedCharacter_fourier (-1:Eisenstein)
  have hc : cubicThetaRamifiedCharacter (-1:Eisenstein)=1 := by
    rw [show (-1:Eisenstein)=-(1:Eisenstein) by ring,AddChar.map_neg_eq_inv,
      cubicThetaRamifiedCharacter_one,inv_one]
  have hr : Ideal.Quotient.mk (modulus (3:Eisenstein)) (2*(-1:Eisenstein))=
      Ideal.Quotient.mk (modulus 3) (1:Eisenstein) :=
    residue_eq_of_dvd_sub ⟨-1,by ring⟩
  rw [hc,hr] at he
  exact he.symm

lemma cubicThetaRamifiedPhase_cube (h : Eisenstein) :
    (residueFourierChar 3 (by norm_num) (Ideal.Quotient.mk (modulus 3) h))^3=1 := by
  rw [← AddChar.map_nsmul_eq_pow]
  have hz : (3:ℕ) • Ideal.Quotient.mk (modulus (3:Eisenstein)) h=0 := by
    rw [← map_nsmul]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_span_singleton.mpr
    exact ⟨h,by simp [nsmul_eq_mul]⟩
  rw [hz,AddChar.map_zero_eq_one]

theorem cubicThetaRamifiedTrace_ne_zero (h : Eisenstein) :
    cubicThetaRamifiedTrace h≠0 := by
  intro hz
  have hp := cubicThetaRamifiedPhase_cube h
  have hn := cubicThetaRamifiedPhase_cube (-h)
  unfold cubicThetaRamifiedTrace at hz
  have he := eq_neg_of_add_eq_zero_left hz
  rw [he] at hp
  rw [neg_pow,hn] at hp
  norm_num at hp

theorem cubicThetaRamifiedTrace_primary {h : Eisenstein} (hh : primary h) :
    cubicThetaRamifiedTrace h=2 := by
  have hr : Ideal.Quotient.mk (modulus (3:Eisenstein)) h=1 :=
    (primary_iff_residue_one h).mp hh
  unfold cubicThetaRamifiedTrace
  rw [map_neg,AddChar.map_neg_eq_inv,hr]
  have hp : residueFourierChar 3 (by norm_num) (1:Residues (3:Eisenstein))=1 := by
    simpa only [map_one] using cubicThetaRamifiedPhase_one
  rw [hp,inv_one]
  norm_num

theorem cubicThetaRamifiedTrace_lambda_cube (h : Eisenstein) :
    cubicThetaRamifiedTrace (lambdaE^3*h)=2 := by
  have hz : Ideal.Quotient.mk (modulus (3:Eisenstein)) (lambdaE^3*h)=0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_span_singleton.mpr
    refine ⟨-lambdaE*h,?_⟩
    rw [pow_succ,lambdaE_sq]
    ring
  unfold cubicThetaRamifiedTrace
  rw [map_neg,hz,neg_zero,AddChar.map_zero_eq_one]
  norm_num

end CubicFirstMoment

end

end OAI
