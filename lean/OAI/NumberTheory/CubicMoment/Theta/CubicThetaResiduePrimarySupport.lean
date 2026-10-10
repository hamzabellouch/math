import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryResidue
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryPowerCoordinates

namespace OAI

/-! Every nonzero primary residue has genuine squarefree/cube support.
Repeated prime cubes are removed by the proved arithmetic periodicity. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicTheta_primary_cube {p : Eisenstein} (hp : primary p) : primary (p^3) := by
  rw [primary_iff_residue_one,map_pow,((primary_iff_residue_one p).mp hp),one_pow]

theorem cubicThetaWeightedFourierResidue_supported {b : Eisenstein}
    (hb : primary b) (hR : cubicThetaWeightedFourierResidue b≠0) :
    ∃ c d : Eisenstein, primary c ∧ primary d ∧ Squarefree c ∧ b=c*d^3 := by
  have H : ∀ n : ℕ, ∀ b : Eisenstein, normNat b=n → primary b →
      cubicThetaWeightedFourierResidue b≠0 →
        ∃ c d : Eisenstein, primary c ∧ primary d ∧ Squarefree c ∧ b=c*d^3 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro b hn hb hR
      by_cases hs : Squarefree b
      · exact ⟨b,1,hb,primary_one,hs,by simp⟩
      obtain ⟨p,hp,hpp⟩ := exists_primary_prime_square_dvd hb hs
      by_cases h3 : p^3∣b
      · obtain ⟨d,rfl⟩ := h3
        have hd : primary d := primary_of_mul (cubicTheta_primary_cube hp.1) hb
        have hdR : cubicThetaWeightedFourierResidue d≠0 := by
          intro hz
          rw [cubicThetaWeightedFourierResidue_cube hp d (primary_ne_zero hd),hz,mul_zero] at hR
          exact hR rfl
        have hNp : 1<normNat p := by
          have he := cubicThetaPrimaryPrime_norm_gt_one hp
          rwa [←normNat_cast,Nat.one_lt_cast] at he
        have hNd : 0<normNat d := Nat.pos_of_ne_zero (normNat_ne_zero (primary_ne_zero hd))
        have hlt : normNat d<n := by
          rw [←hn,normNat_mul,show normNat (p^3)=(normNat p)^3 from map_pow normNatHom p 3]
          have hpow : 1<(normNat p)^3 := one_lt_pow₀ hNp (by decide : (3:ℕ)≠0)
          nlinarith
        obtain ⟨c,e,hc,he,hs,hde⟩ := ih (normNat d) hlt d rfl hd hdR
        refine ⟨c,p*e,hc,primary_mul hp.1 he,hs,?_⟩
        rw [hde]
        ring
      · obtain ⟨d,hbd⟩ := hpp
        have hd : ¬p∣d := by
          rintro ⟨e,he⟩
          apply h3
          refine ⟨e,?_⟩
          rw [hbd,he]
          ring
        have hz : cubicThetaWeightedFourierResidue b=0 := by
          rw [hbd,←pow_two,cubicThetaWeightedFourierResidue_square_zero hp d hd]
        exact (hR hz).elim
  exact H (normNat b) b rfl hb hR

theorem cubicThetaWeightedFourierResidue_primary_all {b : Eisenstein} (hb : primary b) :
    cubicThetaWeightedFourierResidue b=
      (cubicThetaArithmeticCoefficient (lambdaE*b)/81)*cubicThetaWeightedFourierResidue 1 := by
  by_cases hR : cubicThetaWeightedFourierResidue b=0
  · by_cases hc : Nonempty (CubicThetaCoordinates (lambdaE*b))
    · have hc' : Nonempty (CubicThetaCoordinates ((1:Eisensteinˣ)*lambdaE^1*b)) := by
        simpa only [Units.val_one,one_mul,pow_one] using hc
      obtain ⟨c,d,hpc,hpd,hsc,hb'⟩ := (cubicThetaCoordinates_primary_power_iff hb 1 1).mp hc'
      subst b
      simpa only [mul_assoc] using cubicThetaWeightedFourierResidue_theta_primary hpc hpd hsc
    · rw [cubicThetaArithmeticCoefficient,dite_eq_right hc,zero_div,zero_mul,hR]
  · obtain ⟨c,d,hc,hd,hs,hb'⟩ := cubicThetaWeightedFourierResidue_supported hb hR
    subst b
    simpa only [mul_assoc] using cubicThetaWeightedFourierResidue_theta_primary hc hd hs

end CubicFirstMoment

end

end OAI
