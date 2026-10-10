import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramPrimeMismatch
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramKloosterman
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeValuation

namespace OAI

/-! The actual off-diagonal Gram formula has no denominators divisible
by the square of a prime which divides just one of its two frequencies. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaKloostermanSum_square_factor_zero {p c : Eisenstein}
    (hp : primaryPrime p) (hc : (3:Eisenstein)∣c) (hc0 : c≠0) (hpc : p^2∣c)
    (h k : Eisenstein) (hh : p∣h) (hk : ¬p∣k) :
    cubicThetaKloostermanSum h k c hc=0 := by
  obtain ⟨m,d,hpd,he⟩ := WfDvdMonoid.max_power_factor hc0 hp.2.irreducible
  have hd0 : d≠0 := (mul_ne_zero_iff.mp (he ▸ hc0)).2
  have h3p : IsCoprime (3:Eisenstein) p :=
    isCoprime_of_residue_isUnit (unit_residue_of_dvd_primary hp.1 (dvd_refl p))
  have h3d : (3:Eisenstein)∣d := h3p.pow_right.dvd_of_dvd_mul_left (he ▸ hc)
  have hm : 2 ≤ m := by
    by_contra hn
    have hm' : m=0 ∨ m=1 := by omega
    rcases hm' with hm' | hm'
    · subst m
      have hd : p^2∣d := by
        have hd := hpc
        rwa [he,pow_zero,one_mul] at hd
      exact hpd (dvd_trans (dvd_pow_self p (by decide : 2≠0)) hd)
    · subst m
      have hd : p*p∣p*d := by
        have hd := hpc
        rwa [he,pow_one,pow_two] at hd
      exact hpd ((mul_dvd_mul_iff_left hp.2.ne_zero).mp hd)
  have hm' : m=(m-2)+2 := by omega
  have hg := cubicThetaKloostermanSum_prime_mismatch_zero hp h3d hd0
    (hp.2.coprime_iff_not_dvd.mpr hpd).symm (m-2) h k hh hk
  simpa only [←hm',←he] using hg

lemma cubicThetaGramKloostermanTerm_square_factor_zero {p c : Eisenstein}
    (hp : primaryPrime p) (hpc : p^2∣c) (h k : Eisenstein) (hh : p∣h) (hk : ¬p∣k)
    (V : C_c(ℝ,ℂ)) (v : ℝ) : cubicThetaGramKloostermanTerm h k V c v=0 := by
  unfold cubicThetaGramKloostermanTerm
  split_ifs with hc
  · rw [cubicThetaKloostermanSum_square_factor_zero hp hc.1 hc.2 hpc h k hh hk,zero_mul]
  · rfl

theorem cubicThetaGramKloosterman_prime_square_filter {p : Eisenstein}
    (hp : primaryPrime p) (h k : Eisenstein) (hh : p∣h) (hk : ¬p∣k)
    (V : C_c(ℝ,ℂ)) (ε δ v : ℝ) :
    (∑ c∈cubicThetaGramDenominators ε δ,cubicThetaGramKloostermanTerm h k V c v)=
      ∑ c∈(cubicThetaGramDenominators ε δ).filter (fun c => ¬p^2∣c),
        cubicThetaGramKloostermanTerm h k V c v := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : p^2∣c
  · rw [ite_eq_right (not_not.mpr hc),
      cubicThetaGramKloostermanTerm_square_factor_zero hp hc h k hh hk V v]
  · rw [ite_eq_left hc]

theorem cubicThetaKloostermanGram_prime_square_filter {p : Eisenstein}
    (hp : primaryPrime p) (h k : Eisenstein) (hh : p∣h) (hk : ¬p∣k)
    (W V : C_c(ℝ,ℂ)) (ε δ : ℝ) :
    cubicThetaKloostermanGram h k W V ε δ=
      ∫ v in Ioi ε,star (W v)/(v:ℂ)^3*
        (V v*cubicThetaHorizontalFourierCoefficient h (cubicThetaHorizontalCharacter k)+
          ∑ c∈(cubicThetaGramDenominators ε δ).filter (fun c => ¬p^2∣c),
            cubicThetaGramKloostermanTerm h k V c v) := by
  unfold cubicThetaKloostermanGram
  simp_rw [cubicThetaGramKloosterman_prime_square_filter hp h k hh hk]

theorem cubicThetaKloostermanSum_square_factor_zero_symm {p c : Eisenstein}
    (hp : primaryPrime p) (hc : (3:Eisenstein)∣c) (hc0 : c≠0) (hpc : p^2∣c)
    (h k : Eisenstein) (hh : ¬p∣h) (hk : p∣k) :
    cubicThetaKloostermanSum h k c hc=0 := by
  rw [cubicThetaKloostermanSum_hermitian hc hc0,
    cubicThetaKloostermanSum_square_factor_zero hp hc hc0 hpc (-k) (-h)
      (dvd_neg.mpr hk) (fun hd => hh (dvd_neg.mp hd)),star_zero]

lemma cubicThetaGramKloostermanTerm_square_factor_zero_symm {p c : Eisenstein}
    (hp : primaryPrime p) (hpc : p^2∣c) (h k : Eisenstein) (hh : ¬p∣h) (hk : p∣k)
    (V : C_c(ℝ,ℂ)) (v : ℝ) : cubicThetaGramKloostermanTerm h k V c v=0 := by
  unfold cubicThetaGramKloostermanTerm
  split_ifs with hc
  · rw [cubicThetaKloostermanSum_square_factor_zero_symm hp hc.1 hc.2 hpc h k hh hk,zero_mul]
  · rfl

theorem cubicThetaKloostermanGram_prime_square_filter_symm {p : Eisenstein}
    (hp : primaryPrime p) (h k : Eisenstein) (hh : ¬p∣h) (hk : p∣k)
    (W V : C_c(ℝ,ℂ)) (ε δ : ℝ) :
    cubicThetaKloostermanGram h k W V ε δ=
      ∫ v in Ioi ε,star (W v)/(v:ℂ)^3*
        (V v*cubicThetaHorizontalFourierCoefficient h (cubicThetaHorizontalCharacter k)+
          ∑ c∈(cubicThetaGramDenominators ε δ).filter (fun c => ¬p^2∣c),
            cubicThetaGramKloostermanTerm h k V c v) := by
  unfold cubicThetaKloostermanGram
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  dsimp only
  congr 2
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : p^2∣c
  · rw [ite_eq_right (not_not.mpr hc),
      cubicThetaGramKloostermanTerm_square_factor_zero_symm hp hc h k hh hk V v]
  · rw [ite_eq_left hc]

end CubicFirstMoment

end

end OAI
