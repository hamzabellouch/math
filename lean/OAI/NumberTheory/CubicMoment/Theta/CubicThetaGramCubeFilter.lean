import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramCubeLowerLayers
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramPrimeSplit

namespace OAI

/-! The first two positive prime valuations contribute zero when both
frequencies contain a cube. Thus the prime-divisible part has a literal
cube-divisible denominator filter. -/
noncomputable section
open scoped BigOperators CompactlySupported
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaKloostermanSum_cube_low_zero {p c : Eisenstein}
    (hp : primaryPrime p) (hc : (3:Eisenstein)∣c) (hc0 : c≠0)
    (hpc : p∣c) (hpc3 : ¬p^3∣c) (h k : Eisenstein) :
    cubicThetaKloostermanSum (p^3*h) (p^3*k) c hc=0 := by
  have h3p : IsCoprime (3:Eisenstein) p :=
    isCoprime_of_residue_isUnit (unit_residue_of_dvd_primary hp.1 (dvd_refl p))
  obtain ⟨d,rfl⟩ := hpc
  have hd : (3:Eisenstein)∣d := h3p.dvd_of_dvd_mul_left hc
  by_cases hpd : p∣d
  · obtain ⟨e,rfl⟩ := hpd
    have he : (3:Eisenstein)∣e := h3p.dvd_of_dvd_mul_left hd
    have he0 : e≠0 := by intro hz; apply hc0; rw [hz,mul_zero,mul_zero]
    have hpe : ¬p∣e := by
      rintro ⟨a,rfl⟩
      apply hpc3
      refine ⟨a,?_⟩
      ring
    have hpow : p*(p*e)=p^2*e := by ring
    simpa only [hpow] using cubicThetaKloostermanSum_cube_layer_two hp he he0
      (hp.2.coprime_iff_not_dvd.mpr hpe).symm h k
  · have hd0 : d≠0 := by intro hz; apply hc0; rw [hz,mul_zero]
    exact cubicThetaKloostermanSum_cube_layer_one hp hd hd0
      (hp.2.coprime_iff_not_dvd.mpr hpd).symm h k

lemma cubicThetaGramKloostermanTerm_cube_low_zero {p c : Eisenstein}
    (hp : primaryPrime p) (hpc : p∣c) (hpc3 : ¬p^3∣c)
    (h k : Eisenstein) (V : C_c(ℝ,ℂ)) (v : ℝ) :
    cubicThetaGramKloostermanTerm (p^3*h) (p^3*k) V c v=0 := by
  unfold cubicThetaGramKloostermanTerm
  split_ifs with hc
  · rw [cubicThetaKloostermanSum_cube_low_zero hp hc.1 hc.2 hpc hpc3 h k,zero_mul]
  · rfl

theorem cubicThetaGramKloostermanTerm_cube_filter {p : Eisenstein}
    (hp : primaryPrime p) (h k : Eisenstein) (V : C_c(ℝ,ℂ)) (ε δ v : ℝ) :
    (∑ c∈(cubicThetaGramDenominators ε δ).filter (fun c => p∣c),
      cubicThetaGramKloostermanTerm (p^3*h) (p^3*k) V c v)=
    ∑ c∈(cubicThetaGramDenominators ε δ).filter (fun c => p^3∣c),
      cubicThetaGramKloostermanTerm (p^3*h) (p^3*k) V c v := by
  rw [Finset.sum_filter,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc3 : p^3∣c
  · have hc : p∣c := (dvd_pow_self p (by decide : 3≠0)).trans hc3
    rw [ite_eq_left hc,ite_eq_left hc3]
  · rw [ite_eq_right hc3]
    by_cases hc : p∣c
    · rw [ite_eq_left hc,cubicThetaGramKloostermanTerm_cube_low_zero hp hc hc3]
    · rw [ite_eq_right hc]

end CubicFirstMoment

end

end OAI
