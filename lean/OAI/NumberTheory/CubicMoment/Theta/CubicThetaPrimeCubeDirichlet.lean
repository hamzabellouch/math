import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRows

namespace OAI

/-! The exact cube-index recurrence of the convergent Eisenstein series.
The prime-free term is retained explicitly; no claim about its residue is
made by this initial-half-plane identity. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaFrequencyDirichlet_five_terms {p : Eisenstein}
    (hp : primaryPrime p) {s : ℂ} (hs : 2<s.re) (h : Eisenstein) (hh : ¬p ∣ h) :
    cubicThetaFrequencyDirichlet (p^3*h) s=
      ∑ n ∈ Finset.range 5, ∑' d : CubicThetaPrimeFreeDenominator p,
        cubicThetaPrimePowerTerm p hp s (p^3*h) (n,d) := by
  rw [cubicThetaFrequencyDirichlet_primePowers_iterated hp hs]
  apply tsum_eq_sum
  intro n hn
  have hn5 : 5 ≤ n := by simpa only [Finset.mem_range,not_lt] using hn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn5
  have hz (d : CubicThetaPrimeFreeDenominator p) :
      cubicThetaPrimePowerTerm p hp s (p^3*h) (5+k,d)=0 := by
    simpa only [add_comm 5 k] using cubicThetaPrimePowerTerm_cube_high hp s h hh k d
  simp only [hz,tsum_zero]

theorem cubicThetaFrequencyDirichlet_cube_recurrence {p : Eisenstein}
    (hp : primaryPrime p) {s : ℂ} (hs : 2<s.re) (h : Eisenstein) (hh : ¬p ∣ h) :
    cubicThetaFrequencyDirichlet (p^3*h) s=
      (norm p:ℂ)^3*((norm p:ℂ)^(-s))^3*cubicThetaFrequencyDirichlet h s+
      (1-(norm p:ℂ)^2*((norm p:ℂ)^(-s))^3)*cubicThetaPrimeFreeDirichlet p s h 0 := by
  have he := cubicThetaFrequencyDirichlet_two_terms hp hs h hh
  simp_rw [cubicThetaPrimePowerTerm_zero hp] at he
  rw [cubicThetaFrequencyDirichlet_five_terms hp hs h hh]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  simp_rw [cubicThetaPrimePowerTerm_cube_zero hp,cubicThetaPrimePowerTerm_cube_one hp,
    cubicThetaPrimePowerTerm_cube_two hp,cubicThetaPrimePowerTerm_cube_three hp,
    cubicThetaPrimePowerTerm_cube_four hp]
  simp only [tsum_zero,add_zero,tsum_mul_left]
  rw [he]
  unfold cubicThetaPrimeFreeDirichlet
  ring

end CubicFirstMoment

end

end OAI
