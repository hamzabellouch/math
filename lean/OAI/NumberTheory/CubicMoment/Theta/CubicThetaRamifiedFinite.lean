import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedUnitConductor

namespace OAI

/-! A nonzero frequency leaves only finitely many ramified powers in
the actual Dirichlet series, uniformly over the unit and primary part. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaRamifiedHeight_exists {h : Eisenstein} (hh : h≠0) :
    ∃ M : ℕ, ∀ n : ℕ, M ≤ n → ¬lambdaE^n ∣ h := by
  obtain ⟨k,d,hd,he⟩ := WfDvdMonoid.max_power_factor hh lambdaE_prime.irreducible
  refine ⟨k+1,?_⟩
  intro n hn hdiv
  have hp : lambdaE^(k+1) ∣ h := (pow_dvd_pow lambdaE hn).trans hdiv
  have hpd : lambdaE^k*lambdaE ∣ lambdaE^k*d := by
    simpa only [pow_succ,he] using hp
  exact hd ((mul_dvd_mul_iff_left (pow_ne_zero _ lambdaE_prime.ne_zero)).mp hpd)

theorem cubicThetaFrequencyDirichlet_ramified_finite {s : ℂ} (hs : 2<s.re)
    (h : Eisenstein) (M : ℕ) (hM : ∀ n : ℕ, M ≤ n → ¬lambdaE^n ∣ h) :
    cubicThetaFrequencyDirichlet h s=
      ∑' e : Eisensteinˣ, ∑ n ∈ Finset.range M, ∑' a : CubicThetaPrimaryPart,
        cubicThetaRamifiedTerm s h (e,n,a) := by
  rw [cubicThetaFrequencyDirichlet_ramified_iterated hs]
  apply tsum_congr
  intro e
  apply tsum_eq_sum
  intro n hn
  have hmn : M ≤ n := by simpa only [Finset.mem_range,not_lt] using hn
  have hz (a : CubicThetaPrimaryPart) : cubicThetaRamifiedTerm s h (e,n,a)=0 :=
    cubicThetaRamifiedTerm_high s h e n a (hM n hmn)
  simp only [hz,tsum_zero]

theorem cubicThetaFrequencyDirichlet_ramified_finite_exists {s : ℂ} (hs : 2<s.re)
    {h : Eisenstein} (hh : h≠0) :
    ∃ M : ℕ, cubicThetaFrequencyDirichlet h s=
      ∑' e : Eisensteinˣ, ∑ n ∈ Finset.range M, ∑' a : CubicThetaPrimaryPart,
        cubicThetaRamifiedTerm s h (e,n,a) := by
  obtain ⟨M,hM⟩ := cubicThetaRamifiedHeight_exists hh
  exact ⟨M,cubicThetaFrequencyDirichlet_ramified_finite hs h M hM⟩

end CubicFirstMoment

end

end OAI
