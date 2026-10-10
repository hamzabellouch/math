import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeValuation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRowRecurrence

namespace OAI

/-! Exact prime-power separation of the original arithmetic Dirichlet
series. Absolute convergence is used only for the iterated sum. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaDenominatorTerm (s : ℂ) (h : Eisenstein) (c : CubicThetaDenominator) : ℂ :=
  cubicThetaEisensteinGaussCoefficient c.val h*(norm c.val:ℂ)^(-s)

def cubicThetaPrimePowerTerm (p : Eisenstein) (hp : primaryPrime p) (s : ℂ) (h : Eisenstein)
    (v : ℕ × CubicThetaPrimeFreeDenominator p) : ℂ :=
  cubicThetaDenominatorTerm s h (cubicThetaPrimePowerDenominator p hp v)

lemma cubicThetaFrequencyDirichlet_denominators (s : ℂ) (h : Eisenstein) :
    cubicThetaFrequencyDirichlet h s=∑' c : CubicThetaDenominator, cubicThetaDenominatorTerm s h c := by
  have hs : Function.support (cubicThetaFrequencyTerm s h) ⊆
      {c : Eisenstein | (3:Eisenstein) ∣ c ∧ c≠0} := by
    intro c hc
    by_contra hp
    change ¬((3:Eisenstein) ∣ c ∧ c≠0) at hp
    exact hc (by rw [cubicThetaFrequencyTerm,ite_eq_right hp])
  rw [cubicThetaFrequencyDirichlet,← tsum_subtype_eq_of_support_subset hs]
  apply tsum_congr
  intro c
  have hc : (3:Eisenstein) ∣ c.val ∧ c.val≠0 := c.property
  change cubicThetaFrequencyTerm s h c.val=_
  rw [cubicThetaFrequencyTerm,ite_eq_left hc]
  rfl

lemma cubicThetaDenominatorTerm_summable {s : ℂ} (hs : 2<s.re) (h : Eisenstein) :
    Summable (cubicThetaDenominatorTerm s h) := by
  have hf := (cubicThetaFrequencyTerm_norm_summable hs h).of_norm.subtype
    (fun c : Eisenstein => (3:Eisenstein) ∣ c ∧ c≠0)
  apply hf.congr
  intro c
  have hc : (3:Eisenstein) ∣ c.val ∧ c.val≠0 := c.property
  change cubicThetaFrequencyTerm s h c.val=_
  rw [cubicThetaFrequencyTerm,ite_eq_left hc]
  rfl

theorem cubicThetaFrequencyDirichlet_primePowers {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) :
    cubicThetaFrequencyDirichlet h s=∑' v : ℕ × CubicThetaPrimeFreeDenominator p,
      cubicThetaPrimePowerTerm p hp s h v := by
  rw [cubicThetaFrequencyDirichlet_denominators]
  exact ((cubicThetaPrimePowerDenominatorEquiv p hp).tsum_eq (cubicThetaDenominatorTerm s h)).symm

lemma cubicThetaPrimePowerTerm_summable {p : Eisenstein} (hp : primaryPrime p)
    {s : ℂ} (hs : 2<s.re) (h : Eisenstein) : Summable (cubicThetaPrimePowerTerm p hp s h) :=
  (cubicThetaDenominatorTerm_summable hs h).comp_injective
    (cubicThetaPrimePowerDenominatorEquiv p hp).injective

theorem cubicThetaFrequencyDirichlet_primePowers_iterated {p : Eisenstein}
    (hp : primaryPrime p) {s : ℂ} (hs : 2<s.re) (h : Eisenstein) :
    cubicThetaFrequencyDirichlet h s=∑' n : ℕ, ∑' d : CubicThetaPrimeFreeDenominator p,
      cubicThetaPrimePowerTerm p hp s h (n,d) := by
  rw [cubicThetaFrequencyDirichlet_primePowers hp]
  exact (cubicThetaPrimePowerTerm_summable hp hs h).tsum_prod

lemma cubicThetaPrimePowerTerm_high {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (hh : ¬p ∣ h) (n : ℕ) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s h (n+2,d)=0 := by
  have hcp : IsCoprime d.val p := (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm
  change cubicThetaEisensteinGaussCoefficient (p^(n+2)*d.val) h*
    (norm (p^(n+2)*d.val):ℂ)^(-s)=0
  rw [cubicThetaEisensteinGaussCoefficient_highPrimePower hp d.property.1 d.property.2.1 hcp n h hh,
    zero_mul]

theorem cubicThetaFrequencyDirichlet_two_terms {p : Eisenstein} (hp : primaryPrime p)
    {s : ℂ} (hs : 2<s.re) (h : Eisenstein) (hh : ¬p ∣ h) :
    cubicThetaFrequencyDirichlet h s=
      (∑' d : CubicThetaPrimeFreeDenominator p, cubicThetaPrimePowerTerm p hp s h (0,d))+
      ∑' d : CubicThetaPrimeFreeDenominator p, cubicThetaPrimePowerTerm p hp s h (1,d) := by
  rw [cubicThetaFrequencyDirichlet_primePowers_iterated hp hs]
  rw [tsum_eq_sum (s:=({0,1}:Finset ℕ))]
  · simp
  · intro n hn
    have hn2 : 2 ≤ n := by simp only [Finset.mem_insert,Finset.mem_singleton] at hn; omega
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn2
    have hz (d : CubicThetaPrimeFreeDenominator p) : cubicThetaPrimePowerTerm p hp s h (2+k,d)=0 := by
      simpa only [add_comm 2 k] using cubicThetaPrimePowerTerm_high hp s h hh k d
    simp only [hz,tsum_zero]

end CubicFirstMoment

end

end OAI
