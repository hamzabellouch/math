import OAI.NumberTheory.CubicMoment.Estimates.IdealPrimePowerCount

namespace OAI

/-! Exact separation of prime ideals from higher prime powers in the
actual von Mangoldt prefix. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def idealPrimeChebyshev (χ : EisensteinIdealExponent → ℂ) (X : ℝ) : ℂ :=
  ∑ ν ∈ fullIdealBall X with ∃ p : EisensteinIdealPrime, ν=Finsupp.single p 1,
    (Real.log (idealExponentNorm ν):ℂ)*χ ν

lemma idealVonMangoldt_single_prime (p : EisensteinIdealPrime) :
    MvPowerSeries.coeff (Finsupp.single p 1) idealVonMangoldt =
      Real.log (idealExponentNorm (Finsupp.single p 1)) := by
  simpa only [zero_add,idealExponentNorm_single,pow_one] using idealVonMangoldt_prime_power p 0

lemma idealVonMangoldt_support (ν : EisensteinIdealExponent)
    (hν : MvPowerSeries.coeff ν idealVonMangoldt ≠ 0) :
    ∃ p : EisensteinIdealPrime, ∃ j : ℕ, 0 < j ∧ ν=Finsupp.single p j := by
  have hc : ν.support.card=1 := by
    by_contra hn
    exact hν (idealVonMangoldt_not_prime_power ν hn)
  obtain ⟨p,hp,he⟩ := Finsupp.card_support_eq_one.mp hc
  exact ⟨p,ν p,Nat.pos_of_ne_zero hp,he⟩

lemma single_prime_ne_higher {p q : EisensteinIdealPrime} {j : ℕ} (hj : 2 ≤ j) :
    (Finsupp.single p 1 : EisensteinIdealExponent) ≠ Finsupp.single q j := by
  intro he
  have hh := congrArg (fun ν : EisensteinIdealExponent => ν q) he
  by_cases hpq : p=q
  · subst p
    simp only [Finsupp.single_eq_same] at hh
    omega
  · simp [Ne.symm hpq] at hh
    omega

theorem idealMangoldtSum_sub_prime (χ : EisensteinIdealExponent → ℂ) (X : ℝ) :
    idealMangoldtSum χ X-idealPrimeChebyshev χ X =
      ∑ ν ∈ higherIdealPrimePowers X,
        ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν := by
  unfold idealMangoldtSum idealPrimeChebyshev higherIdealPrimePowers
  rw [Finset.sum_filter,←Finset.sum_sub_distrib,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ν hν
  by_cases hp : ∃ p : EisensteinIdealPrime, ν=Finsupp.single p 1
  · obtain ⟨p,rfl⟩ := hp
    have hn : ¬∃ q : EisensteinIdealPrime, ∃ j : ℕ, 2 ≤ j ∧
        (Finsupp.single p 1 : EisensteinIdealExponent)=Finsupp.single q j := by
      rintro ⟨q,j,hj,he⟩
      exact single_prime_ne_higher hj he
    rw [ite_eq_left ⟨p,rfl⟩,ite_eq_right hn,idealVonMangoldt_single_prime,sub_self]
  · rw [ite_eq_right hp,sub_zero]
    by_cases hh : ∃ p : EisensteinIdealPrime, ∃ j : ℕ, 2 ≤ j ∧ ν=Finsupp.single p j
    · rw [ite_eq_left hh]
    · rw [ite_eq_right hh]
      have hz : MvPowerSeries.coeff ν idealVonMangoldt=0 := by
        by_contra hn
        obtain ⟨p,j,hj,he⟩ := idealVonMangoldt_support ν hn
        have hj1 : j ≠ 1 := by
          intro hj1
          exact hp ⟨p,by simpa only [hj1] using he⟩
        exact hh ⟨p,j,by omega,he⟩
      rw [hz,Complex.ofReal_zero,zero_mul]

theorem idealMangoldt_prime_replacement_bound (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {X : ℝ} (hX : 1 ≤ X) :
    ‖idealMangoldtSum χ X-idealPrimeChebyshev χ X‖ ≤
      18*Real.sqrt X*(Nat.log 2 ⌊X⌋₊+1)*Real.log X := by
  rw [idealMangoldtSum_sub_prime]
  exact (norm_sum_le _ _).trans (higherIdealPrimePowers_mass χ hχ hX)

end CubicFirstMoment

end

end OAI
