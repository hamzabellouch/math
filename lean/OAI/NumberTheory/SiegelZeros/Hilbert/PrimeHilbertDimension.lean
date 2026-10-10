import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.NoetherNormalization

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.W24

section OrderLifting

variable {α β : Type*} [PartialOrder α] [PartialOrder β]

theorem exists_chain_lift_last (f : α → β) (hs : Function.Surjective f)
    (hu : ∀ a b, f a < b → ∃ a', a < a' ∧ f a' = b)
    (p : LTSeries β) :
    ∃ q : LTSeries α, q.length = p.length ∧ f q.last = p.last := by
  induction p using RelSeries.inductionOn' with
  | singleton b =>
      obtain ⟨a, ha⟩ := hs b
      exact ⟨RelSeries.singleton _ a, rfl, ha⟩
  | snoc p b hb ih =>
      obtain ⟨q, hlen, hlast⟩ := ih
      obtain ⟨a, ha, hab⟩ := hu q.last b (hlast.symm ▸ hb)
      refine ⟨q.snoc a ha, ?_, ?_⟩
      · simp only [RelSeries.snoc_length, hlen]
      · simpa only [RelSeries.last_snoc] using hab

theorem krullDim_le_of_goingUp (f : α → β) (hs : Function.Surjective f)
    (hu : ∀ a b, f a < b → ∃ a', a < a' ∧ f a' = b) :
    Order.krullDim β ≤ Order.krullDim α := by
  unfold Order.krullDim
  refine iSup_le fun p => ?_
  obtain ⟨q, hlen, _⟩ := exists_chain_lift_last f hs hu p
  exact hlen ▸ le_iSup (fun q : LTSeries α => (q.length : WithBot ℕ∞)) q

end OrderLifting

section IntegralDimension

variable {A B : Type*} [CommRing A] [CommRing B]

theorem ringKrullDim_eq_of_integral_injective (f : A →+* B)
    (hf : Function.Injective f) (hi : f.IsIntegral) :
    ringKrullDim B = ringKrullDim A := by
  let algebraFromHom : Algebra A B := f.toAlgebra
  have integralExtension : Algebra.IsIntegral A B := ⟨hi⟩
  let c : PrimeSpectrum B → PrimeSpectrum A :=
    fun p => ⟨p.asIdeal.comap f, inferInstance⟩
  have hc : StrictMono c := by
    intro p q hpq
    obtain ⟨hpq', x, hxq, hxp⟩ := SetLike.lt_iff_le_and_exists.mp (show p.asIdeal < q.asIdeal from hpq)
    exact Ideal.under_lt_under_of_integral_mem_sdiff hpq' ⟨hxq, hxp⟩
      (Algebra.IsIntegral.isIntegral x)
  have hs : Function.Surjective c := by
    intro p
    obtain ⟨q, _, hq, hqp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
      p.asIdeal (⊥ : Ideal B) (by
        change RingHom.ker f ≤ p.asIdeal
        rw [(RingHom.injective_iff_ker_eq_bot f).mp hf]
        exact bot_le)
    exact ⟨⟨q, hq⟩, PrimeSpectrum.ext hqp⟩
  have hu : ∀ a b, c a < b → ∃ a', a < a' ∧ c a' = b := by
    intro a b hab
    obtain ⟨q, haq, hq, hqb⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime b.asIdeal a.asIdeal hab.le
    refine ⟨⟨q, hq⟩, lt_of_le_of_ne haq ?_, PrimeSpectrum.ext hqb⟩
    intro heq
    have he : c a = b := by
      rw [heq]
      exact PrimeSpectrum.ext hqb
    exact hab.ne he
  exact le_antisymm (Order.krullDim_le_of_strictMono c hc)
    (krullDim_le_of_goingUp c hs hu)

end IntegralDimension

section NormalizationDimension

variable (k R : Type*) [Field k] [CommRing R] [Nontrivial R] [Algebra k R]
  [Algebra.FiniteType k R]

theorem exists_finite_normalization_with_dimension :
    ∃ s : ℕ, ∃ g : MvPolynomial (Fin s) k →ₐ[k] R,
      Function.Injective g ∧ g.Finite ∧ ringKrullDim R = (s : WithBot ℕ∞) := by
  obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k R
  refine ⟨s, g, hg, hfin, ?_⟩
  have hd := ringKrullDim_eq_of_integral_injective g.toRingHom hg hfin.to_isIntegral
  simpa only [MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field, ENat.card_eq_coe_natCard, Nat.card_fin,
    WithBot.coe_natCast, zero_add] using hd

end NormalizationDimension

end WeightedTorusJets.W24

end

end SiegelZeros

end OAI
