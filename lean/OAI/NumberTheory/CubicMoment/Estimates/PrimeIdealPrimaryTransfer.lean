import OAI.NumberTheory.CubicMoment.Estimates.PrimeIdealBall
import OAI.NumberTheory.CubicMoment.Estimates.PrimeToThreeIdeals
import OAI.NumberTheory.CubicMoment.Estimates.FixedAngularHecke

namespace OAI

/-! Exact passage from complete prime ideals to the manuscript's unique
primary prime representatives when the ramified coefficient vanishes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma prime_idealExponent_single {a : Eisenstein} (ha : Prime a) :
    ∃ p : EisensteinIdealPrime, idealExponentOf a=Finsupp.single p 1 := by
  have hcard : (idealExponentOf a).support.card=1 := by
    rw [idealExponentOf_support_card ha.irreducible.squarefree,
      UniqueFactorizationMonoid.card_factors_of_irreducible ha.irreducible]
  obtain ⟨p,hp,he⟩ := Finsupp.card_support_eq_one.mp hcard
  have hone : idealExponentOf a p=1 := by
    have hle := (idealExponentOf_squarefree_iff ha.ne_zero).mpr ha.irreducible.squarefree p
    omega
  exact ⟨p,by rw [he,hone]⟩

lemma prime_idealPrimaryGenerator (p : EisensteinIdealPrime) :
    Prime (idealPrimaryGenerator (Finsupp.single p 1)) := by
  have hp : Prime (idealExponentGenerator (Finsupp.single p 1)) := by
    simpa [idealExponentGenerator,Finsupp.prod_single_index] using
      (idealPrimeRepresentative_irreducible p).prime
  exact (primaryNormalize_associated (idealExponentGenerator (Finsupp.single p 1))).prime_iff.mp hp

lemma primeCutoff_image_idealExponent (X : ℝ) :
    (primeCutoff X).image idealExponentOf =
      ((fullIdealBall X).filter (fun ν => ∃ p : EisensteinIdealPrime, ν=Finsupp.single p 1)).filter
        (fun ν => primary (idealPrimaryGenerator ν)) := by
  ext ν
  simp only [Finset.mem_image,Finset.mem_filter,mem_fullIdealBall]
  constructor
  · rintro ⟨a,ha,rfl⟩
    obtain ⟨hap,haX⟩ := mem_primeCutoff.mp ha
    refine ⟨⟨?_,prime_idealExponent_single hap.2⟩,?_⟩
    · rwa [idealExponentOf_norm hap.2.ne_zero]
    · rw [idealPrimaryGenerator_at_element hap.1]
      exact hap.1
  · rintro ⟨⟨hN,p,rfl⟩,hp⟩
    refine ⟨idealPrimaryGenerator (Finsupp.single p 1),mem_primeCutoff.mpr ⟨⟨hp,
      prime_idealPrimaryGenerator p⟩,?_⟩,idealExponentOf_primaryGenerator _⟩
    rwa [idealPrimaryGenerator_norm]

theorem idealPrimeChebyshev_primary_sum (χ : EisensteinIdealExponent → ℂ)
    (ψ : Eisenstein → ℂ)
    (hzero : ∀ ν, ¬primary (idealPrimaryGenerator ν) → χ ν=0)
    (hval : ∀ a : Eisenstein, primary a → χ (idealExponentOf a)=ψ a) (X : ℝ) :
    idealPrimeChebyshev χ X=primeChebyshev ψ X := by
  unfold idealPrimeChebyshev
  have he : (∑ ν ∈ (fullIdealBall X).filter (fun ν => ∃ p : EisensteinIdealPrime, ν=Finsupp.single p 1),
      (Real.log (idealExponentNorm ν):ℂ)*χ ν) =
      ∑ ν ∈ ((fullIdealBall X).filter (fun ν => ∃ p : EisensteinIdealPrime, ν=Finsupp.single p 1)).filter
        (fun ν => primary (idealPrimaryGenerator ν)), (Real.log (idealExponentNorm ν):ℂ)*χ ν := by
    conv_rhs => rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ν hν
    by_cases hp : primary (idealPrimaryGenerator ν)
    · rw [ite_eq_left hp]
    · rw [ite_eq_right hp,hzero ν hp,mul_zero]
  rw [he,←primeCutoff_image_idealExponent,Finset.sum_image]
  · unfold primeChebyshev
    rw [primeCutoffSum_eq_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have hap := (mem_primeCutoff.mp ha).1
    rw [hval a hap.1,idealExponentOf_norm hap.2.ne_zero]
    ring
  · intro a ha b hb hab
    exact idealExponentOf_inj_primary (mem_primeCutoff.mp ha).1.1
      (mem_primeCutoff.mp hb).1.1 hab

end CubicFirstMoment

end

end OAI
