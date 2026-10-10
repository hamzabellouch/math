import OAI.NumberTheory.CubicMoment.Estimates.IdealPrimeReplacement

namespace OAI

/-! A finite norm ball of prime ideals and the exact reindexing of its
logarithmically weighted sum. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primeIdealBall (X : ℝ) : Finset EisensteinIdealPrime :=
  (fullIdealBall X).biUnion Finsupp.support

@[simp] lemma mem_primeIdealBall {X : ℝ} {p : EisensteinIdealPrime} :
    p ∈ primeIdealBall X ↔ idealExponentNorm (Finsupp.single p 1) ≤ X := by
  constructor
  · intro hp
    obtain ⟨ν,hν,hpν⟩ := Finset.mem_biUnion.mp hp
    have hle : Finsupp.single p 1 ≤ ν := Finsupp.single_le_iff.mpr
      (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hpν))
    exact (idealExponentNorm_mono hle).trans (mem_fullIdealBall.mp hν)
  · intro hp
    exact Finset.mem_biUnion.mpr ⟨Finsupp.single p 1,mem_fullIdealBall.mpr hp,by simp⟩

lemma primeIdealBall_image (X : ℝ) :
    (primeIdealBall X).image (fun p => Finsupp.single p 1) =
      (fullIdealBall X).filter (fun ν => ∃ p : EisensteinIdealPrime, ν=Finsupp.single p 1) := by
  ext ν
  simp only [Finset.mem_image,mem_primeIdealBall,Finset.mem_filter,mem_fullIdealBall]
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact ⟨hp,p,rfl⟩
  · rintro ⟨hν,p,rfl⟩
    exact ⟨p,hν,rfl⟩

lemma idealPrimeChebyshev_eq_sum_primes (χ : EisensteinIdealExponent → ℂ) (X : ℝ) :
    idealPrimeChebyshev χ X = ∑ p ∈ primeIdealBall X,
      (Real.log (idealExponentNorm (Finsupp.single p 1)):ℂ)*χ (Finsupp.single p 1) := by
  unfold idealPrimeChebyshev
  rw [←primeIdealBall_image,Finset.sum_image]
  exact fun _ _ _ _ h => Finsupp.single_left_injective (by norm_num : (1:ℕ) ≠ 0) h

lemma primeIdealLog_nonneg (p : EisensteinIdealPrime) :
    0 ≤ Real.log (idealExponentNorm (Finsupp.single p 1)) :=
  Real.log_nonneg (idealExponentNorm_ge_one _)

lemma idealExponentNorm_primeSet (S : Finset EisensteinIdealPrime) :
    idealExponentNorm (primeSetExponent S) =
      ∏ p ∈ S, idealExponentNorm (Finsupp.single p 1) := by
  induction S using Finset.induction_on with
  | empty => simp [primeSetExponent,idealExponentNorm,idealExponentGenerator]
  | @insert p S hp ih =>
    simp only [primeSetExponent,Finset.sum_insert hp,idealExponentNorm_add,Finset.prod_insert hp] at *
    rw [ih]

lemma primeIdealLog_sum_le (S : Finset EisensteinIdealPrime) (ν : EisensteinIdealExponent)
    (hS : S ⊆ ν.support) :
    (∑ p ∈ S, Real.log (idealExponentNorm (Finsupp.single p 1))) ≤ Real.log (idealExponentNorm ν) := by
  have hle : primeSetExponent S ≤ ν := (primeSetExponent_le_iff S ν).mpr
    (fun p hp => Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (hS hp)))
  have hh := Real.log_le_log (idealExponentNorm_pos (primeSetExponent S)) (idealExponentNorm_mono hle)
  rwa [idealExponentNorm_primeSet,Real.log_prod (fun _ _ => (idealExponentNorm_pos _).ne')] at hh

end CubicFirstMoment

end

end OAI
