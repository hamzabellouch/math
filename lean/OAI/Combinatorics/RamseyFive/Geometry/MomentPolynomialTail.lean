import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.OverlapDyads

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.DyadicMoments
open scoped BigOperators Classical
variable {α ι : Type*} [Fintype α]

theorem moment_polynomial_tail (x : α → ℝ) (a : ι → ℝ) (T : Finset ι)
    (K : ℕ) (hK : K≠0) (A : ℝ) (hx : ∀ v,0 ≤ x v) (ha : ∀ i∈T,0 ≤ a i)
    (hcover : ∀ v,0<x v → ∃ i∈T,a i ≤ x v ∧ x v ≤ 2*a i)
    (hcount : ∀ i∈T,((Finset.univ.filter fun v => a i ≤ x v).card:ℝ)*a i^K ≤ A) :
    (∑ v,x v^K) ≤ 2^K*T.card*A := by
  apply (moment_weighted_cover x a T K hK hx ha hcover).trans
  have hh := Finset.sum_le_sum (fun i hi => hcount i hi)
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring)

theorem pow_sum_from_lower (x : α → ℝ) (m A : ℝ) (K R : ℕ) (hm0 : 0 ≤ m) (hKR : K ≤ R)
    (hx : ∀ v,0 ≤ x v) (hm : ∀ v,x v ≤ m) (hA : (∑ v,x v^K) ≤ A) :
    (∑ v,x v^R) ≤ m^(R-K)*A := by
  have hpow (v : α) : x v^R ≤ m^(R-K)*x v^K := by
    have he : R=(R-K)+K := by omega
    calc
      _ = x v^(R-K)*x v^K := by rw [←pow_add,←he]
      _  ≤  _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hx v) (hm v) _) (pow_nonneg (hx v) _)
  apply (Finset.sum_le_sum (fun v (_ : v∈Finset.univ) => hpow v)).trans
  rw [←Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hA (pow_nonneg hm0 _)

end SharpRamseyFive.DyadicMoments
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence PoissonScore WeightedPrograms DyadicMoments
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

noncomputable def boundedOverlapDyads (X : Finset {y : ℙ K V // x≠y})
    (δ : ℝ≥0) (m : ℝ) : Finset ℕ :=
  (overlapDyads x X).filter fun i => (δ:ℝ)*2^i ≤ m

omit [FiniteDimensional K V] [Finite K] [Fintype (RadialLine x)] in
lemma boundedOverlapDyads_card (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (m : ℝ) :
    (boundedOverlapDyads x X δ m).card ≤ Nat.clog 2 X.card+1 := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

omit [FiniteDimensional K V] [Finite K] in
lemma strength_le_typical_cap (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (m : ℝ)
    (hm : ∀ H : F,mass (radialWeight x X δ) (pencilLines x F H) ≤ m)
    (p : DistinctPairs F) : strength (pencilLines x F) (radialWeight x X δ) p ≤ m := by
  apply le_trans _ (hm p.1)
  change mass _ (_ ∩ _) ≤ mass _ _
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_left)
  intro d _ _
  exact NNReal.coe_nonneg _

omit [Finite K] in
lemma bounded_overlap_cover (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H) (m : ℝ)
    (hm : ∀ H : F,mass (radialWeight x X δ) (pencilLines x F H) ≤ m)
    (p : DistinctPairs F) (hp : 0<strength (pencilLines x F) (radialWeight x X δ) p) :
    ∃ i∈boundedOverlapDyads x X δ m,
      (δ:ℝ)*2^i ≤ strength (pencilLines x F) (radialWeight x X δ) p ∧
      strength (pencilLines x F) (radialWeight x X δ) p ≤ 2*((δ:ℝ)*2^i) := by
  obtain ⟨i,hi,hlo,hhi⟩ := score_dyadic_cover x X δ hδ F hF p hp
  exact ⟨i,Finset.mem_filter.mpr ⟨hi,hlo.trans (strength_le_typical_cap x X δ F m hm p)⟩,hlo,hhi⟩

omit [Finite K] in

theorem score_polynomial_power (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (m A : ℝ) (hA : 0 ≤ A) (k : ℕ) (hk : k≠0)
    (hm : ∀ H : F,mass (radialWeight x X δ) (pencilLines x F H) ≤ m)
    (hcount : ∀ i∈boundedOverlapDyads x X δ m,
      ((Finset.univ.filter fun p : DistinctPairs F => (δ:ℝ)*2^i ≤
        strength (pencilLines x F) (radialWeight x X δ) p).card:ℝ)*((δ:ℝ)*2^i)^k ≤ A) :
    (∑ p : DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) p^k) ≤
      2^k*(Nat.clog 2 X.card+1)*A := by
  apply (moment_polynomial_tail _ _ (boundedOverlapDyads x X δ m) k hk A
    (strength_nonneg _ _) (by intro i _; positivity)
    (bounded_overlap_cover x X δ hδ F hF m hm) hcount).trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (by exact_mod_cast boundedOverlapDyads_card x X δ m) (by positivity)) hA

omit [Finite K] in

theorem score_higher_power (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (A : ℝ) (hA : 0 ≤ A) (k R : ℕ) (hk : k≠0) (hkR : k ≤ R)
    (hm : ∀ H : F,mass (radialWeight x X δ) (pencilLines x F H) ≤ 2)
    (hcount : ∀ i∈boundedOverlapDyads x X δ 2,
      ((Finset.univ.filter fun p : DistinctPairs F => (δ:ℝ)*2^i ≤
        strength (pencilLines x F) (radialWeight x X δ) p).card:ℝ)*((δ:ℝ)*2^i)^k ≤ A) :
    (∑ p : DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) p^R) ≤
      2^R*(Nat.clog 2 X.card+1)*A := by
  have hh := pow_sum_from_lower _ 2 _ k R (by norm_num) hkR
    (strength_nonneg (pencilLines x F) (radialWeight x X δ))
    (strength_le_typical_cap x X δ F 2 hm)
    (score_polynomial_power x X δ hδ F hF 2 A hA k hk hm hcount)
  apply hh.trans_eq
  rw [←mul_assoc,←mul_assoc,←pow_add,Nat.sub_add_cancel hkR]

end SharpRamseyFive.ScoreGeometry

end OAI
