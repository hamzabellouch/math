import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.DegreeStrengthCount
import OAI.Combinatorics.RamseyFive.Entropy.MomentWeightedCover

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence PoissonScore WeightedPrograms DyadicMoments
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

noncomputable def overlapDyads (X : Finset {y : ℙ K V // x≠y}) : Finset ℕ :=
  Finset.range (Nat.clog 2 X.card+1)

omit [Finite K] in

lemma score_dyadic_cover (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0 < δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (p : DistinctPairs F) (hp : 0 < strength (pencilLines x F) (radialWeight x X δ) p) :
    ∃ i∈overlapDyads x X,(δ:ℝ)*2^i ≤ strength (pencilLines x F) (radialWeight x X δ) p ∧
      strength (pencilLines x F) (radialWeight x X δ) p ≤ 2*((δ:ℝ)*2^i) := by
  change ∃ i∈overlapDyads x X,(δ:ℝ)*2^i ≤ mass (radialWeight x X δ)
    (pencilLines x F p.1 ∩ pencilLines x F p.2.val) ∧
    mass (radialWeight x X δ) (pencilLines x F p.1 ∩ pencilLines x F p.2.val) ≤ 2*((δ:ℝ)*2^i)
  rw [mass_overlap x X δ F hF]
  unfold overlapDyads
  apply dyadic_cover δ _ (by positivity)
  · have hl:=overlap_pos_lower x X δ F hF p.1 p.2.val hp
    rwa [mass_overlap x X δ F hF] at hl
  · have hc : ((X.filter fun y => Incident y.val p.1.val ∧ Incident y.val p.2.val.val).card:ℝ) ≤
        (2:ℝ)^Nat.clog 2 X.card := by
      exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans
        (Nat.le_pow_clog (by omega : 1<2) X.card)
    exact mul_le_mul_of_nonneg_left hc (by positivity)

noncomputable def geometricPairBudget (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (a : ℝ) : ℝ :=
  (ActualOverlap.richRadials x X ⊤ ⌈a/(2*(δ:ℝ))⌉₊).card *
    ((Nat.card K:ℝ)^2+Nat.card K+1)^2*a^2+
      2*(δ:ℝ)^2*X.card^2*((Nat.card K:ℝ)+1)^2

noncomputable def pairPowerBudget (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (k : ℕ) : ℝ :=
  ∑ i∈overlapDyads x X,geometricPairBudget x X δ ((δ:ℝ)*2^i)*((δ:ℝ)*2^i)^(k-2)

omit [FiniteDimensional K V] [Finite K] in
lemma pairPowerBudget_nonneg (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (k : ℕ) :
    0 ≤ pairPowerBudget x X δ k := by
  unfold pairPowerBudget geometricPairBudget
  apply Finset.sum_nonneg
  intro i _
  positivity

theorem score_overlap_power (hdim : finrank K V=5)
    (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0 < δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (k : ℕ) (hk : 2 ≤ k) :
    (∑ p : DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) p^k) ≤
      2^k*pairPowerBudget x X δ k := by
  apply moment_quadratic_tail _ (fun i : ℕ => (δ:ℝ)*2^i)
    (fun i => geometricPairBudget x X δ ((δ:ℝ)*2^i)) (overlapDyads x X) k hk
    (strength_nonneg _ _) (by intro i _; positivity)
    (score_dyadic_cover x X δ hδ F hF)
  intro i _
  exact score_pair_count_four x hdim X δ hδ F hF _ (by positivity)

theorem score_shift_pair_budget (hdim : finrank K V=5)
    (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0 < δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (p k : ℕ) (hk : 2 ≤ k) :
    (∑ A : F,∑ B : F,SingletonEnumeration.shiftKernel (radialWeight x X δ)
      (pencilLines x F) p k A B) ≤ F.card+(2*(p:ℝ))^k*pairPowerBudget x X δ k := by
  rw [SingletonEnumeration.sum_pairs_split_diagonal]
  apply add_le_add
  · have hh:=Finset.sum_le_sum (fun A (_ : A∈(Finset.univ : Finset F)) =>
      (SingletonEnumeration.shiftKernel_range (radialWeight x X δ) (pencilLines x F) p k A A).2)
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,Fintype.card_coe] using hh
  · calc
      _  ≤ ∑ z : DistinctPairs F,((p:ℝ)*strength (pencilLines x F) (radialWeight x X δ) z)^k :=
        Finset.sum_le_sum (fun z _ => min_le_right _ _)
      _ = (p:ℝ)^k*∑ z : DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) z^k := by
        simp only [mul_pow,Finset.mul_sum]
      _  ≤  (p:ℝ)^k*(2^k*pairPowerBudget x X δ k) :=
        mul_le_mul_of_nonneg_left (score_overlap_power x hdim X δ hδ F hF k hk) (by positivity)
      _ = _ := by rw [mul_pow]; ring

theorem score_certificate_pair_budget (hdim : finrank K V=5)
    (X : Finset {y : ℙ K V // x≠y}) (δ L : ℝ≥0) (hδ : 0 < δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (R k : ℕ) (hk : 2 ≤ k) :
    WeightedPrograms.pairMoment (B := Fin R) (pencilLines x F)
      (fun l => L*radialWeight x X δ l) k ≤
        (2*(R:ℝ)*(L:ℝ))^k*pairPowerBudget x X δ k := by
  have he : WeightedPrograms.pairMoment (B := Fin R) (pencilLines x F)
      (fun l => L*radialWeight x X δ l) k=
      ((R:ℝ)*(L:ℝ))^k*∑ z : DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) z^k := by
    unfold WeightedPrograms.pairMoment
    change _ = _ * ∑ z : (Σ h : F, {h' : F // h' ≠ h}), _
    rw [Fintype.sum_sigma,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro H _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro H' _
    simp only [Fintype.card_fin,NNReal.coe_mul,←Finset.mul_sum,WeightedPrograms.strength]
    rw [←mul_assoc,mul_pow]
  rw [he]
  apply (mul_le_mul_of_nonneg_left (score_overlap_power x hdim X δ hδ F hF k hk) (by positivity)).trans_eq
  rw [mul_pow,mul_pow,mul_pow]
  ring

end

open Module ProjectiveIncidence PoissonScore WeightedPrograms DyadicMoments
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

noncomputable def offRow (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (H H' : F) : ℝ :=
  if H=H' then 0 else mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H')

omit [FiniteDimensional K V] [Finite K] in
lemma offRow_nonneg (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (H H' : F) : 0 ≤ offRow x X δ F H H' := by
  unfold offRow
  split_ifs
  · rfl
  · exact mass_nonneg _ _

noncomputable def geometricRowBudget (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (H : F) (a : ℝ) : ℝ :=
  2*mass (radialWeight x X δ) (pencilLines x F H)*((Nat.card K:ℝ)^2+Nat.card K+1)*a+
    2*(mass (radialWeight x X δ) (pencilLines x F H))^2*((Nat.card K:ℝ)+1)

noncomputable def rowPowerBudget (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (H : F) (k : ℕ) : ℝ :=
  ∑ i∈overlapDyads x X,geometricRowBudget x X δ F H ((δ:ℝ)*2^i)*((δ:ℝ)*2^i)^(k-2)

omit [Finite K] in
lemma offRow_cover (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H) (H H' : F)
    (hp : 0<offRow x X δ F H H') :
    ∃ i∈overlapDyads x X,(δ:ℝ)*2^i ≤ offRow x X δ F H H' ∧
      offRow x X δ F H H' ≤ 2*((δ:ℝ)*2^i) := by
  have hn : H≠H' := by intro he; simp only [offRow,ite_eq_left he] at hp; linarith
  have hp' : 0 < mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H') := by
    simpa only [offRow,ite_eq_right hn] using hp
  simpa only [offRow,ite_eq_right hn,WeightedPrograms.strength,PoissonScore.mass] using
    score_dyadic_cover x X δ hδ F hF ⟨H,⟨H',Ne.symm hn⟩⟩ hp'

theorem score_row_power (hdim : finrank K V=5)
    (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (H : F) (k : ℕ) (hk : 2 ≤ k) :
    (∑ H',offRow x X δ F H H'^k) ≤ 2^k*rowPowerBudget x X δ F H k := by
  apply moment_quadratic_tail _ (fun i : ℕ => (δ:ℝ)*2^i)
    (fun i => geometricRowBudget x X δ F H ((δ:ℝ)*2^i)) (overlapDyads x X) k hk
    (offRow_nonneg x X δ F H) (by intro i _; positivity) (offRow_cover x X δ hδ F hF H)
  intro i _
  have ha : 0<(δ:ℝ)*2^i := by positivity
  have he : (Finset.univ.filter (fun H' : F => (δ:ℝ)*2^i ≤ offRow x X δ F H H'))=
      Finset.univ.filter (fun H' : F => H≠H' ∧ (δ:ℝ)*2^i ≤
        mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H')) := by
    apply Finset.filter_congr
    intro H' _
    by_cases h : H=H'
    · simp [offRow,h,not_le.mpr ha]
    · simp [offRow,h]
  rw [he]
  exact score_degree_four x hdim X δ hδ F hF H _ ha.le

theorem score_shift_row_budget (hdim : finrank K V=5)
    (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (H : F) (p k : ℕ) (hk : 2 ≤ k) :
    (∑ H',SingletonEnumeration.shiftKernel (radialWeight x X δ) (pencilLines x F) p k H' H) ≤
      1+(2*(p:ℝ))^k*rowPowerBudget x X δ F H k := by
  have hs : (∑ H' : F,if H=H' then (1:ℝ) else 0)=1 := by simp
  calc
    _ ≤ ∑ H' : F,((if H=H' then (1:ℝ) else 0)+((p:ℝ)*offRow x X δ F H H')^k) := by
      apply Finset.sum_le_sum
      intro H' _
      by_cases he : H=H'
      · simp only [ite_eq_left he,offRow,mul_zero,zero_pow (by omega : k≠0),add_zero]
        exact (SingletonEnumeration.shiftKernel_range _ _ p k H' H).2
      · simp only [ite_eq_right he,offRow,zero_add]
        unfold SingletonEnumeration.shiftKernel
        rw [Finset.inter_comm]
        exact min_le_right _ _
    _ = 1+(p:ℝ)^k*(∑ H',offRow x X δ F H H'^k) := by
      rw [Finset.sum_add_distrib,hs]
      simp only [mul_pow,Finset.mul_sum]
    _ ≤ 1+(p:ℝ)^k*(2^k*rowPowerBudget x X δ F H k) := by
      exact add_le_add_right (mul_le_mul_of_nonneg_left
        (score_row_power x hdim X δ hδ F hF H k hk) (pow_nonneg (Nat.cast_nonneg p) k)) 1
    _ = _ := by rw [mul_pow]; ring

end SharpRamseyFive.ScoreGeometry

end OAI
