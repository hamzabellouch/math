import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.LocalLines
import OAI.Combinatorics.RamseyFive.Entropy.HighExceptions

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining HighPlaneBudget
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [FiniteDimensional K V] [Finite K] [Fintype (RadialLine x)] in

lemma outside_pair_card_le (S T O : Finset (ℙ K V)) (hST : S ⊆ T)
    (A B : Submodule K V) :
    (ActualOverlap.pairPoints x (outsideAt x S O) A B).card ≤
      ((T \ O).filter fun y => y.submodule ≤ A ⊓ B).card := by
  change (((outsideAt x S O).filter fun y => y.val.submodule ≤ A ⊓ B)).card ≤ _
  rw [outsideAt_filter_card]
  apply Finset.card_le_card
  intro y hy
  obtain ⟨hy,hAB⟩ := Finset.mem_filter.mp hy
  obtain ⟨hyS,hyO⟩ := Finset.mem_sdiff.mp hy
  exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr
    ⟨hST hyS,fun ho => hyO (Finset.mem_union_left _ ho)⟩,hAB⟩

lemma score_pairs_le_captured {I : Type*} [LinearOrder I]
    (F : Finset I) (hF : F.Nonempty) (P : I → Submodule K V) (X S : Finset (ℙ K V))
    (J M : ℕ) (hS : S ⊆ X \ remaining F hF (fun i => flatPoints (P i)) X J)
    (δ : ℝ≥0) (hδ : 0<δ) (G : Finset (ℙ K (Dual K V))) (hG : ∀ H∈G,Incident x H)
    (a : ℝ) (hscale : (δ:ℝ)*(2*M) ≤ a) :
    (Finset.univ.filter (fun p : WeightedPrograms.DistinctPairs G => a ≤
      WeightedPrograms.strength (pencilLines x G)
        (radialWeight x (outsideAt x S
          (ownCell F hF (fun i => flatPoints (P i)) X J x)) δ) p)).card ≤
      (capturedPairs F hF P X (G.image fun b => LinearMap.ker b.rep) J M x).card := by
  apply (pair_strength_count_le x _ δ G hG a).trans
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hp,hne,hmass⟩ := Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  refine ⟨hp,hne,?_⟩
  have hcard := outside_pair_card_le x S
    (X \ remaining F hF (fun i => flatPoints (P i)) X J)
    (ownCell F hF (fun i => flatPoints (P i)) X J x) hS p.1 p.2
  have hδ' : (0:ℝ)<δ := by exact_mod_cast hδ
  have hM : (2*(M:ℝ)) ≤
      (ActualOverlap.pairPoints x (outsideAt x S
        (ownCell F hF (fun i => flatPoints (P i)) X J x)) p.1 p.2).card := by
    apply (mul_le_mul_iff_right₀ hδ').mp
    exact hscale.trans hmass
  exact (by exact_mod_cast hM : 2*M ≤ _).trans hcard

theorem score_high_captured_pairs (hdim : finrank K V=5)
    {I : Type*} [LinearOrder I] (F : Finset I) (hF : F.Nonempty)
    (P : I → Submodule K V) (X S : Finset (ℙ K V))
    (J : ℕ) (hS : S ⊆ X \ remaining F hF (fun i => flatPoints (P i)) X J)
    (δ : ℝ≥0) (hδ : 0<δ) (G : Finset (ℙ K (Dual K V))) (hG : ∀ H∈G,Incident x H)
    (L : Finset (Submodule K V)) (hL : ∀ A∈L,finrank K A=3)
    (hcomplete : ∀ A : Submodule K V,finrank K A=3 → A∈L)
    (a b χ : ℝ) (Y : Finset (ℙ K V)) (hxY : x∈Y)
    (hn : 0<X.card) (hb : 0<b) (hb2 : b≤2)
    (hhigh : 2097152*(Nat.card K:ℝ)^2≤X.card*b^2)
    (hscale : (δ:ℝ)*(2*HighParameters.threshold (Nat.card K) X.card b) ≤ a)
    (hx : x∉highExceptions F hF P X L J b χ Y) :
    (Finset.univ.filter (fun p : WeightedPrograms.DistinctPairs G => a ≤
      WeightedPrograms.strength (pencilLines x G)
        (radialWeight x (outsideAt x S
          (ownCell F hF (fun i => flatPoints (P i)) X J x)) δ) p)).card ≤
      2*HighParameters.degree (Nat.card K) X.card b χ*(Nat.card K+1)^2 := by
  apply (score_pairs_le_captured x F hF P X S J _ hS δ hδ G hG a hscale).trans
  apply high_pairs F hF P X hdim _ _ L hL hcomplete J b χ Y x hxY _ hn hb hb2 hhigh hx
  · intro A hA
    obtain ⟨H,_,rfl⟩ := Finset.mem_image.mp hA
    have hk := Module.Dual.finrank_ker_add_one_of_ne_zero H.rep_nonzero
    omega
  · intro A hA
    obtain ⟨H,hH,rfl⟩ := Finset.mem_image.mp hA
    exact hG H hH

omit [Finite K] in

lemma score_pairs_le_residual (X S O : Finset (ℙ K V)) (hS : S ⊆ X)
    (M : ℕ) (δ : ℝ≥0) (hδ : 0<δ) (G : Finset (ℙ K (Dual K V)))
    (hG : ∀ H∈G,Incident x H) (a : ℝ) (hscale : (δ:ℝ)*M ≤ a) :
    (Finset.univ.filter (fun p : WeightedPrograms.DistinctPairs G => a ≤
      WeightedPrograms.strength (pencilLines x G)
        (radialWeight x (outsideAt x S O) δ) p)).card ≤
      (residualPairs (G.image fun b => LinearMap.ker b.rep) X M).card := by
  apply (pair_strength_count_le x _ δ G hG a).trans
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hp,hne,hmass⟩ := Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  refine ⟨hp,hne,?_⟩
  have hc := (outside_pair_card_le x S X O hS p.1 p.2).trans
    (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.sdiff_subset)))
  have hδ' : (0:ℝ)<δ := by exact_mod_cast hδ
  have hM : (M:ℝ) ≤ (ActualOverlap.pairPoints x (outsideAt x S O) p.1 p.2).card := by
    apply (mul_le_mul_iff_right₀ hδ').mp
    exact hscale.trans hmass
  exact (by exact_mod_cast hM : M ≤ _).trans hc

end

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining HighPlaneBudget PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [Finite K] in
lemma pair_tail_training_mono (S T : Finset {y : ℙ K V // x≠y}) (hST : S ⊆ T)
    (δ : ℝ≥0) (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H) (a : ℝ) :
    (Finset.univ.filter fun p : DistinctPairs F => a ≤ strength (pencilLines x F) (radialWeight x S δ) p).card ≤
    (Finset.univ.filter fun p : DistinctPairs F => a ≤ strength (pencilLines x F) (radialWeight x T δ) p).card := by
  apply Finset.card_le_card
  intro p hp
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hp).2.trans ?_⟩
  change mass (radialWeight x S δ) (pencilLines x F p.1 ∩ pencilLines x F p.2.val) ≤
    mass (radialWeight x T δ) (pencilLines x F p.1 ∩ pencilLines x F p.2.val)
  rw [mass_overlap x S δ F hF,mass_overlap x T δ F hF]
  apply mul_le_mul_of_nonneg_left _ δ.coe_nonneg
  exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hST)

omit [FiniteDimensional K V] [Finite K] [Fintype (RadialLine x)] in
lemma outsideAt_antitone (S O T : Finset (ℙ K V)) (hOT : O ⊆ T) :
    outsideAt x S T ⊆ outsideAt x S O := by
  intro y hy
  simp only [outsideAt,Finset.mem_subtype,Finset.mem_sdiff] at hy ⊢
  exact ⟨hy.1,fun h => hy.2 (hOT h)⟩

theorem score_high_captured_pairs_of_le (hdim : finrank K V=5)
    {I : Type} [LinearOrder I] (F : Finset I) (hF : F.Nonempty)
    (P : I → Submodule K V) (X S O : Finset (ℙ K V))
    (J : ℕ) (hS : S ⊆ X \ remaining F hF (fun i => flatPoints (P i)) X J)
    (hO : ownCell F hF (fun i => flatPoints (P i)) X J x ⊆ O)
    (δ : ℝ≥0) (hδ : 0 < δ) (G : Finset (ℙ K (Dual K V))) (hG : ∀ H∈G,Incident x H)
    (L : Finset (Submodule K V)) (hL : ∀ A∈L,finrank K A=3)
    (hcomplete : ∀ A : Submodule K V,finrank K A=3 → A∈L)
    (a b χ : ℝ) (Y : Finset (ℙ K V)) (hxY : x∈Y)
    (hn : 0 < X.card) (hb : 0 < b) (hb2 : b ≤ 2)
    (hhigh : 2097152*(Nat.card K:ℝ)^2 ≤ X.card*b^2)
    (hscale : (δ:ℝ)*(2*HighParameters.threshold (Nat.card K) X.card b) ≤ a)
    (hx : x∉highExceptions F hF P X L J b χ Y) :
    (Finset.univ.filter (fun p : DistinctPairs G => a ≤ strength (pencilLines x G)
      (radialWeight x (outsideAt x S O) δ) p)).card ≤
      2*HighParameters.degree (Nat.card K) X.card b χ*(Nat.card K+1)^2 :=
  (pair_tail_training_mono x _ _ (outsideAt_antitone x S _ O hO) δ G hG a).trans
    (score_high_captured_pairs x hdim F hF P X S J hS δ hδ G hG L hL hcomplete
      a b χ Y hxY hn hb hb2 hhigh hscale hx)

theorem score_high_residual_pairs (hdim : finrank K V=5)
    (X S O : Finset (ℙ K V)) (hS : S ⊆ X)
    (δ : ℝ≥0) (hδ : 0 < δ) (G : Finset (ℙ K (Dual K V))) (hG : ∀ H∈G,Incident x H)
    (L : Finset (Submodule K V)) (hL : ∀ A∈L,finrank K A=3)
    (hcomplete : ∀ A : Submodule K V,finrank K A=3 → A∈L)
    (a b χ : ℝ) (Y : Finset (ℙ K V)) (hxY : x∈Y)
    (hscale : (δ:ℝ)*HighParameters.threshold (Nat.card K) X.card b ≤ a)
    (hx : x∉residualExceptions L X Y b χ) :
    (Finset.univ.filter (fun p : DistinctPairs G => a ≤ strength (pencilLines x G)
      (radialWeight x (outsideAt x S O) δ) p)).card ≤
      HighParameters.degree (Nat.card K) X.card b χ*(Nat.card K+1)^2 := by
  apply (score_pairs_le_residual x X S O hS _ δ hδ G hG a hscale).trans
  apply residual_pairs hdim _ _ L hL hcomplete X Y b χ x hxY _ hx
  · intro A hA
    obtain ⟨H,_,rfl⟩ := Finset.mem_image.mp hA
    have hk := Module.Dual.finrank_ker_add_one_of_ne_zero H.rep_nonzero
    omega
  · intro A hA
    obtain ⟨H,hH,rfl⟩ := Finset.mem_image.mp hA
    exact hG H hH

lemma high_threshold_scale (δ : ℝ≥0) (n a : ℝ) (hn : 0 < n) (ha : 0 ≤ a)
    (hscale : n*(δ:ℝ) ≤ 4*Nat.card K) :
    (δ:ℝ)*(2*HighParameters.threshold (Nat.card K) n a) ≤ a := by
  have hq : (0:ℝ) < Nat.card K := by exact_mod_cast (Nat.card_pos : 0 < Nat.card K)
  have ht := Nat.floor_le (show 0 ≤ n*a/(64*Nat.card K) by positivity)
  change (HighParameters.threshold (Nat.card K) n a:ℝ) ≤ _ at ht
  calc
    _ ≤ (δ:ℝ)*(2*(n*a/(64*Nat.card K))) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left ht (by norm_num)) δ.coe_nonneg
    _ = (n*(δ:ℝ))*a/(32*Nat.card K) := by ring
    _ ≤ (4*Nat.card K)*a/(32*Nat.card K) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hscale ha) (by positivity)
    _ = a/8 := by field_simp; ring
    _ ≤ a := by linarith

end SharpRamseyFive.ScoreGeometry

end OAI
