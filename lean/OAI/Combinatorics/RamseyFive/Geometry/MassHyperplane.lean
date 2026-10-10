import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.PencilCount

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma mass_hyperplaneSupport (S : Finset (ℙ K V)) (δ : ℝ≥0) (H : ℙ K (Dual K V)) :
    mass (fun _ : S => δ) (hyperplaneSupport S H)=cellMass S δ H := by
  unfold mass cellMass hyperplaneSupport
  rw [Finset.sum_const,nsmul_eq_mul,mul_comm]
  congr 1
  congr 1
  exact Finset.card_bij (fun y _ => y.val) (fun y hy =>
    Finset.mem_filter.mpr ⟨y.property,(Finset.mem_filter.mp hy).2⟩)
    (fun _ _ _ _ h => Subtype.ext h)
    (fun y hy => ⟨⟨y,(Finset.mem_filter.mp hy).1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hy).2⟩,rfl⟩)

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma sum_cellMass (S : Finset (ℙ K V)) (T : Finset (ℙ K (Dual K V))) (δ : ℝ) :
    (∑H∈T,cellMass S δ H)=δ*(incidences S T:ℝ) := by
  rw [incidences_eq_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H _
  simp only [cellMass,incidenceEntry,Finset.sum_boole]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma cellMass_training_mono (S X : Finset (ℙ K V)) (hS : S⊆X)
    {δ : ℝ} (hδ : 0≤δ) (H : ℙ K (Dual K V)) : cellMass S δ H≤cellMass X δ H := by
  apply mul_le_mul_of_nonneg_left _ hδ
  exact Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hS))

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
theorem thin_hyperplanes (X S : Finset (ℙ K V)) (hS : S⊆X) (hS0 : S.Nonempty)
    (hret : X.card≤4*S.card) (T : Finset (ℙ K (Dual K V)))
    {τ : ℝ} (hτ : 0<τ)
    (hdensity : (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card) :
    let T₀ := T.filter fun H => cellMass S ((Nat.card K:ℝ)/S.card) H≤8*τ
    (T.card:ℝ)/2≤T₀.card := by
  dsimp only
  let δ : ℝ := (Nat.card K:ℝ)/S.card
  let T₀ := T.filter fun H => cellMass S δ H≤8*τ
  let T₁ := T.filter fun H => ¬cellMass S δ H≤8*τ
  have hn : (0:ℝ)<S.card := Nat.cast_pos.mpr hS0.card_pos
  have hδ : 0≤δ := div_nonneg (Nat.cast_nonneg _) hn.le
  have hsum : (∑H∈T,cellMass S δ H)≤4*τ*T.card := by
    calc
      _ ≤ ∑H∈T,cellMass X δ H := Finset.sum_le_sum fun H _ => cellMass_training_mono S X hS hδ H
      _ = ((Nat.card K:ℝ)*(incidences X T:ℝ))/S.card := by rw [sum_cellMass];dsimp [δ];ring
      _ ≤ (τ*X.card*T.card)/S.card := div_le_div_of_nonneg_right hdensity hn.le
      _ ≤ 4*τ*T.card := by
        apply (div_le_iff₀ hn).mpr
        have hr : (X.card:ℝ)≤4*(S.card:ℝ) := by exact_mod_cast hret
        have h := mul_le_mul_of_nonneg_left hr (mul_nonneg hτ.le (Nat.cast_nonneg T.card))
        nlinarith only [h]
  have ht : (8*τ)*(T₁.card:ℝ)≤∑H∈T,cellMass S δ H := by
    calc
      _ = ∑_H∈T₁,8*τ := by simp;ring
      _ ≤ ∑H∈T₁,cellMass S δ H := Finset.sum_le_sum fun H hH =>
        (lt_of_not_ge (Finset.mem_filter.mp hH).2).le
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun H _ _ => mul_nonneg hδ (Nat.cast_nonneg _))
  have he : (T₀.card:ℝ)+T₁.card=T.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s:=T)
      (fun H => cellMass S δ H≤8*τ)
  change (T.card:ℝ)/2≤T₀.card
  nlinarith only [ht,hsum,he,hτ]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma thin_subset_exceptional {J : Type*} [Fintype J]
    (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (hS : S.Nonempty)
    (T : Finset (ℙ K (Dual K V))) {τ : ℝ} (hτ : 8*τ≤4/5) :
    (T.filter fun H => cellMass S ((Nat.card K:ℝ)/S.card) H≤8*τ)⊆exceptional S C := by
  intro H hH
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,none,?_⟩
  have hn : (S.card:ℝ)≠0 := (Nat.cast_pos.mpr hS.card_pos).ne'
  simp only [threshold,deviation,familyCell,div_self hn]
  have hh := (Finset.mem_filter.mp hH).2.trans hτ
  have hn0 : cellMass S ((Nat.card K:ℝ)/S.card) H-1≤0 := by linarith only [hh]
  rw [abs_of_nonpos hn0]
  linarith only [hh]

end SharpRamseyFive.ScoreGeometry

end OAI
