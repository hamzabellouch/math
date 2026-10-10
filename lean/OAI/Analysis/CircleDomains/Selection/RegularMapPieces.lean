import OAI.Analysis.CircleDomains.Sobolev.InverseOnDifferentiation
import Mathlib.MeasureTheory.Function.Jacobian

namespace OAI

/-! A planar map with invertible derivatives splits into countably many
measurable pieces with quantitative forward and inverse Lipschitz bounds. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

 def linearInverseApproxRadius (A : ℂ →L[ℝ] ℂ) : ℝ≥0 :=
  (2*(‖A.inverse‖₊+1))⁻¹

lemma linearInverseApproxRadius_ne_zero (A : ℂ →L[ℝ] ℂ) :
    linearInverseApproxRadius A ≠ 0 := by
  unfold linearInverseApproxRadius
  apply inv_ne_zero
  positivity

lemma linearInverseApproxRadius_lt (e : ℂ ≃L[ℝ] ℂ) :
    linearInverseApproxRadius (e : ℂ →L[ℝ] ℂ) < ‖(e.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ := by
  unfold linearInverseApproxRadius
  rw [ContinuousLinearMap.inverse_equiv]
  have hN : 0 < ‖(e.symm : ℂ →L[ℝ] ℂ)‖₊ := by exact_mod_cast e.symm.norm_pos
  apply (inv_lt_inv₀ (by positivity) hN).mpr
  calc
    _ < ‖(e.symm : ℂ →L[ℝ] ℂ)‖₊+1 := lt_add_one _
    _ ≤ (‖(e.symm : ℂ →L[ℝ] ℂ)‖₊+1)+(‖(e.symm : ℂ →L[ℝ] ℂ)‖₊+1) :=
      le_add_of_nonneg_right (by positivity)
    _ = _ := (two_mul _).symm

lemma regular_map_measurable_pieces {F : ℂ → ℂ} {DF : ℂ → ℂ →L[ℝ] ℂ}
    {S : Set ℂ} (hS : MeasurableSet S) (hne : S.Nonempty)
    (hd : ∀ p ∈ S, HasFDerivAt F (DF p) p)
    (hi : ∀ p ∈ S, (DF p).IsInvertible) :
    ∃ (B : ℕ → Set ℂ) (L K : ℕ → ℝ≥0),
      (∀ n, MeasurableSet (B n)) ∧ Pairwise (Disjoint on B) ∧ (⋃ n, B n) = S ∧
      ∀ n, LipschitzOnWith (L n) F (B n) ∧ AntilipschitzWith (K n) ((B n).domRestrict F) := by
  obtain ⟨t, A, htDisj, htMeas, htCover, htApprox, hA⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt F S DF
      (fun p hp => (hd p hp).hasFDerivWithinAt) linearInverseApproxRadius
      linearInverseApproxRadius_ne_zero
  have hAi (n : ℕ) : (A n).IsInvertible := by
    obtain ⟨p, hp, hAp⟩ := hA hne n
    rw [hAp]
    exact hi p hp
  choose e he using hAi
  let B : ℕ → Set ℂ := fun n => S ∩ t n
  let L : ℕ → ℝ≥0 := fun n => ‖A n‖₊+linearInverseApproxRadius (A n)
  let K : ℕ → ℝ≥0 := fun n =>
    (‖((e n).symm : ℂ →L[ℝ] ℂ)‖₊⁻¹-linearInverseApproxRadius (A n))⁻¹
  refine ⟨B, L, K, (fun n => hS.inter (htMeas n)), ?_, ?_, ?_⟩
  · exact fun i j hij => (htDisj hij).mono inter_subset_right inter_subset_right
  · simp only [B, ← inter_iUnion, inter_eq_left.mpr htCover]
  · intro n
    refine ⟨lipschitzOnWith_iff_restrict.mpr (htApprox n).lipschitz, ?_⟩
    have hh := htApprox n
    rw [← he n] at hh
    dsimp only [K, B]
    rw [← he n]
    exact hh.antilipschitz (Or.inr (linearInverseApproxRadius_lt (e n)))

end CircleDomainRigidity

end

end OAI
