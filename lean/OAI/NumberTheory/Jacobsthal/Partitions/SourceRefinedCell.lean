import OAI.NumberTheory.Jacobsthal.Estimates.RefinedDiscardBound
import OAI.NumberTheory.Jacobsthal.Estimates.RefinementRewardMargin
import OAI.NumberTheory.Jacobsthal.Sieve.RefinementPrimeCongruences

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseRefinement
open ErdosInverseCells ErdosInverseSampling ErdosInversePrimeBin ErdosInverseEuler ErdosInverseBoxHeight

theorem source_refined_cell (K gamma : ℝ) (h : ℕ) (hK : 0 ≤ K) (hg : 0 < gamma) :
    ∀ᶠ z : ℝ in atTop,∀ U theta : ℝ,0 ≤ U → U ≤ (sourceW z)^K → 0 ≤ theta → theta ≤ 1 →
      ∀ (s : Sample (primeBin U theta) h) (P C : Finset ℕ) (a : ℕ → ℕ)
        (witness : (ℕ × ℕ) → ℕ → Prop) (S : ℝ),
        0 < P.card → 0 < S → S/sourceZ z ≤ (C.card : ℝ) →
        gamma/2 ≤ selectedFraction (P.product C) (primeBin U theta) witness h s →
        ∃ i : RefinementLabel (sampleModulus (primeBin U theta) h s),
          S/(sourceZ z)^3 ≤ ((refinementCell C a (sampleModulus (primeBin U theta) h s) i).card : ℝ) ∧
          (refinementCell C a (sampleModulus (primeBin U theta) h s) i).Nonempty ∧
          (gamma/4)*((refinementCell C a (sampleModulus (primeBin U theta) h s) i).card : ℝ) <
            ∑ q ∈ refinementCell C a (sampleModulus (primeBin U theta) h s) i,
              rowReward P (primeBin U theta) witness h s q := by
  filter_upwards [source_sample_modulus_square K 1 h hK zero_lt_one,
    sourceZ_tendsto_atTop.eventually_ge_atTop (8/gamma)] with z hmod hZlarge
  intro U theta hU0 hUtop htheta htheta1 s P C a witness S hP hS hC hreward
  let W := sampleModulus (primeBin U theta) h s
  have hWpos : 0 < W := sampleModulus_pos _ h s
    (fun u hu => ((mem_primeBin hU0 htheta u).mp hu).1.pos)
  let : NeZero W := ⟨hWpos.ne'⟩
  have hZ : 0 < sourceZ z := Real.exp_pos _
  have hCpos : 0 < C.card := by exact_mod_cast (div_pos hS hZ).trans_le hC
  have hInv : 1/sourceZ z ≤ gamma/8 := by
    apply (div_le_iff₀ hZ).mpr
    have hh := (div_le_iff₀ hg).mp hZlarge
    nlinarith
  have hWsq : (W : ℝ)^2 ≤ sourceZ z := by
    simpa only [Real.rpow_one] using hmod U theta hU0 hUtop htheta htheta1 s
  have hDiscard := refined_discard_bound C a W S (sourceZ z) gamma hS.le hZ hC hWsq hInv
  have hMass : (gamma/2)*(C.card : ℝ) ≤ ∑ q ∈ C,rowReward P (primeBin U theta) witness h s q := by
    rw [rowReward_sum P C (primeBin U theta) witness h s hP hCpos]
    exact mul_le_mul_of_nonneg_right hreward (Nat.cast_nonneg _)
  obtain ⟨i,hlarge,hdense⟩ := dense_fiber_after_count_discard C (refinementLabel a W) (S/(sourceZ z)^3)
    (gamma/2) (gamma/4) (gamma/8) hCpos (by positivity) (by linarith)
    (rowReward P (primeBin U theta) witness h s)
    (fun q _ => (rowReward_bounds P (primeBin U theta) witness h s q hP).2) hMass hDiscard
  have hnR : (0 : ℝ) < (refinementCell C a W i).card :=
    (div_pos hS (pow_pos hZ 3)).trans_le hlarge
  have hn : 0 < (refinementCell C a W i).card := by exact_mod_cast hnR
  exact ⟨i,hlarge,Finset.card_pos.mp hn,hdense⟩

end ErdosInverseRefinement

end

end Erdos970

end OAI
