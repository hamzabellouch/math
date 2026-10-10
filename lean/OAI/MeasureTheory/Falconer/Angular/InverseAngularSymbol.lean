import OAI.MeasureTheory.Falconer.Estimates.SeededInverse
import OAI.MeasureTheory.Falconer.Angular.AngularJetSymbol
import OAI.MeasureTheory.Falconer.Estimates.QuadraticBudget

namespace OAI

/-! # Actual inverse coefficients preserve the finite angular symbol budget

The geometric coefficient and the newly differentiated multiplier are
normalized by one constant chosen before all descriptor lists and scales.
The derivative scale stays fixed; only the consumed order is removed.
-/

namespace Falconer
open Set Metric
open scoped ContDiff

/-- Simultaneous bounds for all required derivatives of every geometric
coefficient, independent of the descriptor labels and initial orders. -/
theorem inverse_seed_coefficient_budget (m j K : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      ∀ (k : ι → MaskJetIndex (m+3))
        (a : ((MaskJetExpansion.seed k).inverse m j).index),
      ∀ t ≤ K, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ t (((MaskJetExpansion.seed k).inverse m j).term a).coefficient w‖ ≤ C := by
  classical
  have hs : IsCompact (Sphere (m+3)) := isCompact_sphere (0 : Space (m+3)) 1
  choose c hc hb using fun t : Fin (K+1) =>
    MaskJetExpansion.inverse_seed_coefficient_derivatives m j t.val hs
  let C := 1+∑ t : Fin (K+1), c t
  have hsum : 0 ≤ ∑ t : Fin (K+1), c t := Finset.sum_nonneg (fun t _ => hc t)
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro ι _ _ k a t ht w
  let q : Fin (K+1) := ⟨t,Nat.lt_succ_of_le ht⟩
  have hsingle : c q ≤ ∑ t : Fin (K+1), c t :=
    Finset.single_le_sum (fun t _ => hc t) (Finset.mem_univ q)
  exact (hb q ι k a w w.property).trans (by dsimp [C]; linarith)

/-- This is the angular multiplier appearing in an actual separated inverse
term. Taking order `p` requires exactly `p+K` derivatives of the old multiplier. -/
theorem inverse_angular_symbol (m j K : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      ∀ (k : ι → MaskJetIndex (m+3))
        (a : ((MaskJetExpansion.seed k).inverse m j).index)
        (p : MaskJetIndex (m+3)) (L : ℕ) (f : Space (m+3) → ℂ),
      ContDiff ℝ ∞ f → ∀ D : ℝ, 1 ≤ D → p.order+K ≤ L →
      (∀ t ≤ L, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ t f w‖ ≤ D^t) →
      let g := fun z => (((MaskJetExpansion.seed k).inverse m j).term a).coefficient z *
        p.scaledValue D⁻¹ f z
      ContDiff ℝ ∞ (normalizedAngular A g) ∧
      (∀ t ≤ K, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ t (normalizedAngular A g) w‖ ≤ D^t) ∧
      ChartSymbolControl K
        (fun (_ : Space (m+3)) (w : Sphere (m+3)) => normalizedAngular A g w) 1 D := by
  obtain ⟨C,hC,hcoeff⟩ := inverse_seed_coefficient_budget m j K
  obtain ⟨H,hH,hnormalize⟩ := ambient_angular_normalization (m+1) K
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hpow : 1 ≤ (2 : ℝ)^K := one_le_pow₀ (by norm_num)
  have hP : 1 ≤ (2 : ℝ)^K*C :=
    (show 1 = (1:ℝ)*1 by ring).le.trans (mul_le_mul hpow hC (by norm_num) (by positivity))
  have hA : 1 ≤ H*((2 : ℝ)^K*C) :=
    (show 1 = (1:ℝ)*1 by ring).le.trans (mul_le_mul hH hP (by norm_num) (by positivity))
  refine ⟨H*((2 : ℝ)^K*C),hA,?_⟩
  intro ι _ _ k a p L f hf D hD hLK hb g
  have hg : ContDiff ℝ ∞ g :=
    (((MaskJetExpansion.seed k).inverse m j).term a).coefficient_smooth.mul
      (p.scaledValue_contDiff D⁻¹ f hf)
  have hp := p.angular_budget_shift f hf hD (by omega) hb
  have hbudget : ∀ t ≤ K, ∀ w : Sphere (m+3),
      ‖iteratedFDeriv ℝ t g w‖ ≤ ((2 : ℝ)^K*C)*D^t := by
    intro t ht w
    have hprod := mixed_product_uniform_bound_at
      ((((MaskJetExpansion.seed k).inverse m j).term a).coefficient_smooth.contDiffAt)
      ((p.scaledValue_contDiff D⁻¹ f hf).contDiffAt) hC0.le
      (pow_nonneg (zero_le_one.trans hD) t) t
      (fun l hl => hcoeff ι k a l (hl.trans ht) w)
      (fun l hl => (hp l (by omega) w).trans (pow_le_pow_right₀ hD hl))
    exact hprod.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) ht) hC0.le)
      (pow_nonneg (zero_le_one.trans hD) t))
  exact hnormalize g hg ((2 : ℝ)^K*C) D (zero_lt_one.trans_le hP) hD hbudget

end Falconer

end OAI
