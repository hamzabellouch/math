import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

noncomputable def compositionDerivativeCost (g : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ c : OrderedFinpartition n, ∏ j, ‖iteratedDeriv (c.partSize j) g x‖

 theorem compositionDerivativeCost_nonneg (g : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    0 ≤ compositionDerivativeCost g n x := by
  unfold compositionDerivativeCost
  positivity

 theorem compositionDerivativeCost_continuous {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (n : ℕ) : Continuous (compositionDerivativeCost g n) := by
  apply continuous_finsetSum
  intro c _
  apply continuous_finsetProd
  intro j _
  exact (hg.continuous_iteratedDeriv _ (by exact_mod_cast (le_top : (c.partSize j:ℕ∞) ≤ ⊤))).norm

 theorem composition_derivative_scale {f : ℝ → ℂ} {g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (n : ℕ) (x : ℝ)
    (hb : ∀ k ≤ n, ‖iteratedDeriv k f (g x)‖ ≤ C*D^k) :
    ‖iteratedDeriv n (f ∘ g) x‖ ≤ compositionDerivativeCost g n x * (C*D^n) := by
  rw [iteratedDeriv_scomp_eq_sum_orderedFinpartition hf.contDiffAt hg.contDiffAt
    (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))]
  rw [compositionDerivativeCost,Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro c _
  rw [norm_smul, norm_prod]
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
  exact (hb c.length c.length_le).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD c.length_le) hC)

noncomputable def weightedCompositionCost (w : ℝ → ℂ) (g : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), (n.choose k:ℝ) * ‖iteratedDeriv k w x‖ * compositionDerivativeCost g (n-k) x

 theorem weightedCompositionCost_nonneg (w : ℝ → ℂ) (g : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    0 ≤ weightedCompositionCost w g n x := by
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
    (compositionDerivativeCost_nonneg _ _ _)

 theorem weightedCompositionCost_continuous {w : ℝ → ℂ} {g : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hg : ContDiff ℝ ∞ g) (n : ℕ) :
    Continuous (weightedCompositionCost w g n) := by
  apply continuous_finsetSum
  intro k _
  exact (continuous_const.mul (hw.continuous_iteratedDeriv k
    (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤))).norm).mul
      (compositionDerivativeCost_continuous hg (n-k))

 theorem weighted_composition_derivative_scale {w f : ℝ → ℂ} {g : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (n : ℕ) (x : ℝ)
    (hb : ∀ k ≤ n, ‖iteratedDeriv k f (g x)‖ ≤ C*D^k) :
    ‖iteratedDeriv n (fun x => w x * f (g x)) x‖ ≤
      weightedCompositionCost w g n x * (C*D^n) := by
  have hwn : ContDiffAt ℝ n w x := (hw.of_le (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))).contDiffAt
  have hfn : ContDiffAt ℝ n (f ∘ g) x :=
    ((hf.comp hg).of_le (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))).contDiffAt
  change ‖iteratedDeriv n (fun y => w y * (f ∘ g) y) x‖ ≤ _
  rw [iteratedDeriv_fun_mul hwn hfn,weightedCompositionCost,Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  simp only [norm_mul,Complex.norm_natCast]
  have hc := composition_derivative_scale hf hg hC hD (n-k) x
    (fun l hl => hb l (hl.trans (Nat.sub_le _ _)))
  have hp : C*D^(n-k) ≤ C*D^n :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (Nat.sub_le _ _)) hC
  calc
    _ ≤ (n.choose k:ℝ) * ‖iteratedDeriv k w x‖ *
        (compositionDerivativeCost g (n-k) x * (C*D^n)) := by
      gcongr
      exact hc.trans (mul_le_mul_of_nonneg_left hp (compositionDerivativeCost_nonneg _ _ _))
    _ = _ := by ring

 theorem compact_weighted_composition_scale {w : ℝ → ℂ} {g : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hg : ContDiff ℝ ∞ g)
    {K : Set ℝ} (hK : IsCompact K) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (f : ℝ → ℂ), ContDiff ℝ ∞ f →
      ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ k ≤ n, ∀ y, ‖iteratedDeriv k f y‖ ≤ C*D^k) →
      ∀ x ∈ K, ‖iteratedDeriv n (fun y => w y * f (g y)) x‖ ≤ A*C*D^n := by
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn
    (weightedCompositionCost_continuous hw hg n).continuousOn
  refine ⟨max 0 B,le_max_left _ _,?_⟩
  intro f hf C D hC hD hb x hx
  have hA : weightedCompositionCost w g n x ≤ max 0 B :=
    (le_abs_self _).trans ((hB x hx).trans (le_max_right _ _))
  calc
    _ ≤ weightedCompositionCost w g n x * (C*D^n) :=
      weighted_composition_derivative_scale hw hf hg hC hD n x (fun k hk => hb k hk _)
    _ ≤ max 0 B * (C*D^n) := mul_le_mul_of_nonneg_right hA (by positivity)
    _ = _ := by ring

end PlanarFalconer

end OAI
