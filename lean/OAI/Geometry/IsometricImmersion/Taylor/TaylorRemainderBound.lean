import OAI.Geometry.IsometricImmersion.Taylor.UniformTaylorDenominator
import Mathlib.Analysis.Calculus.Taylor

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem iteratedDerivWithin_Icc_eq_of_contDiffAt {f : ℝ → ℝ} {a b t : ℝ}
    (hab : a < b) (hf : ContDiffAt ℝ ∞ f t) (ht : t ∈ Icc a b) (k : ℕ) :
    iteratedDerivWithin k f (Icc a b) t = iteratedDeriv k f t := by
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDeriv_eq_iteratedFDeriv,
    iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Icc hab)
      (hf.of_le (WithTop.coe_le_coe.mpr le_top)) ht]

theorem zero_jets_remainder_bound {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, ContDiffAt ℝ ∞ f t) (N : ℕ)
    (hzero : ∀ k < N, iteratedDeriv k f a = 0) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ t ∈ Icc a b, |iteratedDeriv N f t| ≤ C)
    {t : ℝ} (ht : t ∈ Icc a b) : |f t| ≤ C * (t - a)^N := by
  cases N with
  | zero => simpa only [iteratedDeriv_zero, pow_zero, mul_one] using hbound t ht
  | succ n =>
    rcases eq_or_lt_of_le hab with hab | hab
    · subst b
      have hta : t = a := le_antisymm ht.2 ht.1
      subst t
      have hfa : f a = 0 := hzero 0 (by omega)
      simp [hfa]
    have hwithin (j : ℕ) (s : ℝ) (hs : s ∈ Icc a b) :
        iteratedDerivWithin j f (Icc a b) s = iteratedDeriv j f s :=
      iteratedDerivWithin_Icc_eq_of_contDiffAt hab (hf s hs) hs j
    have hTaylor : taylorWithinEval f n (Icc a b) a t = 0 := by
      rw [taylor_within_apply]
      apply Finset.sum_eq_zero
      intro j hj
      rw [hwithin j a ⟨le_rfl, hab.le⟩, hzero j (Finset.mem_range.mp hj)]
      simp
    have hdiff : ContDiffOn ℝ (n + 1) f (Icc a b) :=
      fun s hs => ((hf s hs).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffWithinAt
    have hrem := taylor_mean_remainder_bound hab.le hdiff ht
      (fun s hs => by rw [hwithin (n + 1) s hs, Real.norm_eq_abs]; exact hbound s hs)
    rw [hTaylor, sub_zero, Real.norm_eq_abs] at hrem
    apply hrem.trans
    have hfac : (1 : ℝ) ≤ (n.factorial : ℝ) := by
      exact_mod_cast (show 1 ≤ n.factorial from Nat.factorial_pos n)
    exact div_le_self (mul_nonneg hC (pow_nonneg (sub_nonneg.mpr ht.1) _)) hfac

theorem qResidual_time_jet_le_fullJet {g : MetricField} {U : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I))
    (x t : ℝ) (hx : x ∈ I) (hpU : (![x, t] : Coord) ∈ U)
    (hxx : covHessian g P ![x, t] 0 0 ≠ 0) (N : ℕ) :
    |iteratedDeriv N (fun s => qResidual g P ![x, s]) t| ≤
      ‖iteratedFDeriv ℝ N (qResidual g P) ![x, t]‖ := by
  have hD := comparisonDomain_isOpen hg hU hI hP
  have hR := qResidual_contDiffOn hg hU hI hP
  have hp := mem_comparisonDomain hx hpU hxx
  rw [verticalJet_slice hD hR x N t hp]
  have hb := norm_verticalJet_fullJet_le hR hD hp N 0
  rw [Nat.zero_add, norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hb
  exact hb

end SmoothLocal.Taylor

end

end OAI
