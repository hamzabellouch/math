import OAI.Geometry.Kahler.BaseCompositionJets

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open Set Filter Topology MeasureTheory
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma regularizedLog_positive_jet_bound (a : ℝ) {ε R A B : ℝ} (he : ε ≠ 0)
    (hR : 0 < R) (hA : 0 ≤ A) (hB : 0 ≤ B) {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Base → ℂ) (c : Base) (t : ℝ),
      AnalyticOnNhd ℂ f (Metric.ball c R) → ‖f c‖ ≤ A → 0 < t → t ≤ 1 →
      (∀ x ∈ Metric.ball c R, ‖f x-f c‖ ≤ B*t) →
      ‖iteratedFDeriv ℝ n (regularizedLog a ε ∘ f) c‖ ≤ C*t := by
  let radius : NNReal := ⟨A, hA⟩
  obtain ⟨C,hC,hCb⟩ := smooth_jet_bound_compact (regularizedLog_contDiff a he)
    (isCompact_closedBall (0:ℂ) (radius : ℝ)) n
  let D : ℝ := 1+∑ i ∈ Finset.range (n+1), cauchyJetConstant i*B/(R/2)^i
  have hterm (i : ℕ) : 0 ≤ cauchyJetConstant i*B/(R/2)^i := by
    exact div_nonneg (mul_nonneg (cauchyJetConstant_pos i).le hB) (by positivity)
  have hD : 1 ≤ D := by
    have hh := Finset.sum_nonneg (s := Finset.range (n+1)) (fun i _ => hterm i)
    dsimp [D]; linarith
  have hDb (i : ℕ) (hi : i ≤ n) : cauchyJetConstant i*B/(R/2)^i ≤ D := by
    have hh := Finset.single_le_sum (s := Finset.range (n+1)) (fun j _ => hterm j)
      (show i ∈ Finset.range (n+1) by simp; omega)
    dsimp [D]; linarith
  refine ⟨n.factorial*C*D^n,by positivity,?_⟩
  intro f c t hf hfc ht ht1 hb
  have hfn : ContDiffOn ℝ n f (Metric.ball c R) := (hf.contDiffOn Metric.isOpen_ball.uniqueDiffOn).restrict_scalars ℝ
  have hh := norm_composition_jet_linear Metric.isOpen_ball (Metric.mem_ball_self hR) hn hfn
    ((regularizedLog_contDiff a he).of_le (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))) hD ht ht1
    (fun i hi => hCb i hi (f c) (by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hfc))
    (fun i hi hin => ?_)
  · exact hh
  rw [analytic_real_jet_norm (hf c (Metric.mem_ball_self hR)) i]
  have hbound := analytic_positive_jet_bound hR (mul_nonneg hB ht.le) hf hb (by omega : 0 < i)
  apply hbound.trans
  calc cauchyJetConstant i*(B*t)/(R/2)^i = (cauchyJetConstant i*B/(R/2)^i)*t := by ring
       _ ≤ D*t := mul_le_mul_of_nonneg_right (hDb i hin) ht.le

end PinchedHartogs.BaseConstruction

end

end OAI
