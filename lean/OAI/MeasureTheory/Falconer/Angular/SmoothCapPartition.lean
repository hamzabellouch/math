import OAI.MeasureTheory.Falconer.Angular.SphereModel
import OAI.MeasureTheory.Falconer.Fourier.SmoothReciprocal
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

namespace OAI

/-!
# A finite smooth cap partition on the actual sphere

These are ambient smooth functions restricted to the sphere. The denominator
is extended smoothly away from the sphere, where the covering lower bound
need not hold. Quantitative derivative and overlap estimates are separate
from this qualitative construction.
-/

namespace Falconer
open Set Metric
open scoped ContDiff
attribute [local instance] Classical.propDecidable

noncomputable def capBump {d : ℕ} (δ : ℝ) (hδ : 0 < δ) (c : Sphere d) :
    ContDiffBump (c : Space d) where
  rIn := δ/2
  rOut := δ
  rIn_pos := half_pos hδ
  rIn_lt_rOut := half_lt_self hδ

theorem smooth_cap_partition_on_net (d : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist (w : Space d) (c : Space d) ≤ δ/2) :
    ∃ F : Sphere d → Space d → ℝ,
      (∀ c, ContDiff ℝ ∞ (F c)) ∧
      (∀ w : Sphere d, ∑ c ∈ S, F c w = 1) ∧
      (∀ c ∈ S, ∀ w : Sphere d, 0 ≤ F c w ∧ F c w ≤ 1) ∧
      (∀ c ∈ S, ∀ x : Space d, F c x ≠ 0 → ‖x-(c : Space d)‖ ≤ δ) := by
  let g : Space d → ℝ := fun x => ∑ c ∈ S, capBump δ hδ c x
  have hg : ContDiff ℝ ∞ g := ContDiff.sum (fun c _ => (capBump δ hδ c).contDiff)
  have hg0 (x : Space d) : 0 ≤ g x :=
    Finset.sum_nonneg (fun c _ => (capBump δ hδ c).nonneg)
  have hg1 (w : Sphere d) : 1 ≤ g w := by
    obtain ⟨c,hc,hcw⟩ := hcover w
    have hb : capBump δ hδ c w = 1 :=
      (capBump δ hδ c).one_of_mem_closedBall (mem_closedBall.mpr hcw)
    calc
      1 = capBump δ hδ c w := hb.symm
      _ ≤ g w := Finset.single_le_sum (fun c _ => (capBump δ hδ c).nonneg) hc
  let F : Sphere d → Space d → ℝ := fun c x =>
    capBump δ hδ c x * smoothReciprocal 1 zero_lt_one (g x)
  have hrec (w : Sphere d) : g w * smoothReciprocal 1 zero_lt_one (g w) = 1 :=
    smoothReciprocal_eq zero_lt_one (by simpa only [abs_of_nonneg (hg0 w)] using hg1 w)
  have hrecval (w : Sphere d) : smoothReciprocal 1 zero_lt_one (g w) = (g w)⁻¹ := by
    have hn : g w ≠ 0 := ne_of_gt (zero_lt_one.trans_le (hg1 w))
    apply (mul_left_cancel₀ hn)
    rw [hrec w,mul_inv_cancel₀ hn]
  refine ⟨F,?_,?_,?_,?_⟩
  · intro c
    exact (capBump δ hδ c).contDiff.mul ((smoothReciprocal_contDiff 1 zero_lt_one).comp hg)
  · intro w
    simpa only [F,← Finset.sum_mul] using hrec w
  · intro c hc w
    dsimp only [F]
    rw [hrecval]
    have hb : capBump δ hδ c w ≤ g w :=
      Finset.single_le_sum (fun c _ => (capBump δ hδ c).nonneg) hc
    constructor
    · exact mul_nonneg (capBump δ hδ c).nonneg (inv_nonneg.mpr (hg0 w))
    · have hn : 0 < g w := zero_lt_one.trans_le (hg1 w)
      exact (mul_inv_le_iff₀ hn).mpr (by simpa only [one_mul] using hb)
  · intro c _ x hx
    have hb : capBump δ hδ c x ≠ 0 := (mul_ne_zero_iff.mp hx).1
    have hm : x ∈ ball (c : Space d) δ := by
      change x ∈ ball (c : Space d) (capBump δ hδ c).rOut
      rw [← (capBump δ hδ c).support_eq]
      exact hb
    exact (mem_ball_iff_norm.mp hm).le

theorem finite_smooth_cap_partition (d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (S : Finset (Sphere d)) (F : Sphere d → Space d → ℝ),
      (∀ c, ContDiff ℝ ∞ (F c)) ∧
      (∀ w : Sphere d, ∑ c ∈ S, F c w = 1) ∧
      (∀ c ∈ S, ∀ w : Sphere d, 0 ≤ F c w ∧ F c w ≤ 1) ∧
      (∀ c ∈ S, ∀ x : Space d, F c x ≠ 0 → ‖x-(c : Space d)‖ ≤ δ) := by
  have hs : IsCompact (sphere (0 : Space d) 1) := isCompact_sphere _ _
  obtain ⟨S,hS⟩ := hs.elim_finite_subcover
    (fun c : Sphere d => ball (c : Space d) (δ/2)) (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (half_pos hδ)⟩)
  obtain ⟨F,hF,hpartition,hbounds,hsupport⟩ := smooth_cap_partition_on_net d hδ S (by
    intro w
    obtain ⟨c,hc,hcw⟩ := mem_iUnion₂.mp (hS w.property)
    exact ⟨c,hc,(mem_ball.mp hcw).le⟩)
  exact ⟨S,F,hF,hpartition,hbounds,hsupport⟩

end Falconer

end OAI
