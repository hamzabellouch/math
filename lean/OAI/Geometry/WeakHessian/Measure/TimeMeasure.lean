import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.InclusionDoubleDualSurjective
import OAI.Geometry.WeakHessian.LocalBounds.SquareControl

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian

abbrev timeMeasure : Measure ℝ := volume.restrict (Icc (0:ℝ) 1)
abbrev ControlSpace := Lp ℝ 2 timeMeasure

def intervalVector (s t : Time) : ControlSpace :=
  indicatorConstLp 2 measurableSet_Icc (measure_ne_top _ _) (1:ℝ)
    (s := Icc (s:ℝ) (t:ℝ))

def intervalFunctional (s t : Time) : ControlSpace →L[ℝ] ℝ :=
  innerSL ℝ (intervalVector s t)

lemma intervalFunctional_apply (s t : Time) (u : ControlSpace) (hst : s ≤ t) :
    intervalFunctional s t u = ∫ r in (s:ℝ)..(t:ℝ), u r := by
  rw [intervalFunctional, innerSL_apply_apply, intervalVector,
    L2.inner_indicatorConstLp_one]
  rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr
    (Icc_subset_Icc s.2.1 t.2.2), integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hst]

lemma norm_intervalVector_sq (s t : Time) (hst : s ≤ t) :
    ‖intervalVector s t‖^2 = (t:ℝ)-(s:ℝ) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [intervalVector, L2.real_inner_indicatorConstLp_one_indicatorConstLp_one,
    inter_self, Measure.real]
  rw [Measure.restrict_apply measurableSet_Icc,
    inter_eq_left.mpr (Icc_subset_Icc s.2.1 t.2.2), Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hst)]

def HasControlBound {X : Type*} [MetricSpace X] (γ : Curve X) (B : ℝ) : Prop :=
  ∃ u : ControlSpace, ‖u‖ ≤ B ∧ ∀ s t : Time, s ≤ t →
    dist (γ s) (γ t) ≤ intervalFunctional s t u

variable {X : Type*} [MetricSpace X]

lemma HasControlBound.nonneg {γ : Curve X} {B : ℝ} (h : HasControlBound γ B) : 0 ≤ B := by
  obtain ⟨u,hu,_⟩ := h
  exact (norm_nonneg u).trans hu

lemma HasControlBound.dist_sq_le {γ : Curve X} {B : ℝ} (h : HasControlBound γ B)
    (s t : Time) : dist (γ s) (γ t)^2 ≤ |(s:ℝ)-(t:ℝ)| * B^2 := by
  have H (s t : Time) (hst : s ≤ t) :
      dist (γ s) (γ t)^2 ≤ ((t:ℝ)-(s:ℝ))*B^2 := by
    obtain ⟨u, hu, hud⟩ := h
    have hd := hud s t hst
    have hn := norm_inner_le_norm (𝕜 := ℝ) (intervalVector s t) u
    have hI : intervalFunctional s t u ≤ ‖intervalVector s t‖*B := by
      exact (le_abs_self _).trans (hn.trans (mul_le_mul_of_nonneg_left hu (norm_nonneg _)))
    have hsq := sq_le_sq₀ dist_nonneg (mul_nonneg (norm_nonneg _) ((norm_nonneg u).trans hu)) |>.mpr (hd.trans hI)
    simpa only [mul_pow, norm_intervalVector_sq s t hst] using hsq
  rcases le_total s t with hst | hts
  · simpa only [abs_sub_comm (s:ℝ), abs_of_nonneg (sub_nonneg.mpr (show (s:ℝ) ≤ (t:ℝ) from hst))] using H s t hst
  · simpa only [dist_comm (γ t), abs_of_nonneg (sub_nonneg.mpr (show (t:ℝ) ≤ (s:ℝ) from hts))] using H t s hts

lemma HasControlBound.squareControl {γ : Curve X} {B : ℝ} (h : HasControlBound γ B) :
    ∃ a : ℝ → ℝ, IsSquareControl γ a ∧
      (∫ r in Icc (0:ℝ) 1, (a r)^2) ≤ B^2 := by
  obtain ⟨u,hu,hud⟩ := h
  have habs : MemLp (fun r => |u r|) 2 timeMeasure := by
    simpa only [Real.norm_eq_abs] using (Lp.memLp u).norm
  refine ⟨fun r => |u r|, ⟨(Lp.stronglyMeasurable u).measurable.abs, habs,
    ae_of_all _ (fun r => abs_nonneg _), ?_⟩, ?_⟩
  · intro s t hst
    have HD := hud s t hst
    rw [intervalFunctional_apply s t u hst] at HD
    exact HD.trans (intervalIntegral.integral_mono_on hst
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hst).mpr
        (((Lp.memLp u).integrable (by norm_num)).mono_measure
          (Measure.restrict_mono (Icc_subset_Icc s.2.1 t.2.2) le_rfl)))
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hst).mpr
        ((habs.integrable (by norm_num)).mono_measure
          (Measure.restrict_mono (Icc_subset_Icc s.2.1 t.2.2) le_rfl)))
      (fun r _ => le_abs_self _))
  · have heq : (∫ r in Icc (0:ℝ) 1, |u r|^2) = ‖u‖^2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      congr 1
      ext r
      simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs]
    rw [heq]
    exact (sq_le_sq₀ (norm_nonneg u) ((norm_nonneg u).trans hu)).mpr hu

lemma isClosed_hasControlBound (B : ℝ) : IsClosed {γ : Curve X | HasControlBound γ B} := by
  apply isSeqClosed_iff_isClosed.mp
  intro γ g hγ hg
  let K : ℕ → Set ControlSpace := fun n => Metric.closedBall 0 B ∩
    ⋂ (s : Time) (t : Time) (_ : s ≤ t),
      {u | dist (g s) (g t) - 1/(n+1:ℝ) ≤ intervalFunctional s t u}
  have hKcl : ∀ n, IsClosed (K n) := fun n => Metric.isClosed_closedBall.inter
    (isClosed_iInter fun s => isClosed_iInter fun t => isClosed_iInter fun _ =>
      isClosed_le continuous_const (intervalFunctional s t).continuous)
  have hKconv : ∀ n, Convex ℝ (K n) := fun n => (convex_closedBall (0:ControlSpace) B).inter
    (convex_iInter fun s => convex_iInter fun t => convex_iInter fun _ =>
      (convex_Ici _).linear_preimage (intervalFunctional s t).toLinearMap)
  have hKanti : Antitone K := by
    intro n k hnk u hu
    refine ⟨hu.1, mem_iInter.mpr fun s => mem_iInter.mpr fun t => mem_iInter.mpr fun hst => ?_⟩
    have H := mem_iInter.mp (mem_iInter.mp (mem_iInter.mp hu.2 s) t) hst
    have heps : 1/(k+1:ℝ) ≤ 1/(n+1:ℝ) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hnk 1
    dsimp at H ⊢
    linarith
  have hKne : ∀ n, (K n).Nonempty := by
    intro n
    obtain ⟨k,hk⟩ := (Metric.tendsto_atTop.mp hg (1/(2*(n+1:ℝ))) (by positivity))
    obtain ⟨u,hu,hud⟩ := hγ k
    refine ⟨u, by simpa only [Metric.mem_closedBall, dist_zero_right] using hu,
      mem_iInter.mpr fun s => mem_iInter.mpr fun t => mem_iInter.mpr fun hst => ?_⟩
    have hs := ContinuousMap.dist_apply_le_dist s (f := γ k) (g := g)
    have ht := ContinuousMap.dist_apply_le_dist t (f := γ k) (g := g)
    have he := hk k le_rfl
    have hd := (dist_triangle (g s) (γ k s) (g t)).trans
      (add_le_add le_rfl (dist_triangle (γ k s) (γ k t) (g t)))
    rw [dist_comm (g s) (γ k s)] at hd
    have heps : 1/(n+1:ℝ) = 2*(1/(2*(n+1:ℝ))) := by
      field_simp [show (n:ℝ)+1 ≠ 0 by positivity]
    have hi := hud s t hst
    dsimp
    linarith
  obtain ⟨u,hu⟩ := WeakHessianFunctional.nonempty_iInter_closed_convex hKne hKcl hKconv hKanti
    (Metric.isBounded_closedBall.subset inter_subset_left)
  refine ⟨u, by simpa only [Metric.mem_closedBall, dist_zero_right] using (mem_iInter.mp hu 0).1,
    fun s t hst => ?_⟩
  have Hall : ∀ n : ℕ, dist (g s) (g t) - 1/(n+1:ℝ) ≤ intervalFunctional s t u :=
    fun n => mem_iInter.mp (mem_iInter.mp (mem_iInter.mp (mem_iInter.mp hu n).2 s) t) hst
  have htend : Tendsto (fun n : ℕ => dist (g s) (g t)-1/(n+1:ℝ)) atTop
      (𝓝 (dist (g s) (g t))) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := dist (g s) (g t))).sub tendsto_one_div_add_atTop_nhds_zero_nat
  exact le_of_tendsto htend (Eventually.of_forall Hall)

end WeakHessian

open scoped BoundedContinuousFunction

end
end InlinedFile0

end OAI
