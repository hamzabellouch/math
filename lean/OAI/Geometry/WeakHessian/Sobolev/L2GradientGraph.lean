import Mathlib
import OAI.Geometry.WeakHessian.Transport.MapEvalReal
import OAI.Geometry.WeakHessian.LocalBounds.InclusionDoubleDualSurjective

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [MetricSpace X] [BorelSpace X] in
lemma eLpNorm_sub_tendsto_of_tendsto_Lp {u : ℕ → Lp ℝ 2 m} {v : Lp ℝ 2 m}
    (h : Tendsto u atTop (𝓝 v)) :
    Tendsto (fun n => eLpNorm (fun x => u n x - v x) 2 m) atTop (𝓝 0) := by
  have heq : (fun n => eLpNorm (fun x => u n x - v x) 2 m) =
      (fun n => ‖u n - v‖ₑ) := by
    funext n
    rw [Lp.enorm_def]
    exact (eLpNorm_congr_ae (Lp.coeFn_sub (u n) v)).symm
  rw [heq]
  simpa only [sub_self, enorm_zero] using (h.sub (tendsto_const_nhds (x := v))).enorm

def l2GradientGraph (m : Measure X) : Set (WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m)) :=
  {p | IsLocalWeakUpperGradient m p.fst p.snd}

lemma isClosed_l2GradientGraph : IsClosed (l2GradientGraph m) := by
  apply IsSeqClosed.isClosed
  intro u p hu hlim
  have hf := (WithLp.continuous_fst 2 (Lp ℝ 2 m) (Lp ℝ 2 m)).tendsto p |>.comp hlim
  have hg := (WithLp.continuous_snd 2 (Lp ℝ 2 m) (Lp ℝ 2 m)).tendsto p |>.comp hlim
  exact IsLocalWeakUpperGradient.of_l2_tendsto hu
    (fun n => Lp.memLp (u n).fst) (fun n => Lp.memLp (u n).snd)
    (Lp.memLp p.fst) (Lp.memLp p.snd)
    (eLpNorm_sub_tendsto_of_tendsto_Lp hf) (eLpNorm_sub_tendsto_of_tendsto_Lp hg)

lemma convex_l2GradientGraph : Convex ℝ (l2GradientGraph m) := by
  intro p hp q hq a b ha hb _hab
  have hpa := hp.const_mul a
  have hqb := hq.const_mul b
  have H := hpa.add hqb (fun o R _ => ((Lp.memLp p.fst).const_mul a).restrict (Metric.ball o R))
  apply H.congr_ae
  · change (fun x => a * p.fst x + b * q.fst x) =ᵐ[m] ⇑(a • p.fst + b • q.fst)
    filter_upwards [Lp.coeFn_add (a • p.fst) (b • q.fst),
      Lp.coeFn_smul a p.fst, Lp.coeFn_smul b q.fst] with x hsum hp hq
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hp, hq] using hsum.symm
  · change (fun x => |a| * p.snd x + |b| * q.snd x) =ᵐ[m] ⇑(a • p.snd + b • q.snd)
    filter_upwards [Lp.coeFn_add (a • p.snd) (b • q.snd),
      Lp.coeFn_smul a p.snd, Lp.coeFn_smul b q.snd] with x hsum hp hq
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hp, hq,
      abs_of_nonneg ha, abs_of_nonneg hb] using hsum.symm

lemma exists_upperGradient_of_bounded_l2 {fn Dn : ℕ → Lp ℝ 2 m} {f : Lp ℝ 2 m}
    (hn : ∀ n, IsLocalWeakUpperGradient m (fn n) (Dn n))
    (hf : Tendsto fn atTop (𝓝 f)) {B : ℝ} (hB : ∀ n, ‖Dn n‖ ≤ B) :
    ∃ D : Lp ℝ 2 m, IsLocalWeakUpperGradient m f D ∧ ‖D‖ ≤ B := by
  exact WeakHessianFunctional.exists_snd_of_tendsto_fst_of_bounded
    isClosed_l2GradientGraph convex_l2GradientGraph
    (u := fun n => WithLp.toLp 2 (fn n, Dn n)) hn hf hB

lemma isClosed_upperGradient_sublevel (B : ℝ) :
    IsClosed {f : Lp ℝ 2 m | ∃ D : Lp ℝ 2 m,
      IsLocalWeakUpperGradient m f D ∧ ‖D‖ ≤ B} := by
  apply IsSeqClosed.isClosed
  intro fn f hfn hf
  choose Dn hDn hB using hfn
  exact exists_upperGradient_of_bounded_l2 hDn hf hB

lemma exists_norm_minimal_upperGradient {f : Lp ℝ 2 m}
    (h : ∃ D : Lp ℝ 2 m, IsLocalWeakUpperGradient m f D) :
    ∃ D : Lp ℝ 2 m, IsLocalWeakUpperGradient m f D ∧
      ∀ E : Lp ℝ 2 m, IsLocalWeakUpperGradient m f E → ‖D‖ ≤ ‖E‖ := by
  let S : Set (Lp ℝ 2 m) := {D | IsLocalWeakUpperGradient m f D}
  have hScl : IsClosed S := by
    exact isClosed_l2GradientGraph.preimage
      ((WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 m) (Lp ℝ 2 m)).symm.continuous.comp
        (continuous_const.prodMk continuous_id))
  have hSc : Convex ℝ S := by
    intro D hD E hE a b ha hb hab
    have H := convex_l2GradientGraph (m := m)
      (x := WithLp.toLp 2 (f, D)) (y := WithLp.toLp 2 (f, E)) hD hE ha hb hab
    change IsLocalWeakUpperGradient m ⇑(a • f + b • f) ⇑(a • D + b • E) at H
    rwa [← add_smul, hab, one_smul] at H
  obtain ⟨D, hD, hnorm⟩ := exists_norm_eq_iInf_of_complete_convex h hScl.isComplete hSc (0 : Lp ℝ 2 m)
  refine ⟨D, hD, fun E hE => ?_⟩
  rw [zero_sub, norm_neg] at hnorm
  rw [hnorm]
  have hlow : BddBelow (Set.range fun w : S => ‖(0 : Lp ℝ 2 m) - w‖) := ⟨0, by
    rintro _ ⟨w, rfl⟩
    exact norm_nonneg _⟩
  calc
    _ ≤ ‖(0 : Lp ℝ 2 m) - E‖ := ciInf_le hlow (⟨E, hE⟩ : S)
    _ = ‖E‖ := by rw [zero_sub, norm_neg]

end WeakHessian

end
end InlinedFile0

end OAI
