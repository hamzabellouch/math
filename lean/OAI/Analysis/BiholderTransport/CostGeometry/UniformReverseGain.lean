import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.UniformFixedCrossing
import OAI.Analysis.BiholderTransport.Regularity.UniformMixedBound
import OAI.Analysis.BiholderTransport.Regularity.UniformIntervalCrossing
import OAI.Analysis.BiholderTransport.Coordinates.ReverseIsotropicGain

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_uniform_reverse_divided_gain :
    ∃ c>0, ∀ᶠ z : ℝ×ℝ in 𝓝 (1,1), z.1≤z.2 → z.2<1 →
      ∀ x y : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      ∀ q : TangentSpace 𝓘(ℝ,Model n) y,
      p∈minimizingVectors x → q∈injectivityDomain y →
      riemannianExp x (z.1 • p)=y → riemannianExp y q=x →
      ∃ R : TangentSpace 𝓘(ℝ,Model n) y → TangentSpace 𝓘(ℝ,Model n) x,
        ContDiffAt ℝ ∞ R q ∧ R q=0 ∧
        (∀ᶠ w in 𝓝 q, riemannianExp x (R w)=riemannianExp y w) ∧
        ∀ w : TangentSpace 𝓘(ℝ,Model n) y,
          c*(z.2-z.1)*‖w‖^2 ≤
            hessianValue x (z.1 • p) (fderiv ℝ R q w)/z.1-
              hessianValue x (z.2 • p) (fderiv ℝ R q w)/z.2 := by
  obtain ⟨h,hh,hh1,Hsplit⟩ := exists_actual_uniform_regular_split (n := n) (M := M)
  obtain ⟨c,hc,C,hC,HC⟩ := fixedJoinMiddle_uniform_interval_crossing hh hh1 Hsplit
  obtain ⟨B,hB,HB⟩ := normalEndpointMixedOperator_uniform_bound hh hh1 Hsplit
  have Hnear : Tendsto (fun z : ℝ×ℝ => h/z.1) (𝓝 (1,1)) (𝓝 h) := by
    have H : ContinuousAt (fun z : ℝ×ℝ => h/z.1) (1,1) :=
      continuousAt_const.div continuousAt_fst (by norm_num)
    simpa only [div_one] using H.tendsto
  have Hpos : ∀ᶠ z : ℝ×ℝ in 𝓝 (1,1), h<z.1 :=
    continuousAt_fst.eventually (eventually_gt_nhds hh1)
  refine ⟨c/B^2,div_pos hc (sq_pos_of_pos hB),?_⟩
  filter_upwards [HC,Hnear.eventually HB,Hpos] with z hz hnorm hhs
  intro hst ht1 x y p q hp hq hpx hqy
  have hs : 0<z.1 := hh.trans hhs
  have ht : 0<z.2 := hs.trans_le hst
  have hs1 : z.1<1 := hst.trans_lt ht1
  have hps := contracted_minimizer_mem_injectivityDomain hp hs hs1
  have hpt := contracted_minimizer_mem_injectivityDomain hp ht ht1
  have hbound : z.1*‖normalEndpointMixedOperator x y (h/z.1) (z.1 • p)‖≤B := by
    have H := hnorm x (z.1 • p) (injectivityDomain_subset_minimizingVectors x hps)
    rw [hpx] at H
    calc
      _ ≤ 1*‖normalEndpointMixedOperator x y (h/z.1) (z.1 • p)‖ := by
        gcongr
      _ ≤ B := by simpa only [one_mul] using H
  obtain ⟨R,hR,hR0,hRi,HR⟩ := exists_reverse_exp_divided_isotropic_gain hh hhs
    (hhs.trans_le hst) hps hpt hq hpx hqy hB
    (mul_nonneg hc.le (sub_nonneg.mpr hst))
    (fun v => (hz hhs ht1 hst x p hp v).1) hbound
  refine ⟨R,hR,hR0,hRi,?_⟩
  intro w
  convert HR w using 1
  ring

end WeakMTWTransport

end

end OAI
