import Mathlib

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma coordinate_metric_norm {a : M} {z : E}
    (hz : z ∈ (extChartAt 𝓘(ℝ,E) a).target)
    {g : E →L[ℝ] E →L[ℝ] ℝ}
    (hg : ∀ u v : E, g u v =
      inner ℝ ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,E) a).symm z) u)
        ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,E) a).symm z) v)) (v : E) :
    Real.sqrt (g v v) = ‖mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) a).symm z v‖ := by
  have hsrc := (extChartAt 𝓘(ℝ,E) a).map_target hz
  have hsrc' : (extChartAt 𝓘(ℝ,E) a).symm z ∈ (chartAt E a).source := by
    simpa only [extChartAt_source] using hsrc
  have heq := TangentBundle.symmL_trivializationAt (I := 𝓘(ℝ,E)) hsrc'
  rw [ModelWithCorners.range_eq_univ,mfderivWithin_univ] at heq
  have hinv : extChartAt 𝓘(ℝ,E) a ((extChartAt 𝓘(ℝ,E) a).symm z) = z :=
    (extChartAt 𝓘(ℝ,E) a).right_inv hz
  rw [hinv] at heq
  rw [hg,heq,real_inner_self_eq_norm_sq,Real.sqrt_sq_eq_abs,abs_norm]
  rfl

lemma coordinate_metric_chart_derivative_norm {a y : M}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) a).source)
    {g : E →L[ℝ] E →L[ℝ] ℝ}
    (hg : ∀ u v : E, g u v =
      inner ℝ ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).symmL ℝ y u)
        ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).symmL ℝ y v))
    (v : TangentSpace 𝓘(ℝ,E) y) :
    Real.sqrt (g (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) a) y v)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) a) y v)) = ‖v‖ := by
  let w : E := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) a) y v
  change Real.sqrt (g w w) = ‖v‖
  have hy' : y ∈ (chartAt E a).source := by simpa only [extChartAt_source] using hy
  have hbase : y ∈ (trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).baseSet := hy'
  have hv := (trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).symmL_continuousLinearMapAt (R := ℝ) hbase v
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hy'] at hv
  change (trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).symmL ℝ y w = v at hv
  rw [hg,hv,real_inner_self_eq_norm_sq,Real.sqrt_sq_eq_abs,abs_norm]

lemma coordinate_path_length {c : M} {γ : ℝ → M} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,E) 1 γ (Icc a b))
    (himg : MapsTo γ (Icc a b) (extChartAt 𝓘(ℝ,E) c).source)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ∀ t ∈ Icc a b, ∀ u v : E, g (extChartAt 𝓘(ℝ,E) c (γ t)) u v =
      inner ℝ ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) c).symmL ℝ (γ t) u)
        ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) c).symmL ℝ (γ t) v)) :
    pathELength 𝓘(ℝ,E) γ a b =
      ∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt (g (extChartAt 𝓘(ℝ,E) c (γ t))
        (deriv ((extChartAt 𝓘(ℝ,E) c) ∘ γ) t)
        (deriv ((extChartAt 𝓘(ℝ,E) c) ∘ γ) t))) := by
  rw [pathELength_eq_lintegral_mfderiv_Ioo,←restrict_Ioo_eq_restrict_Icc]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have ht' : t ∈ Icc a b := Ioo_subset_Icc_self ht
  have hγd := (hγ t ht').contMDiffAt (Icc_mem_nhds ht.1 ht.2) |>.mdifferentiableAt one_ne_zero
  have hsrc' : γ t ∈ (chartAt E c).source := by simpa only [extChartAt_source] using himg ht'
  have hχd := mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) hsrc'
  have hcomp := mfderiv_comp t hχd hγd
  rw [mfderiv_eq_fderiv] at hcomp
  have hval : deriv ((extChartAt 𝓘(ℝ,E) c) ∘ γ) t =
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) c) (γ t))
        (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t 1) := by
    change (fderiv ℝ ((extChartAt 𝓘(ℝ,E) c) ∘ γ) t) 1 = _
    exact congrArg (fun L : ℝ →L[ℝ] E => L 1) hcomp
  have hn := coordinate_metric_chart_derivative_norm (himg ht') (hg t ht')
    (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t 1)
  dsimp only
  rw [←ofReal_norm]
  congr 1
  rw [hval]
  exact hn.symm

lemma inverse_coordinate_path_length {c : M} {η : ℝ → E} {a b : ℝ}
    (hη : ContDiffOn ℝ 1 η (Icc a b))
    (himg : MapsTo η (Icc a b) (extChartAt 𝓘(ℝ,E) c).target)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ∀ t ∈ Icc a b, ∀ u v : E, g (η t) u v =
      inner ℝ ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) c).symmL ℝ
        ((extChartAt 𝓘(ℝ,E) c).symm (η t)) u)
        ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) c).symmL ℝ
        ((extChartAt 𝓘(ℝ,E) c).symm (η t)) v)) :
    pathELength 𝓘(ℝ,E) ((extChartAt 𝓘(ℝ,E) c).symm ∘ η) a b =
      ∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt (g (η t) (deriv η t) (deriv η t))) := by
  rw [pathELength_eq_lintegral_mfderiv_Ioo,←restrict_Ioo_eq_restrict_Icc]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have ht' : t ∈ Icc a b := Ioo_subset_Icc_self ht
  have hηd := (hη.contDiffAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt one_ne_zero
  have hφd : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) c).symm (η t) :=
    ((contMDiffOn_extChartAt_symm (n := ∞) c) _ (himg ht')).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds (himg ht')) |>.mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp t hφd (mdifferentiableAt_iff_differentiableAt.mpr hηd)
  have hval := congrArg (fun L => L (1:ℝ)) hcomp
  rw [mfderiv_eq_fderiv] at hval
  have hn := coordinate_metric_norm (himg ht') (hg t ht') (deriv η t)
  have hnval : ‖mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ((extChartAt 𝓘(ℝ,E) c).symm ∘ η) t 1‖ =
      ‖mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) c).symm (η t) (deriv η t)‖ :=
    congrArg (fun v : TangentSpace 𝓘(ℝ,E) ((extChartAt 𝓘(ℝ,E) c).symm (η t)) => ‖v‖) hval
  exact (ofReal_norm _).symm.trans (congrArg ENNReal.ofReal (hnval.trans hn.symm))

end WeakMTWTransport

end

end OAI
