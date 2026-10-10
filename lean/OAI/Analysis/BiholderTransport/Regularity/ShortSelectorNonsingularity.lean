import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.EuclideanUpper
import OAI.Analysis.BiholderTransport.LinearAlgebra.DiagonalCostConvexity
import OAI.Analysis.BiholderTransport.Coordinates.ShortLocalMinimum
import OAI.Analysis.BiholderTransport.Contact.SmoothSupportSemibound
import OAI.Analysis.BiholderTransport.LinearAlgebra.EnvelopeKernelHessian

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma second_fderiv_partial_snd {C : E×E → ℝ} {a b : E}
    (hC : ContDiffAt ℝ 2 C (a,b)) (v w:E) :
    fderiv ℝ (fderiv ℝ (fun z => C (a,z))) b v w =
      fderiv ℝ (fderiv ℝ C) (a,b) (0,v) (0,w) := by
  have hg : ContDiffAt ℝ 2 (fun z:E => (a,z)) b := contDiffAt_const.prodMk contDiffAt_id
  have hD : fderiv ℝ (fun z:E => (a,z)) = fun _ =>
      (0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E) := by
    funext z
    exact ((hasFDerivAt_const a z).prodMk (hasFDerivAt_id z)).fderiv
  rw [second_fderiv_comp_with_acceleration hC hg,hD]
  rw [show fderiv ℝ (fun _ : E => (0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)) b=0 from
    (hasFDerivAt_const _ b).fderiv]
  simp only [ContinuousLinearMap.prod_apply,zero_apply,
    ContinuousLinearMap.id_apply,map_zero,add_zero]

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma exists_chart_cost_kernel_gap {a:M} {x:Model n}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    let C := fun q:Model n×Model n => chartCost a
      ((extChartAt 𝓘(ℝ,Model n) a).symm q.1) q.2
    ∃ m>0, ∀ᶠ q in 𝓝 (x,x), ContDiffAt ℝ 2 C q ∧
      ∀ d:Model n,m*‖d‖^2≤fderiv ℝ (fderiv ℝ C) q (0,d) (0,d) := by
  let : NormedAddCommGroup (Model n →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (Model n →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  dsimp only
  let F := fun y:Model n => chartCost (n := n) a ((extChartAt 𝓘(ℝ,Model n) a).symm y)
  have hc := chartCost_pair_contDiffAt_diagonal hx
  have hH : ContinuousAt (fun q:Model n×Model n => fderiv ℝ (fderiv ℝ (F q.1)) q.2) (x,x) :=
    (ContDiffAt.partial_snd_fderiv_two (f := F) hc).continuousAt
  obtain ⟨k,hk,hpos⟩ := chartCost_diagonal_coercive hx
  have hdiff : ContinuousAt (fun q:Model n×Model n =>
      fderiv ℝ (fderiv ℝ (F q.1)) q.2-fderiv ℝ (fderiv ℝ (F x)) x) (x,x) :=
    hH.sub continuousAt_const
  have hnorm := hdiff.norm
  have hn : ∀ᶠ q:Model n×Model n in 𝓝 (x,x),
      ‖fderiv ℝ (fderiv ℝ (F q.1)) q.2-fderiv ℝ (fderiv ℝ (F x)) x‖ < k/2 := by
    apply hnorm.eventually_lt continuousAt_const
    simpa only [Pi.sub_apply,Prod.fst,Prod.snd,sub_self,ContinuousLinearMap.opNorm_zero] using half_pos hk
  refine ⟨k/2,half_pos hk,?_⟩
  filter_upwards [hn,(hc.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eventually (by simp)] with q hq hreg
  refine ⟨hreg,fun d => ?_⟩
  rw [←second_fderiv_partial_snd hreg d d]
  have hb := bilinear_diag_sub_bound (fderiv ℝ (fderiv ℝ (F q.1)) q.2)
    (fderiv ℝ (fderiv ℝ (F x)) x) d
  have hh := hpos d
  have hm := mul_le_mul_of_nonneg_right hq.le (sq_nonneg ‖d‖)
  have ha := (abs_le.mp hb).1
  change k/2*‖d‖^2≤fderiv ℝ (fderiv ℝ (F q.1)) q.2 d d
  linarith only [hh,hm,ha]

lemma actual_short_selector_injective_near {a:M} {x:Model n}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ∃ m>0, ∀ᶠ q:Model n×Model n in 𝓝 (x,x),
      ∀ t : ℝ, 0 < t → ∀ u : M → ℝ, Continuous u →
      ∀ Y:Model n → Model n,∀ R:Model n →L[ℝ] Model n,
      Y q.2=q.1 → HasFDerivAt Y R q.2 →
      let χ := extChartAt 𝓘(ℝ,Model n) a
      let G := fun z:Model n => hopfLax t u (χ.symm z)
      (∀ᶠ z in 𝓝 q.2,G z=u (χ.symm (Y z))+chartCost a (χ.symm (Y z)) z/t) →
      (∀ᶠ z in 𝓝 q.2,DifferentiableAt ℝ G z) →
      ∀ b : ℝ, t*b < m →
      (∀ d:Model n,fderiv ℝ (fderiv ℝ G) q.2 d d≤b*‖d‖^2) →
      Function.Injective R := by
  obtain ⟨m,hm,H⟩ := exists_chart_cost_kernel_gap hx
  refine ⟨m,hm,?_⟩
  filter_upwards [H] with q hq
  intro t ht u hu Y R hY hR
  dsimp only
  intro hcontact hd b hb hupp
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let G := fun z:Model n => hopfLax t u (χ.symm z)
  let C := fun z:Model n×Model n => t⁻¹*chartCost a (χ.symm z.1) z.2
  have hc : ContDiffAt ℝ 2 C (Y q.2,q.2) := by
    rw [hY]
    exact contDiffAt_const.mul hq.1
  have hs : ∀ᶠ z in 𝓝 q.2,∀ᶠ v in 𝓝 z,
      G v≤G z+C (Y z,v)-C (Y z,z) := by
    filter_upwards [hcontact] with z hz
    apply Filter.Eventually.of_forall
    intro v
    have hv := hopfLax_le hu t (χ.symm v) (χ.symm (Y z))
    rw [cost_symm] at hv
    change G v≤u (χ.symm (Y z))+chartCost a (χ.symm (Y z)) v/t at hv
    change G z=u (χ.symm (Y z))+chartCost a (χ.symm (Y z)) z/t at hz
    dsimp only [C]
    rw [hz]
    convert hv using 1
    ring
  apply envelope_selector_injective_of_hessian_gap hc hR hd hs
    (show b < m/t from (lt_div_iff₀ ht).mpr (by linarith only [hb])) hupp
  intro d
  rw [hY]
  change (m/t)*‖d‖^2≤fderiv ℝ (fderiv ℝ (fun z:Model n×Model n =>
    t⁻¹*chartCost a (χ.symm z.1) z.2)) q (0,d) (0,d)
  rw [second_fderiv_const_mul]
  have HH := mul_le_mul_of_nonneg_left (hq.2 d) (inv_nonneg.mpr ht.le)
  convert HH using 1
  first | rfl | ring

end WeakMTWTransport

end

end OAI
