import Mathlib
import OAI.Geometry.WeakHessian.Entropy.TruncatedLog
import OAI.Geometry.WeakHessian.HeatFlow.HeatPositiveDerivative

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X}

lemma cheegerHeat_tendsto_joint
    (hfin : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m)
    {ι : Type*} {l : Filter ι} {θ : ι → ℝ} {u : ι → Lp ℝ 2 m}
    {T : ℝ} {v : Lp ℝ 2 m} (hT : 0 < T)
    (hθ : Tendsto θ l (𝓝 T)) (hu : Tendsto u l (𝓝 v)) :
    Tendsto (fun z => cheegerHeat h (θ z) (u z)) l (𝓝 (cheegerHeat h T v)) := by
  have hc : ContinuousAt (fun s => cheegerHeat h s v) T :=
    ((cheegerHeat_continuousOn hfin h v) T hT.le).continuousAt (Ici_mem_nhds hT)
  have hz : ∀ᶠ z in l, 0 ≤ θ z :=
    (hθ.eventually (eventually_gt_nhds hT)).mono fun _ hz => hz.le
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hb : ∀ᶠ z in l, dist (cheegerHeat h (θ z) (u z)) (cheegerHeat h T v) ≤
      dist (u z) v + dist (cheegerHeat h (θ z) v) (cheegerHeat h T v) := by
    filter_upwards [hz] with z hz
    have h1 := dist_triangle (cheegerHeat h (θ z) (u z))
      (cheegerHeat h (θ z) v) (cheegerHeat h T v)
    have h2 := cheegerHeat_contractive h hz (u z) v
    exact h1.trans (add_le_add h2 le_rfl)
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) hb
  simpa only [zero_add,Function.comp_def] using
    (tendsto_iff_dist_tendsto_zero.mp hu).add
      (tendsto_iff_dist_tendsto_zero.mp (hc.tendsto.comp hθ))

lemma cheegerHeat_diagonal_hasDerivAt
    (hfin : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m)
    {θ : ℝ → ℝ} {u : ℝ → Lp ℝ 2 m} {s τ : ℝ} {v : Lp ℝ 2 m}
    (hθ : HasDerivAt θ τ s) (hu : HasDerivAt u v s) (hpos : 0 < θ s) :
    ∃ L : Lp ℝ 2 m,
      (cheeger_closedQuadraticEnergy h).IsFormGenerator (cheegerHeat h (θ s) (u s)) L ∧
      HasDerivAt (fun z => cheegerHeat h (θ z) (u z))
        (cheegerHeat h (θ s) v + τ • L) s := by
  obtain ⟨L,hL,hLD⟩ := cheegerHeat_deriv_at_positive hfin h (u s) hpos
  refine ⟨L,hL,?_⟩
  have ha : HasDerivAt (fun z => cheegerHeat h (θ z) (u z-u s))
      (cheegerHeat h (θ s) v) s := by
    apply hasDerivAt_iff_tendsto_slope.mpr
    have H := cheegerHeat_tendsto_joint hfin h hpos
      (hθ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hu.tendsto_slope
    apply H.congr'
    exact Eventually.of_forall fun z => by
      simp only [slope_def_module,sub_self,map_zero,sub_zero,map_smul]
  have hb : HasDerivAt (fun z => cheegerHeat h (θ z) (u s)) (τ • L) s :=
    hLD.scomp s hθ
  apply (ha.add hb).congr_of_eventuallyEq
  exact Eventually.of_forall fun z => by
    simp only [Pi.add_apply,map_sub,sub_add_cancel]

lemma cheegerHeat_diagonal_entropy_hasDerivAt
    (hfin : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m)
    {θ : ℝ → ℝ} {u : ℝ → Lp ℝ 2 m} {s τ : ℝ} {v : Lp ℝ 2 m}
    (hθ : HasDerivAt θ τ s) (hu : HasDerivAt u v s) (hpos : 0 < θ s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L : Lp ℝ 2 m,
      (cheeger_closedQuadraticEnergy h).IsFormGenerator (cheegerHeat h (θ s) (u s)) L ∧
      HasDerivAt (fun z => cheegerHeat h (θ z) (u z))
        (cheegerHeat h (θ s) v + τ • L) s ∧
      HasDerivAt (fun z => ∫ x, regularizedEntropy ε (cheegerHeat h (θ z) (u z) x) ∂m)
        ⟪cheegerHeat h (θ s) v + τ • L,
          (regularizedLog_memLp hε (cheegerHeat h (θ s) (u s))).toLp
            (fun x => regularizedLog ε (cheegerHeat h (θ s) (u s) x))⟫_ℝ s := by
  obtain ⟨L,hL,hD⟩ := cheegerHeat_diagonal_hasDerivAt hfin h hθ hu hpos
  refine ⟨L,hL,hD,?_⟩
  have H := (regularizedEntropy_hasFDeriv hε (cheegerHeat h (θ s) (u s))).comp_hasDerivAt s hD
  convert! H using 1
  exact real_inner_comm _ _

end WeakHessian

end
end

end OAI
