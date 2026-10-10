import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeKernelChartGaussian

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FlatHeat
lemma heat_time_bound {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (z : V) :
    heat (a*t) z ≤ ((4*Real.pi*a)⁻¹)^2/t^2 := by
  have he : Real.exp (-‖z‖^2/(4*(a*t))) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity))
  calc
    _ ≤ (4*Real.pi*(a*t))⁻¹^2*1 := mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ = _ := by simp only [mul_one,← mul_assoc,mul_inv, mul_pow,inv_pow,div_eq_mul_inv]
end TamingCompatibility.GeometricHilbert.FlatHeat

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldVolume ManifoldLocalization ManifoldKernelExtension Set MeasureTheory Filter
open scoped Manifold ContDiff Topology NNReal
variable {X B : Type*} [MetricSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [NormedRing B]

def pushedHeatKernel (p : X) (K : ℝ → Space × Space → B) (t : ℝ) (x y : X) : B :=
  if 0 < t then push p (K t) (y,x) else 0

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [SecondCountableTopology B]

omit [IsManifold Model ∞ X] in
lemma pushedHeatKernel_measurable (p : X) (L : Set Space) (hL : IsCompact L)
    (hLt : L ⊆ (extChartAt Model p).target) (K : ℝ → Space × Space → B)
    (hsupp : ∀ t, Function.support (K t) ⊆ L ×ˢ L)
    (hKc : ∀ t, 0 < t → ∀ z, ContinuousAt (fun v : ℝ × (Space × Space) => K v.1 v.2) (t,z)) :
    VolterraKernel.MeasurableKernel (pushedHeatKernel p K) := by
  let : MeasurableSpace B := borel B
  let : BorelSpace B := ⟨rfl⟩
  have hc : ContinuousOn (fun v : ℝ × (X × X) => push p (K v.1) (v.2.2,v.2.1)) {v | 0 < v.1} := by
    intro v hv
    have hh := push_joint_continuousAt p K (L ×ˢ L) (hL.prod hL)
      (fun _ h => ⟨hLt h.1,hLt h.2⟩) hsupp v.1 (hKc v.1 hv) (v.2.2,v.2.1)
    exact (hh.comp (f := fun w : ℝ × (X × X) => (w.1,(w.2.2,w.2.1))) (continuousAt_fst.prodMk (continuousAt_snd.snd.prodMk continuousAt_snd.fst))).continuousWithinAt
  have hm := hc.measurable_piecewise (continuousOn_const (c := (0 : B)))
    (isOpen_lt continuous_const continuous_fst).measurableSet
  have he : {v : ℝ × (X × X) | 0 < v.1}.piecewise
      (fun v => push p (K v.1) (v.2.2,v.2.1)) (fun _ => (0 : B)) =
      (fun v => pushedHeatKernel p K v.1 v.2.1 v.2.2) := by
    funext v
    by_cases hv : 0 < v.1
    · simp only [Set.piecewise,Set.mem_ofPred_eq,hv,ite_eq_left,pushedHeatKernel]
    · simp only [Set.piecewise,Set.mem_ofPred_eq,hv,ite_false,pushedHeatKernel]
  rw [he] at hm
  exact hm.stronglyMeasurable

variable [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (A : FiniteCharts X)
include hs ht in

lemma pushedHeatKernel_bound (p : X) (L : Set Space) (hL : IsCompact L)
    (hLt : L ⊆ (extChartAt Model p).target) (C : ℝ≥0)
    (hLip : LipschitzOnWith C (extChartAt Model p).symm L)
    (D : ℝ) (hD : 0 ≤ D) (hDb : ∀ z ∈ L, chartDensity J α p z ≤ D)
    (K : ℝ → Space × Space → B) (hsupp : ∀ t, Function.support (K t) ⊆ L ×ˢ L)
    (hKc : ∀ t, 0 < t → ∀ z, ContinuousAt (fun v : ℝ × (Space × Space) => K v.1 v.2) (t,z))
    (n : ℕ) (T : ℝ) {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    (hK : ∀ t, 0 < t → ∀ q y, ‖K t (q,y)‖ ≤ M*FlatHeat.heat (a*t) (y-q)) :
    ∃ H : ℝ, VolterraKernel.HeatBound (geometricVolume A J α) n T H (pushedHeatKernel p K) := by
  let c := (max (C:ℝ) 1)^n*M*(2^n*(4+4*(8*a)^n*(n.factorial : ℝ)))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let b := ((4*Real.pi*(2*a))⁻¹)^2
  have hb : 0 ≤ b := sq_nonneg _
  let H := c*b+D*c
  have hsup : c*b ≤ H := le_add_of_nonneg_right (mul_nonneg hD hc)
  have hint : D*c ≤ H := le_add_of_nonneg_left (mul_nonneg hc hb)
  have hcont (t : ℝ) (htp : 0 < t) : Continuous (K t) := by
    rw [continuous_iff_continuousAt]
    intro z
    exact (hKc t htp z).comp (continuousAt_const.prodMk continuousAt_id)
  refine ⟨H,⟨pushedHeatKernel_measurable p L hL hLt K hsupp hKc,add_nonneg (mul_nonneg hc hb) (mul_nonneg hD hc),?_,?_,?_,?_,?_⟩⟩
  · intro t htpos x y
    rw [pushedHeatKernel,ite_eq_left htpos.1,VolterraBounds.weight_symm n t x y]
    have hh := push_weighted_gaussian p L C hLip (K t) (hsupp t) n ha htpos.1 hM (hK t htpos.1) y x
    calc
      _ ≤ c*FlatHeat.heat (2*a*t) (extChartAt Model p x-extChartAt Model p y) := hh
      _ ≤ c*(b/t^2) := mul_le_mul_of_nonneg_left (FlatHeat.heat_time_bound (by positivity : 0 < 2*a) htpos.1 _) hc
      _ = (c*b)/t^2 := by ring
      _ ≤ H/t^2 := div_le_div_of_nonneg_right hsup (sq_nonneg t)
  · intro t htpos x
    have hh := push_gaussian_col J α hs ht A p L hL hLt C hLip D hD hDb (K t) (hcont t htpos.1)
      (hsupp t) n ha htpos.1 hM (hK t htpos.1) x
    simpa only [pushedHeatKernel,ite_eq_left htpos.1,VolterraBounds.weight_symm n t x] using hh.1
  · intro t htpos x
    have hh := push_gaussian_col J α hs ht A p L hL hLt C hLip D hD hDb (K t) (hcont t htpos.1)
      (hsupp t) n ha htpos.1 hM (hK t htpos.1) x
    simpa only [pushedHeatKernel,ite_eq_left htpos.1,VolterraBounds.weight_symm n t x] using hh.2.trans hint
  · intro t htpos y
    have hh := push_gaussian_row J α hs ht A p L hL hLt C hLip D hD hDb (K t) (hcont t htpos.1)
      (hsupp t) n ha htpos.1 hM (hK t htpos.1) y
    simpa only [pushedHeatKernel,ite_eq_left htpos.1,VolterraBounds.weight_symm n t _ y] using hh.1
  · intro t htpos y
    have hh := push_gaussian_row J α hs ht A p L hL hLt C hLip D hD hDb (K t) (hcont t htpos.1)
      (hsupp t) n ha htpos.1 hM (hK t htpos.1) y
    simpa only [pushedHeatKernel,ite_eq_left htpos.1,VolterraBounds.weight_symm n t _ y] using hh.2.trans hint

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.VolterraKernel
open MeasureTheory Set VolterraBounds
variable {X B : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [NormedRing B]
variable (μ : Measure X)

omit [SecondCountableTopology X] in
lemma HeatBound.finset_sum {ι : Type*} (s : Finset ι) (N : ℕ) (T : ℝ)
    (C : ι → ℝ) (K : ι → Kernel (X := X) (B := B))
    (hK : ∀ i ∈ s, HeatBound μ N T (C i) (K i)) :
    HeatBound μ N T (∑ i ∈ s, C i) (fun t x y => ∑ i ∈ s, K i t x y) := by
  have hm : MeasurableKernel (fun t x y => ∑ i ∈ s, K i t x y) :=
    s.stronglyMeasurable_fun_sum (fun i hi => (hK i hi).measurable)
  have hp (t : ℝ) (ht : 0 < t) (x y : X) :
      weight N t x y*‖∑ i ∈ s, K i t x y‖ ≤ ∑ i ∈ s, weight N t x y*‖K i t x y‖ := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (weight_pos N ht x y).le
  have hr (t : ℝ) (ht : t ∈ Ioc 0 T) (x : X) :
      Integrable (fun y => weight N t x y*‖∑ i ∈ s, K i t x y‖) μ := by
    have hint := integrable_finsetSum s (fun i hi => (hK i hi).row_int t ht x)
    apply hint.mono' ((weight_continuous N t x).aestronglyMeasurable.mul
      ((hm.comp_measurable (measurable_const.prodMk (measurable_const.prodMk measurable_id))).norm.aestronglyMeasurable))
    filter_upwards [] with y
    change ‖weight N t x y*‖∑ i ∈ s, K i t x y‖‖ ≤ ∑ i ∈ s, weight N t x y*‖K i t x y‖
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (weight_pos N ht.1 x y).le (norm_nonneg _))]
    exact hp t ht.1 x y
  have hc (t : ℝ) (ht : t ∈ Ioc 0 T) (y : X) :
      Integrable (fun x => weight N t x y*‖∑ i ∈ s, K i t x y‖) μ := by
    have hint := integrable_finsetSum s (fun i hi => (hK i hi).col_int t ht y)
    have hw : Continuous (fun x => weight N t x y) := by unfold weight; fun_prop
    apply hint.mono' (hw.aestronglyMeasurable.mul
      ((hm.comp_measurable (measurable_const.prodMk (measurable_id.prodMk measurable_const))).norm.aestronglyMeasurable))
    filter_upwards [] with x
    change ‖weight N t x y*‖∑ i ∈ s, K i t x y‖‖ ≤ ∑ i ∈ s, weight N t x y*‖K i t x y‖
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (weight_pos N ht.1 x y).le (norm_nonneg _))]
    exact hp t ht.1 x y
  refine ⟨hm,Finset.sum_nonneg (fun i hi => (hK i hi).nonneg),?_,hr,?_,hc,?_⟩
  · intro t ht x y
    calc
      _ ≤ ∑ i ∈ s, weight N t x y*‖K i t x y‖ := hp t ht.1 x y
      _ ≤ ∑ i ∈ s, C i/t^2 := Finset.sum_le_sum (fun i hi => (hK i hi).sup t ht x y)
      _ = _ := by rw [Finset.sum_div]
  · intro t ht x
    calc
      _ ≤ ∫ y, ∑ i ∈ s, weight N t x y*‖K i t x y‖ ∂μ :=
        integral_mono (hr t ht x) (integrable_finsetSum s (fun i hi => (hK i hi).row_int t ht x)) (hp t ht.1 x)
      _ = ∑ i ∈ s, ∫ y, weight N t x y*‖K i t x y‖ ∂μ :=
        integral_finsetSum s (fun i hi => (hK i hi).row_int t ht x)
      _ ≤ _ := Finset.sum_le_sum (fun i hi => (hK i hi).row t ht x)
  · intro t ht y
    calc
      _ ≤ ∫ x, ∑ i ∈ s, weight N t x y*‖K i t x y‖ ∂μ :=
        integral_mono (hc t ht y) (integrable_finsetSum s (fun i hi => (hK i hi).col_int t ht y)) (fun x => hp t ht.1 x y)
      _ = ∑ i ∈ s, ∫ x, weight N t x y*‖K i t x y‖ ∂μ :=
        integral_finsetSum s (fun i hi => (hK i hi).col_int t ht y)
      _ ≤ _ := Finset.sum_le_sum (fun i hi => (hK i hi).col t ht y)

end TamingCompatibility.GeometricHilbert.VolterraKernel

end
end

end

end OAI
