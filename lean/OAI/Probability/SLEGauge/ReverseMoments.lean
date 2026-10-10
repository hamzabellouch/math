import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.ReverseGenerators

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped NNReal ENNReal Topology
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
open scoped ContDiff Manifold
noncomputable section
open Filter Topology
noncomputable section
open Complex Real Set Filter
open scoped Topology
noncomputable section
open scoped Topology
open MeasureTheory
noncomputable section
open Set Filter Real
open scoped Topology
namespace SLEExactGauge.ReverseDerivative
open _root_.OAI.SLEExactGauge.Localization BrownianCalculus ODEPath RationalStop
open MeasureTheory ProbabilityTheory
theorem expected_stopped_reverse_aux {a : ℝ} (ha : 1/4 < a)
    {W : Measure Driver} (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W)
    {H : ℝ} (hH : 0 ≤ H) (φ : State × ℝ → ℝ) (hφ : Continuous φ)
    (hK : IsCompact {x | φ x ≤ 2}) (hKO : {x | φ x ≤ 2} ⊆ domain)
    (v : State → ℝ → State) (hv : Continuous (Function.uncurry v))
    {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hbound : ∀ x b, ‖v x b‖ ≤ M)
    (hlip : ∀ b x y, ‖v x b-v y b‖ ≤ L*‖x-y‖)
    (hveq : ∀ x, φ x ≤ 2 → v x.1 x.2 = vector a x.1 x.2)
    (z : State) (hz : φ (z,0) < 1) :
    let g := fun b : Driver => ODEPath.flow v z b
    let τ := fun b : Driver => Exit (fun u => φ (g b u,b u.toNNReal)) 1 H
    ∀ t ≥ 0, (∫ b : Driver, test a (g b (min t (τ b))) (b (min t (τ b)).toNNReal) ∂W) ≤ test a z 0 := by
  let g := fun b : Driver => ODEPath.flow v z b
  let f := fun (b : ℝ≥0 → ℝ) u => φ (ODEPath.flow v z b u,b u.toNNReal)
  let τ := fun b : Driver => Exit (f b) 1 H
  have hg (b : Driver) := ODEPath.flow_solution v hv z b b.continuous
    hM hL (by linarith : 0 ≤ H+1) hbound hlip
  have hgc (b : Driver) : ContinuousOn (g b) (Icc 0 (H+1)) :=
    ODEPath.continuousOn_flow v hv z b b.continuous hM hL (by linarith) hbound hlip
  have hfc (b : Driver) : ContinuousOn (f b) (Icc 0 (H+1)) :=
    hφ.comp_continuousOn ((hgc b).prodMk ((b.continuous.comp continuous_real_toNNReal).continuousOn))
  have hfcH (b : Driver) : ContinuousOn (f b) (Icc 0 H) :=
    (hfc b).mono (Icc_subset_Icc_right (by linarith))
  have hf0 (b : Driver) : f b 0 < 1 := by
    simpa only [f,(hg b).1,Real.toNNReal_zero,map_zero] using hz
  have hτ (b : Driver) : 0 ≤ τ b ∧ τ b < H+1 := by
    have hb := exit_bounds hH (hfcH b) (R := 1)
    exact ⟨hb.1,lt_of_le_of_lt hb.2 (by linarith)⟩
  have hsafe (b : Driver) : ∀ u ∈ Icc 0 (τ b), f b u ≤ 1 :=
    bound_until_exit hH (hfcH b) (hf0 b)
  change ∀ t ≥ 0, (∫ b : Driver, test a (g b (min t (τ b))) (b (min t (τ b)).toNNReal) ∂W) ≤ test a z 0
  intro t ht
  let K : Set (State × ℝ) := {q | φ q ≤ 2}
  have hDo : IsOpen {q | φ q < 2} := isOpen_lt hφ continuous_const
  have hK1 : IsCompact {q | φ q ≤ 1} :=
    hK.of_isClosed_subset (isClosed_le hφ continuous_const) (fun q hq => by dsimp at *; linarith)
  obtain ⟨δ,hδ,hδD⟩ := hK1.exists_thickening_subset_open hDo (fun q hq => by dsimp at *; linarith)
  have hD (b : Driver) : ∃ δ > 0, ∀ u ∈ Icc 0 (τ b), ∀ x,
      ‖x-g b u‖ < δ → (x,b u.toNNReal) ∈ K := by
    refine ⟨δ,hδ,?_⟩
    intro u hu x hx
    have hi : φ (x,b u.toNNReal) < 2 := hδD (by
      apply Metric.mem_thickening_iff.mpr
      refine ⟨(g b u,b u.toNNReal),hsafe b u hu,?_⟩
      rw [dist_eq_norm]
      change max ‖x-g b u‖ ‖b u.toNNReal-b u.toNNReal‖ < δ
      simpa using hx)
    exact hi.le
  have mf (u : ℝ) : Measurable (fun b : ℝ≥0 → ℝ => f b u) :=
    hφ.measurable.comp ((ODEPath.measurable_flow v hv.measurable z u).prodMk (measurable_pi_apply _))
  have hfpast : ∀ s ≥ 0, ∀ b c : ℝ≥0 → ℝ,
      (∀ u : ℝ≥0, (u:ℝ) ≤ s → b u = c u) → f b s = f c s := by
    intro s hs b c hbc
    have hb := hbc s.toNNReal (by simpa only [Real.coe_toNNReal',max_eq_left hs] using le_refl s)
    simp only [f,ODEPath.flow_past v z hs hbc,hb]
  let S : ℝ≥0 → Set ((ℝ≥0 → ℝ) × (State × ℝ)) := fun r =>
    {q | (r:ℝ) < H ∧ Safe (f q.1) 1 r ∧ q.2 ∈ K}
  have mS : ∀ r, MeasurableSet (S r) := by
    intro r
    exact (MeasurableSet.const _).inter
      (((measurableSet_safe f mf 1 _).preimage measurable_fst).inter (hK.measurableSet.preimage measurable_snd))
  have hSpast : ∀ r b c, (∀ u ≤ r, b u = c u) → ∀ x, ((b,x) ∈ S r ↔ (c,x) ∈ S r) := by
    intro r b c hbc x
    have he : Safe (f b) 1 r ↔ Safe (f c) 1 r := safe_past hfpast r.coe_nonneg
      (fun u hu => hbc u hu)
    exact and_congr_right fun _ => and_congr_left fun _ => he
  have hSeq : ∀ (b : Driver) r x, (((b:ℝ≥0 → ℝ),x) ∈ S r ↔ (r:ℝ) < τ b ∧ x ∈ K) := by
    intro b r x
    change (_ ∧ _ ∧ _) ↔ (_ ∧ _)
    rw [lt_exit_iff hH (hfcH b) r.coe_nonneg]
    exact and_assoc.symm
  apply expected_stopped_local_grid hW ((Function.uncurry (test a))) K domain hK isOpen_domain hKO (contDiffOn_test a)
    v hv.measurable g z hL hM hbound hlip (fun b => (hg b).1) (fun b => (hg b).2)
    (fun b => hv.comp_continuousOn ((hgc b).prodMk
      ((b.continuous.comp continuous_real_toNNReal).continuousOn))) τ hτ hD
    (fun q hq => by rw [hveq q hq]; exact test_generator_nonpos ha (hKO hq).1.le (hKO hq).2 q.2)
    S mS hSpast hSeq (fun r q hq => hq.2.2) (by change φ (z,0) ≤ 2; linarith) ht

theorem expected_stopped_reverseFlow {a q : ℝ} (ha : 1/4 < a) (hq : 0 < q)
    {W : Measure Driver} (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W)
    {H : ℝ} (hH : 0 ≤ H) (φ : State × ℝ → ℝ) (hφ : Continuous φ)
    (hK : IsCompact {x | φ x ≤ 2}) (hKO : {x | φ x ≤ 2} ⊆ domain)
    (hyK : ∀ x, φ x ≤ 2 → q ≤ x.1.2.1.im)
    (z : State) (hz : φ (z,0) < 1) :
    let g := fun b : Driver => ODEPath.flow (globalVector a q) z b
    let τ := fun b : Driver => Exit (fun u => φ (g b u,b u.toNNReal)) 1 H
    ∀ t ≥ 0, (∫ b : Driver, test a (g b (min t (τ b))) (b (min t (τ b)).toNNReal) ∂W) ≤ test a z 0 := by
  exact expected_stopped_reverse_aux ha hW hH φ hφ hK hKO (globalVector a q)
    (continuous_globalVector hq a) (by dsimp [bound]; positivity)
    (by dsimp [lipBound]; positivity) (norm_globalVector_le hq a) (globalVector_sub_le hq a)
    (fun x hx => globalVector_eq hq a _ _ (hyK x hx)) z hz
end SLEExactGauge.ReverseDerivative

namespace SLEExactGauge.ReverseDerivative
open MeasureTheory ProbabilityTheory BrownianCalculus RationalStop

def exhaustion (q : ℝ) (n : ℕ) (x : State × ℝ) : ℝ :=
  max (‖x‖/((n:ℝ)+1)) (max (3-((n:ℝ)+1)*x.1.1) (3-x.1.2.1.im/q))

lemma continuous_exhaustion (q : ℝ) (n : ℕ) : Continuous (exhaustion q n) := by
  unfold exhaustion
  fun_prop

lemma exhaustion_compact (q : ℝ) (n : ℕ) : IsCompact {x | exhaustion q n x ≤ 2} := by
  apply (isCompact_closedBall (0 : State × ℝ) (2*((n:ℝ)+1))).of_isClosed_subset
    (isClosed_le (continuous_exhaustion q n) continuous_const)
  intro x hx
  have h : ‖x‖/((n:ℝ)+1) ≤ 2 := (le_max_left _ _).trans hx
  rw [mem_closedBall,dist_zero_right]
  exact (div_le_iff₀ (by positivity : 0 < (n:ℝ)+1)).mp h

lemma exhaustion_height {q : ℝ} (hq : 0 < q) (n : ℕ) {x : State × ℝ}
    (hx : exhaustion q n x ≤ 2) : q ≤ x.1.2.1.im := by
  have h : 3-x.1.2.1.im/q ≤ 2 :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hi : 1 ≤ x.1.2.1.im/q := by linarith
  simpa using (le_div_iff₀ hq).mp hi

lemma exhaustion_domain {q : ℝ} (hq : 0 < q) (n : ℕ) :
    {x | exhaustion q n x ≤ 2} ⊆ domain := by
  intro x hx
  refine ⟨?_,hq.trans_le (exhaustion_height hq n hx)⟩
  have h : 3-((n:ℝ)+1)*x.1.1 ≤ 2 :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hn : 0 < (n:ℝ)+1 := by positivity
  nlinarith

lemma exhaustion_lt {q : ℝ} (hq : 0 < q) (n : ℕ) {x : State × ℝ}
    (hn : ‖x‖ < (n:ℝ)+1) (hu : 2 < ((n:ℝ)+1)*x.1.1) (hy : 2*q < x.1.2.1.im) :
    exhaustion q n x < 1 := by
  apply max_lt
  · exact (div_lt_one (by positivity)).mpr hn
  · apply max_lt
    · linarith
    · have hi := (lt_div_iff₀ hq).mpr hy
      linarith

lemma eventually_exhaustion_lt {q δ : ℝ} (hq : 0 < q) (hδ : 0 < δ)
    {T : ℝ} (_hT : 0 ≤ T) (f : ℝ → State × ℝ) (hf : ContinuousOn f (Icc 0 T))
    (hu : ∀ t ∈ Icc 0 T, δ ≤ (f t).1.1)
    (hy : ∀ t ∈ Icc 0 T, 2*q < (f t).1.2.1.im) :
    ∀ᶠ n : ℕ in atTop, ∀ t ∈ Icc 0 T, exhaustion q n (f t) < 1 := by
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) T)).exists_bound_of_continuousOn hf
  obtain ⟨N,hN⟩ := exists_nat_gt (max C (2/δ))
  filter_upwards [eventually_ge_atTop N] with n hn
  intro t ht
  have hnN : (N:ℝ) ≤ n := by exact_mod_cast hn
  have hnC : C < (n:ℝ)+1 := by linarith [le_max_left C (2/δ)]
  have hnδ : 2/δ < (n:ℝ)+1 := by linarith [le_max_right C (2/δ)]
  apply exhaustion_lt hq n ((hC t ht).trans_lt hnC) _ (hy t ht)
  have hi : 2 < ((n:ℝ)+1)*δ := (div_lt_iff₀ hδ).mp hnδ
  exact hi.trans_le (mul_le_mul_of_nonneg_left (hu t ht) (by positivity))

lemma measurable_test (a : ℝ) : Measurable (Function.uncurry (test a)) := by
  change Measurable (fun x : State × ℝ => Real.exp
    (lambda a*x.1.2.2+r a/2*Real.log ((x.1.2.1.re-x.2)^2+x.1.2.1.im^2)+
     (zeta a-r a)*Real.log x.1.2.1.im-zeta a/2*Real.log
       (((x.1.2.1.re-x.2)^2+x.1.2.1.im^2)+x.1.1/2)))
  fun_prop

lemma test_pos (a : ℝ) (x : State) (b : ℝ) : 0 < test a x b := Real.exp_pos _

end SLEExactGauge.ReverseDerivative

namespace SLEExactGauge.ReverseDerivative
open MeasureTheory ProbabilityTheory BrownianCalculus RationalStop

def driven (a q : ℝ) (z : State) (b : Driver) (t : ℝ) : State × ℝ :=
  (ODEPath.flow (globalVector a q) z b t,b t.toNNReal)

lemma measurable_driven {q : ℝ} (hq : 0 < q) (a : ℝ) (z : State) (t : ℝ) :
    Measurable (fun b : Driver => driven a q z b t) := by
  have mb : Measurable (fun b : Driver => (b : ℝ≥0 → ℝ)) :=
    Measurable.of_eval fun time => (show Continuous (fun driver : Driver => driver time) from continuous_eval_const time).measurable
  exact ((ODEPath.measurable_flow _ (continuous_globalVector hq a).measurable z t).comp mb).prodMk
    (show Continuous (fun b : Driver => b t.toNNReal) from continuous_eval_const _).measurable

lemma continuousOn_driven {q T : ℝ} (hq : 0 < q) (hT : 0 ≤ T) (a : ℝ) (z : State) (b : Driver) :
    ContinuousOn (driven a q z b) (Icc 0 T) := by
  exact (ODEPath.continuousOn_flow _ (continuous_globalVector hq a) z b b.continuous
    (by dsimp [bound]; positivity) (by dsimp [lipBound]; positivity) hT
    (norm_globalVector_le hq a) (globalVector_sub_le hq a)).prodMk
    ((b.continuous.comp continuous_real_toNNReal).continuousOn)

lemma exit_eq_horizon {f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T)) (hs : ∀ t ∈ Icc 0 T, f t < 1) : Exit f 1 T = T := by
  have hb := exit_bounds hT hf (R := 1)
  apply le_antisymm hb.2
  by_contra hn
  have he : Exit f 1 T < T := lt_of_not_ge hn
  have hs' : Safe f 1 (Exit f 1 T) := (safe_iff hb.1
    (hf.mono (Icc_subset_Icc_right hb.2))).mpr (fun t ht => hs t ⟨ht.1,ht.2.trans hb.2⟩)
  exact lt_irrefl _ ((lt_exit_iff hT hf hb.1).mpr ⟨he,hs'⟩)

lemma stopped_test_integrable {q : ℝ} (hq : 0 < q) (a : ℝ)
    {W : Measure Driver} [IsFiniteMeasure W] {T : ℝ} (hT : 0 ≤ T)
    (φ : State × ℝ → ℝ) (hφ : Continuous φ)
    (hK : IsCompact {x | φ x ≤ 2}) (hKO : {x | φ x ≤ 2} ⊆ domain)
    (z : State) (hz : φ (z,0) < 1) :
    Integrable (fun b : Driver => test a
      (driven a q z b (Exit (fun u => φ (driven a q z b u)) 1 T)).1
      (driven a q z b (Exit (fun u => φ (driven a q z b u)) 1 T)).2) W := by
  let f := fun (b : Driver) u => φ (driven a q z b u)
  let τ := fun b => Exit (f b) 1 T
  have hfc (b : Driver) : ContinuousOn (f b) (Icc 0 T) :=
    hφ.comp_continuousOn (continuousOn_driven hq hT a z b)
  have mτ : Measurable τ := measurable_exit hT
    (fun u => hφ.measurable.comp (measurable_driven hq a z u)) hfc
  have hτ (b : Driver) : τ b ∈ Icc 0 T := exit_bounds hT (hfc b)
  have md : Measurable (fun b => driven a q z b (τ b)) := measurable_stopped_eval hT
    (measurable_driven hq a z) (continuousOn_driven hq hT a z) mτ hτ
  have hf0 (b : Driver) : f b 0 < 1 := by
    have hg := ODEPath.flow_solution (globalVector a q) (continuous_globalVector hq a) z b b.continuous
      (by dsimp [bound]; positivity) (by dsimp [lipBound]; positivity) hT
      (norm_globalVector_le hq a) (globalVector_sub_le hq a)
    simpa only [f,driven,hg.1,Real.toNNReal_zero,map_zero] using hz
  have hsafe (b : Driver) : driven a q z b (τ b) ∈ {x | φ x ≤ 2} := by
    have hb := bound_until_exit hT (hfc b) (hf0 b) (τ b) ⟨(hτ b).1,le_rfl⟩
    change f b (τ b) ≤ 2
    linarith
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn ((contDiffOn_test a).continuousOn.mono hKO)
  exact Integrable.of_bound ((measurable_test a).comp md).aestronglyMeasurable C
    (ae_of_all _ fun b => hC _ (hsafe b))

lemma lintegral_of_eventually_stopped {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : ℕ → Ω → ℝ) (hf : ∀ n, Integrable (f n) μ) (hpos : ∀ n x, 0 ≤ f n x)
    (F : Ω → ℝ) (hlim : ∀ x, ∀ᶠ n in atTop, f n x = F x)
    (C : ℝ) (he : ∀ n, (∫ x, f n x ∂μ) ≤ C) :
    (∫⁻ x, ENNReal.ofReal (F x) ∂μ) ≤ ENNReal.ofReal C := by
  have hl (x : Ω) : liminf (fun n => ENNReal.ofReal (f n x)) atTop = ENNReal.ofReal (F x) :=
    (tendsto_const_nhds.congr' ((hlim x).mono fun n hn => congrArg ENNReal.ofReal hn.symm)).liminf_eq
  calc (∫⁻ x, ENNReal.ofReal (F x) ∂μ)
      = ∫⁻ x, liminf (fun n => ENNReal.ofReal (f n x)) atTop ∂μ := by simp only [hl]
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (f n x) ∂μ) atTop :=
      lintegral_liminf_le' fun n => (hf n).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal C) atTop := by
      refine Filter.liminf_le_liminf ?_
      filter_upwards [] with n
      rw [← ofReal_integral_eq_lintegral_ofReal (hf n) (ae_of_all _ (hpos n))]
      exact ENNReal.ofReal_le_ofReal (he n)
    _ = ENNReal.ofReal C := tendsto_const_nhds.liminf_eq
end SLEExactGauge.ReverseDerivative

namespace SLEExactGauge.ReverseDerivative
open MeasureTheory ProbabilityTheory BrownianCalculus RationalStop

 

theorem reverse_supersolution_bound {a y δ T : ℝ} (ha : 1/4 < a)
    (hy : 0 < y) (hδ : 0 < δ) (hT : 0 ≤ T)
    {W : Measure Driver} (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W) :
    (∫⁻ b : Driver, ENNReal.ofReal
      (test a (reverseFlow a (y/4) (T+δ) y b T) (b T.toNNReal)) ∂W) ≤
        ENNReal.ofReal (test a (initial (T+δ) y) 0) := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  let q := y/4
  let z := initial (T+δ) y
  have hq : 0 < q := by dsimp [q]; positivity
  have ha0 : 0 ≤ a := by linarith
  have hi : ∀ᶠ n : ℕ in atTop, exhaustion q n (z,0) < 1 := by
    have hh := eventually_exhaustion_lt hq hδ (T := 0) le_rfl (fun _ => (z,0))
      continuousOn_const (fun t ht => by change δ ≤ T+δ; linarith)
      (fun t ht => by change 2*(y/4) < y; linarith)
    filter_upwards [hh] with n hn
    exact hn 0 ⟨le_rfl,le_rfl⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp hi
  let φ := fun n => exhaustion q (n+N)
  have hφ0 (n : ℕ) : φ n (z,0) < 1 := hN (n+N) (by omega)
  let τ := fun n (b : Driver) => Exit (fun u => φ n (driven a q z b u)) 1 T
  let f := fun n (b : Driver) => test a (driven a q z b (τ n b)).1 (driven a q z b (τ n b)).2
  have hτ (n : ℕ) (b : Driver) : τ n b ∈ Icc 0 T := exit_bounds hT
    ((continuous_exhaustion q (n+N)).comp_continuousOn (continuousOn_driven hq hT a z b))
  have hf (n : ℕ) : Integrable (f n) W := stopped_test_integrable hq a hT (φ n)
    (continuous_exhaustion q (n+N)) (exhaustion_compact q (n+N)) (exhaustion_domain hq (n+N)) z (hφ0 n)
  have he (n : ℕ) : (∫ b, f n b ∂W) ≤ test a z 0 := by
    have hh := expected_stopped_reverseFlow ha hq hW hT (φ n) (continuous_exhaustion q (n+N))
      (exhaustion_compact q (n+N)) (exhaustion_domain hq (n+N))
      (fun x hx => exhaustion_height hq (n+N) hx) z (hφ0 n) T hT
    have heq (b : Driver) : min T (τ n b) = τ n b := min_eq_right (hτ n b).2
    change (∫ b : Driver, test a (ODEPath.flow (globalVector a q) z b (min T (τ n b)))
      (b (min T (τ n b)).toNNReal) ∂W) ≤ test a z 0 at hh
    simpa only [heq,f,driven] using hh
  have hlim (b : Driver) : ∀ᶠ n in atTop,
      f n b = test a (reverseFlow a q (T+δ) y b T) (b T.toNNReal) := by
    have hh := eventually_exhaustion_lt hq hδ hT (driven a q z b)
      (continuousOn_driven hq hT a z b)
      (fun t ht => by
        change δ ≤ (reverseFlow a q (T+δ) y b t).1
        rw [reverseFlow_time hq a (T+δ) y b b.continuous hT t ht]
        linarith [ht.2])
      (fun t ht => by
        have hb := reverseFlow_height hq ha0 hy.le (T+δ) b b.continuous hT t ht
        change 2*q < (reverseFlow a q (T+δ) y b t).2.1.im
        dsimp [q]
        linarith)
    obtain ⟨K,hK⟩ := eventually_atTop.mp hh
    filter_upwards [eventually_ge_atTop K] with n hn
    have hexit : τ n b = T := exit_eq_horizon hT
      ((continuous_exhaustion q (n+N)).comp_continuousOn (continuousOn_driven hq hT a z b))
      (hK (n+N) (by omega))
    simp only [f,hexit,driven]
    rfl
  exact lintegral_of_eventually_stopped W f hf (fun n b => (test_pos a _ _).le)
    (fun b => test a (reverseFlow a q (T+δ) y b T) (b T.toNNReal)) hlim (test a z 0) he
end SLEExactGauge.ReverseDerivative

namespace SLEExactGauge.ReverseDerivative

lemma r_sub_zeta_pos {a : ℝ} (ha : 1/4 < a) : 0 < r a-zeta a := by
  have ha0 : 0 < a := by linarith
  have he : r a-zeta a = a+1/2+1/(16*a) := by unfold r zeta; ring
  rw [he]
  positivity

lemma exp_logderiv_le_test {a : ℝ} (ha : 1/4 < a) (v : State) (b : ℝ)
    (hu : 0 ≤ v.1) (hy : 0 < v.2.1.im) (huy : v.1 ≤ v.2.1.im^2) :
    Real.exp (lambda a*v.2.2) ≤ Real.exp (zeta a/2*Real.log (3/2))*test a v b := by
  let x := v.2.1.re-b
  let y := v.2.1.im
  have hR := R_pos x hy
  have hD := D_pos hu hy x
  have hlogR : 2*Real.log y ≤ Real.log (R x y) := by
    have hh := Real.log_le_log (sq_pos_of_pos hy) (show y^2 ≤ R x y from by unfold R; nlinarith [sq_nonneg x])
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  have hlogD : Real.log (D v.1 x y) ≤ Real.log (R x y)+Real.log (3/2) := by
    have hle : D v.1 x y ≤ R x y*(3/2) := by
      dsimp [D,R,x,y]
      nlinarith [sq_nonneg (v.2.1.re-b)]
    have hh := Real.log_le_log hD hle
    rwa [Real.log_mul hR.ne' (by norm_num : (3/2:ℝ) ≠ 0)] at hh
  have hz := (parameters ha).1
  have hrz := r_sub_zeta_pos ha
  have h1 := mul_nonneg hrz.le (sub_nonneg.mpr hlogR)
  have h2 := mul_nonneg hz.le (sub_nonneg.mpr hlogD)
  unfold test F
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  change lambda a*v.2.2 ≤ zeta a/2*Real.log (3/2)+H a v.1 x y v.2.2
  unfold H
  nlinarith

lemma initial_test_scale (a : ℝ) {y T : ℝ} (hy : 0 < y) (hT : 0 ≤ T) :
    Real.exp (zeta a/2*Real.log (3/2))*test a (initial (T+y^2) y) 0 =
      (3*y^2/(T+3*y^2))^(zeta a/2) := by
  have hy2 : 0 < y^2 := sq_pos_of_pos hy
  have hD : 0 < y^2+(T+y^2)/2 := by positivity
  have hden : 0 < T+3*y^2 := by positivity
  have hrat : 0 < 3*y^2/(T+3*y^2) := by positivity
  have he : 3*y^2/(T+3*y^2) = ((3/2:ℝ)*y^2)/(y^2+(T+y^2)/2) := by
    field_simp
    ring
  rw [Real.rpow_def_of_pos hrat,he,
    Real.log_div (mul_ne_zero (by norm_num) hy2.ne') hD.ne',
    Real.log_mul (by norm_num : (3/2:ℝ) ≠ 0) hy2.ne',Real.log_pow]
  simp only [test,initial,F,H,D,R,sub_zero,zero_pow (by omega : (2:ℕ) ≠ 0),zero_add,mul_zero,zero_add]
  rw [← Real.exp_add,Real.log_pow]
  congr 1
  ring
end SLEExactGauge.ReverseDerivative

namespace SLEExactGauge.ReverseDerivative
open MeasureTheory ProbabilityTheory BrownianCalculus

 

theorem reverse_logderiv_moment {a y T : ℝ} (ha : 1/4 < a)
    (hy : 0 < y) (hT : 0 ≤ T)
    {W : Measure Driver} (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W) :
    (∫⁻ b : Driver, ENNReal.ofReal (Real.exp
      (lambda a*(reverseFlow a (y/4) (T+y^2) y b T).2.2)) ∂W) ≤
        ENNReal.ofReal ((3*y^2/(T+3*y^2))^(zeta a/2)) := by
  let C := Real.exp (zeta a/2*Real.log (3/2))
  let g := fun (b : Driver) => reverseFlow a (y/4) (T+y^2) y b T
  have hq : 0 < y/4 := by positivity
  have htime (b : Driver) : (g b).1 = y^2 := by
    dsimp [g]
    rw [reverseFlow_time hq a (T+y^2) y b b.continuous hT T ⟨hT,le_rfl⟩]
    ring
  have hheight (b : Driver) : y ≤ (g b).2.1.im :=
    reverseFlow_height hq (by linarith) hy.le (T+y^2) b b.continuous hT T ⟨hT,le_rfl⟩
  have hpoint (b : Driver) : Real.exp (lambda a*(g b).2.2) ≤ C*test a (g b) (b T.toNNReal) := by
    apply exp_logderiv_le_test ha _ _
    · rw [htime]; positivity
    · exact hy.trans_le (hheight b)
    · rw [htime]
      nlinarith [hheight b]
  calc (∫⁻ b : Driver, ENNReal.ofReal (Real.exp (lambda a*(g b).2.2)) ∂W)
      ≤ ∫⁻ b : Driver, ENNReal.ofReal (C*test a (g b) (b T.toNNReal)) ∂W :=
        lintegral_mono fun b => ENNReal.ofReal_le_ofReal (hpoint b)
    _ = ENNReal.ofReal C*(∫⁻ b : Driver, ENNReal.ofReal (test a (g b) (b T.toNNReal)) ∂W) := by
      simp only [ENNReal.ofReal_mul (show 0 ≤ C from (Real.exp_pos _).le)]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C*ENNReal.ofReal (test a (initial (T+y^2) y) 0) :=
      mul_le_mul' le_rfl (reverse_supersolution_bound ha hy (sq_pos_of_pos hy) hT hW)
    _ = ENNReal.ofReal ((3*y^2/(T+3*y^2))^(zeta a/2)) := by
      rw [← ENNReal.ofReal_mul (show 0 ≤ C from (Real.exp_pos _).le)]
      exact congrArg ENNReal.ofReal (initial_test_scale a hy hT)
end SLEExactGauge.ReverseDerivative

open Set MeasureTheory ProbabilityTheory Topology Function Filter
open scoped NNReal ENNReal ContinuousMapZero

noncomputable section
namespace SLEExactGauge.BrownianRestart

abbrev Driver := C(ℝ≥0, ℝ)₀
instance : MeasurableSpace Driver := borel Driver
instance : BorelSpace Driver := ⟨rfl⟩
instance : PolishSpace Driver := ContinuousMapZero.isClosedEmbedding_toContinuousMap.polishSpace

def code (b : Driver) : ℚ → ℝ := fun q => b (Real.toNNReal (q:ℝ))

lemma measurable_code : Measurable code :=
  Measurable.of_eval fun _ => (continuous_eval_const _).measurable

lemma dense_rational_time : DenseRange (fun q : ℚ => Real.toNNReal (q:ℝ)) := by
  have hd : Surjective Real.toNNReal := fun x => ⟨(x:ℝ),Real.toNNReal_coe⟩
  exact hd.denseRange.comp Rat.denseRange_cast continuous_real_toNNReal

lemma code_injective : Injective code := by
  intro b c h
  apply ContinuousMapZero.ext
  have he := dense_rational_time.equalizer (map_continuous b) (map_continuous c) h
  exact congrFun he

lemma code_embedding : MeasurableEmbedding code := measurable_code.measurableEmbedding code_injective

end SLEExactGauge.BrownianRestart
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
