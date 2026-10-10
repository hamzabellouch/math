import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.FrozenExpectations

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
namespace SLEExactGauge.EulerGeneral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
omit [CompleteSpace E] in
lemma interpolate_at_node (f : ℝ → E → E) {h : ℝ} (hh : 0 < h) (z : E) (k : ℕ) :
    interpolate f h z ((k:ℝ)*h) = nodes f h z k := by
  simp [interpolate, mul_div_cancel_right₀ _ hh.ne']

 

omit [CompleteSpace E] in
lemma nodes_converge_moving {f : ℝ → E → E} {g : ℝ → E} {z : E} {L M T U s : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hg0 : g 0 = z)
    (hlip : ∀ u ∈ Icc 0 T, ∀ x y, ‖f u x-f u y‖ ≤ L*‖x-y‖)
    (hder : ∀ u ∈ Icc 0 T, HasDerivWithinAt g (f u (g u)) (Icc 0 T) u)
    (hcf : ContinuousOn (fun u => f u (g u)) (Icc 0 T))
    (hbound : ∀ u ∈ Icc 0 T, ‖f u (g u)‖ ≤ M)
    (hU : 0 ≤ U) (hUT : U < T) (hs : s ∈ Icc 0 U)
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0))
    (k : ℕ → ℕ) (hk : ∀ᶠ n in atTop, (k n:ℝ)*h n ≤ U)
    (hks : Tendsto (fun n => (k n:ℝ)*h n) atTop (𝓝 s)) :
    Tendsto (fun n => nodes f (h n) z (k n)) atTop (𝓝 (g s)) := by
  have hu := converge_uniformOn hL hM hg0 hlip hder hcf hbound hU hUT hh hh0
  have hgs : ContinuousWithinAt g (Icc 0 U) s :=
    (hder s ⟨hs.1, hs.2.trans hUT.le⟩).continuousWithinAt.mono (Icc_subset_Icc_right hUT.le)
  have hs' : Tendsto (fun n => (k n:ℝ)*h n) atTop (𝓝[Icc 0 U] s) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hks, hk.mono fun n hn => ⟨mul_nonneg (Nat.cast_nonneg _) (hh n).le,hn⟩⟩
  simpa only [interpolate_at_node _ (hh _) _ _] using hu.tendsto_comp hgs hs'

end SLEExactGauge.EulerGeneral

namespace SLEExactGauge.BrownianCalculus
open Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma frozenNodes_eq_min (v : E → ℝ → E) (f : ℝ → E → E)
    (U : ℕ → Set ((ℝ≥0 → ℝ) × (E × ℝ))) (h : ℝ≥0) (z : E) (b : ℝ≥0 → ℝ)
    (hf : ∀ (k : ℕ) x, f ((k:ℝ)*h) x = v x (b ((k:ℝ≥0)*h))) (K : ℕ)
    (ha : ∀ k < K, (b,(EulerGeneral.nodes f h z k,b ((k:ℝ≥0)*h))) ∈ U k)
    (hi : ∀ k ≥ K, ∀ x, (b,x) ∉ U k) (k : ℕ) :
    frozenNodes v U h (z,b 0) k b =
      (EulerGeneral.nodes f h z (min k K),b (((min k K:ℕ):ℝ≥0)*h)) := by
  induction k with
  | zero => simp [frozenNodes,EulerGeneral.nodes]
  | succ k ih =>
    by_cases hk : k < K
    · have hk1 : k+1 ≤ K := hk
      rw [frozenNodes,ih]
      simp only [min_eq_left hk.le, min_eq_left hk1, ha k hk, ite_eq_left, EulerGeneral.nodes, hf]
      congr 1
      simp only [Nat.cast_add,Nat.cast_one]
      ring
    · have hk' : K ≤ k := Nat.le_of_not_gt hk
      have hk1 : K ≤ k+1 := hk'.trans (Nat.le_succ _)
      rw [frozenNodes,ih]
      simp only [min_eq_right hk',min_eq_right hk1,hi k hk',ite_false]

end SLEExactGauge.BrownianCalculus

namespace SLEExactGauge.EulerGeneral

lemma ceil_mesh_times_converge {h : ℕ → ℝ} (hh : ∀ n, 0 < h n)
    (hh0 : Tendsto h atTop (𝓝 0)) {τ : ℝ} (hτ : 0 ≤ τ) :
    Tendsto (fun n => (⌈τ/h n⌉₊:ℝ)*h n) atTop (𝓝 τ) := by
  have hb (n : ℕ) : 0 ≤ (⌈τ/h n⌉₊:ℝ)*h n-τ ∧ (⌈τ/h n⌉₊:ℝ)*h n-τ ≤ h n := by
    have hl := Nat.le_ceil (τ/h n)
    have hu := Nat.ceil_lt_add_one (div_nonneg hτ (hh n).le)
    have hl' := (div_le_iff₀ (hh n)).mp hl
    have hu' := (mul_lt_mul_of_pos_right hu (hh n))
    rw [add_mul,div_mul_cancel₀ _ (hh n).ne',one_mul] at hu'
    constructor <;> linarith
  have hz : Tendsto (fun n => (⌈τ/h n⌉₊:ℝ)*h n-τ) atTop (𝓝 0) :=
    squeeze_zero (fun n => (hb n).1) (fun n => (hb n).2) hh0
  simpa using hz.add_const τ

lemma effective_stop_times_converge {h : ℕ → ℝ} (hh : ∀ n, 0 < h n)
    (hh0 : Tendsto h atTop (𝓝 0)) {τ t : ℝ} (hτ : 0 ≤ τ) (ht : 0 ≤ t) :
    Tendsto (fun n => ((min ⌊t/h n⌋₊ ⌈τ/h n⌉₊:ℕ):ℝ)*h n) atTop (𝓝 (min t τ)) := by
  have h1 := mesh_times_converge hh hh0 ht
  have h2 := ceil_mesh_times_converge hh hh0 hτ
  simpa only [Nat.cast_min, min_mul_of_nonneg _ _ (hh _).le] using h1.min h2

end SLEExactGauge.EulerGeneral

namespace SLEExactGauge.BrownianCalculus
open Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 

omit [CompleteSpace E] in
lemma ordinary_nodes_eventually_inside (f : ℝ → E → E) (g : ℝ → E) (z : E)
    (b : ℝ≥0 → ℝ) (D : Set (E × ℝ)) {τ T L M ε : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hg0 : g 0 = z)
    (hlip : ∀ u ∈ Icc 0 T, ∀ x y, ‖f u x-f u y‖ ≤ L*‖x-y‖)
    (hder : ∀ u ∈ Icc 0 T, HasDerivWithinAt g (f u (g u)) (Icc 0 T) u)
    (hcf : ContinuousOn (fun u => f u (g u)) (Icc 0 T))
    (hbound : ∀ u ∈ Icc 0 T, ‖f u (g u)‖ ≤ M)
    (hτ : 0 ≤ τ) (hτT : τ < T) (hε : 0 < ε)
    (hD : ∀ u ∈ Icc 0 τ, ∀ x, ‖x-g u‖ < ε → (x,b u.toNNReal) ∈ D)
    {h : ℕ → ℝ≥0} (hh : ∀ n, 0 < h n) (hh0 : Tendsto (fun n => (h n:ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∀ k : ℕ, (k:ℝ)*(h n:ℝ) < τ →
      (EulerGeneral.nodes f (h n) z k,b ((k:ℝ≥0)*h n)) ∈ D := by
  have hu := EulerGeneral.converge_uniformOn hL hM hg0 hlip hder hcf hbound hτ hτT
    (fun n => show 0 < (h n:ℝ) from hh n) hh0
  have he := (Metric.tendstoUniformlyOn_iff.mp hu) ε hε
  filter_upwards [he] with n hn
  intro k hk
  have htime : (k:ℝ)*(h n:ℝ) ∈ Icc 0 τ := ⟨by positivity,hk.le⟩
  have hn' := hn _ htime
  rw [EulerGeneral.interpolate_at_node _ (show 0 < (h n:ℝ) from hh n) _ _] at hn'
  have hb : ((k:ℝ)*(h n:ℝ)).toNNReal = (k:ℝ≥0)*h n := by
    apply NNReal.coe_injective
    simp [Real.toNNReal_of_nonneg (show 0 ≤ (k:ℝ)*(h n:ℝ) by positivity)]
  rw [← hb]
  apply hD _ htime _
  rw [dist_comm] at hn'
  simpa only [dist_eq_norm] using hn'

end SLEExactGauge.BrownianCalculus

namespace SLEExactGauge.BrownianCalculus
open Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 

omit [CompleteSpace E] in
theorem frozen_nodes_path_limit (v : E → ℝ → E) (g : ℝ → E) (z : E)
    (b : ℝ≥0 → ℝ) (cb : Continuous b) (D : Set (E × ℝ))
    (U : ℕ → ℕ → Set ((ℝ≥0 → ℝ) × (E × ℝ))) {τ T t L M ε : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hg0 : g 0 = z)
    (hlip : ∀ u ∈ Icc 0 T, ∀ x y, ‖v x (b u.toNNReal)-v y (b u.toNNReal)‖ ≤ L*‖x-y‖)
    (hder : ∀ u ∈ Icc 0 T, HasDerivWithinAt g (v (g u) (b u.toNNReal)) (Icc 0 T) u)
    (hcf : ContinuousOn (fun u => v (g u) (b u.toNNReal)) (Icc 0 T))
    (hbound : ∀ u ∈ Icc 0 T, ‖v (g u) (b u.toNNReal)‖ ≤ M)
    (hτ : 0 ≤ τ) (hτT : τ < T) (ht : 0 ≤ t) (hε : 0 < ε)
    (hD : ∀ u ∈ Icc 0 τ, ∀ x, ‖x-g u‖ < ε → (x,b u.toNNReal) ∈ D)
    {h : ℕ → ℝ≥0} (hh : ∀ n, 0 < h n) (hh0 : Tendsto (fun n => (h n:ℝ)) atTop (𝓝 0))
    (hU : ∀ n k x, (b,x) ∈ U n k ↔ (k:ℝ)*(h n:ℝ) < τ ∧ x ∈ D) :
    Tendsto (fun n => frozenNodes v (U n) (h n) (z,b 0) ⌊t/(h n:ℝ)⌋₊ b)
      atTop (𝓝 (g (min t τ),b (min t τ).toNNReal)) := by
  let f : ℝ → E → E := fun u x => v x (b u.toNNReal)
  let K : ℕ → ℕ := fun n => ⌈τ/(h n:ℝ)⌉₊
  let k : ℕ → ℕ := fun n => min ⌊t/(h n:ℝ)⌋₊ (K n)
  have hn := ordinary_nodes_eventually_inside f g z b D hL hM hg0 hlip hder hcf hbound
    hτ hτT hε hD hh hh0
  have he : ∀ᶠ n in atTop, frozenNodes v (U n) (h n) (z,b 0) ⌊t/(h n:ℝ)⌋₊ b =
      (EulerGeneral.nodes f (h n) z (k n),b ((k n:ℝ≥0)*h n)) := by
    filter_upwards [hn] with n hn
    refine frozenNodes_eq_min v f (U n) (h n) z b ?_ (K n) ?_ ?_ _
    · intro j x
      dsimp [f]
      congr 2
      apply NNReal.coe_injective
      simp [Real.toNNReal_of_nonneg (show 0 ≤ (j:ℝ)*(h n:ℝ) by positivity)]
    · intro j hj
      have htj : (j:ℝ)*(h n:ℝ) < τ :=
        (lt_div_iff₀ (show 0 < (h n:ℝ) from hh n)).mp (Nat.lt_ceil.mp hj)
      exact (hU n j _).mpr ⟨htj,hn j htj⟩
    · intro j hj x hx
      have htj : τ ≤ (j:ℝ)*(h n:ℝ) :=
        (div_le_iff₀ (show 0 < (h n:ℝ) from hh n)).mp (Nat.ceil_le.mp hj)
      exact (not_lt_of_ge htj) ((hU n j x).mp hx).1
  have hk0 : Tendsto (fun n => (k n:ℝ)*(h n:ℝ)) atTop (𝓝 (min t τ)) :=
    EulerGeneral.effective_stop_times_converge (fun n => hh n) hh0 hτ ht
  let S : ℝ := (τ+T)/2
  have hsS : min t τ < S := lt_of_le_of_lt (min_le_right _ _) (by dsimp [S]; linarith)
  have hkS : ∀ᶠ n in atTop, (k n:ℝ)*(h n:ℝ) ≤ S :=
    (hk0.eventually (gt_mem_nhds hsS)).mono fun _ hn => hn.le
  have hg := EulerGeneral.nodes_converge_moving hL hM hg0 hlip hder hcf hbound
    (show 0 ≤ S by dsimp [S]; linarith) (show S < T by dsimp [S]; linarith)
    (show min t τ ∈ Icc 0 S from ⟨le_min ht hτ,hsS.le⟩)
    (fun n => show 0 < (h n:ℝ) from hh n) hh0 k hkS hk0
  have hb0 : Tendsto (fun n => (k n:ℝ≥0)*h n) atTop (𝓝 (min t τ).toNNReal) := by
    convert! continuous_real_toNNReal.continuousAt.tendsto.comp hk0 using 1
    funext n
    apply NNReal.coe_injective
    simp [Real.toNNReal_of_nonneg (show 0 ≤ (k n:ℝ)*(h n:ℝ) by positivity)]
  exact (hg.prodMk_nhds (cb.continuousAt.tendsto.comp hb0)).congr' (Filter.EventuallyEq.symm he)

end SLEExactGauge.BrownianCalculus

namespace SLEExactGauge.BrownianCalculus
open Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

 

omit [CompleteSpace E] in
theorem expected_stopped_smooth {W : Measure Driver}
    (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W)
    (A : SmoothTest E) (v : E → ℝ → E) (mv : Measurable (Function.uncurry v))
    (g : Driver → ℝ → E) (z : E) {L M T t : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hv : ∀ x b, ‖v x b‖ ≤ M) (hlip : ∀ b x y, ‖v x b-v y b‖ ≤ L*‖x-y‖)
    (hg0 : ∀ b, g b 0 = z)
    (hder : ∀ b u, u ∈ Icc 0 T → HasDerivWithinAt (g b) (v (g b u) (b u.toNNReal)) (Icc 0 T) u)
    (hcf : ∀ b, ContinuousOn (fun u => v (g b u) (b u.toNNReal)) (Icc 0 T))
    (τ : (ℝ≥0 → ℝ) → ℝ) (mτ : Measurable τ)
    (hτpast : ∀ (s : ℝ≥0) b c, (∀ u ≤ s, b u = c u) → ((s:ℝ) < τ b ↔ (s:ℝ) < τ c))
    (hτ : ∀ b : Driver, 0 ≤ τ b ∧ τ b < T)
    (D : Set (E × ℝ)) (mD : MeasurableSet D)
    (hD : ∀ b : Driver, ∃ ε > 0, ∀ u ∈ Icc 0 (τ b), ∀ x,
      ‖x-g b u‖ < ε → (x,b u.toNNReal) ∈ D)
    (hgen : ∀ x ∈ D, A.D x.1 x.2 (v x.1 x.2)+deriv (deriv (A.F x.1)) x.2/2 ≤ 0)
    (ht : 0 ≤ t) :
    (∫ b : Driver, A.F (g b (min t (τ b))) (b (min t (τ b)).toNNReal) ∂W) ≤ A.F z 0 := by
  let h : ℕ → ℝ≥0 := fun n => (1/2)^n
  have hh : ∀ n, 0 < h n := fun n => pow_pos (by norm_num) n
  have hh0 : Tendsto (fun n => (h n:ℝ)) atTop (𝓝 0) := by
    simp only [h,NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  let U : ℕ → ℕ → Set ((ℝ≥0 → ℝ) × (E × ℝ)) :=
    fun n k => {q | (k:ℝ)*(h n:ℝ) < τ q.1 ∧ q.2 ∈ D}
  have mU : ∀ n k, MeasurableSet (U n k) := by
    intro n k
    exact (measurableSet_lt measurable_const (mτ.comp measurable_fst)).inter
      (mD.preimage measurable_snd)
  have hu : ∀ n (k : ℕ) b c, (∀ u ≤ (k:ℝ≥0)*h n, b u = c u) → ∀ x,
      ((b,x) ∈ U n k ↔ (c,x) ∈ U n k) := by
    intro n k b c hbc x
    change ((k:ℝ)*(h n:ℝ) < τ b ∧ x ∈ D ↔ (k:ℝ)*(h n:ℝ) < τ c ∧ x ∈ D)
    rw [show (k:ℝ)*(h n:ℝ) = (((k:ℝ≥0)*h n):ℝ) by simp]
    exact and_congr_left fun _ => hτpast _ b c hbc
  apply expected_frozen_limit hW A v mv U mU h (fun n => ⌊t/(h n:ℝ)⌋₊) (z,0) hu M hv
    (fun _ _ _ x hx => hgen x hx.2)
    (fun b => (g b (min t (τ b)), b (min t (τ b)).toNNReal)) t hh0
    (EulerGeneral.mesh_times_converge (fun n => hh n) hh0 ht)
  filter_upwards [] with b
  obtain ⟨ε,hε,hDb⟩ := hD b
  have hp := frozen_nodes_path_limit v (g b) z b b.continuous D U hL hM (hg0 b)
    (fun _ _ => hlip _) (hder b) (hcf b) (fun u _ => hv _ _) (hτ b).1 (hτ b).2 ht
    hε hDb hh hh0 (fun _ _ _ => Iff.rfl)
  simpa only [map_zero] using hp

end SLEExactGauge.BrownianCalculus

open scoped ContDiff Manifold
namespace SLEExactGauge.BrownianCalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

 
def driverJets (F : E × ℝ → ℝ) : ℕ → E × ℝ → ℝ
  | 0 => F
  | n+1 => fun q => fderiv ℝ (driverJets F n) q (0,1)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma driverJets_smooth {F : E × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    ContDiff ℝ ∞ (driverJets F n) := by
  induction n with
  | zero => exact hF
  | succ n ih =>
    exact (contDiff_infty_iff_fderiv.mp ih).2.clm_apply contDiff_const

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma driverJets_compact {F : E × ℝ → ℝ} (hF : HasCompactSupport F) (n : ℕ) :
    HasCompactSupport (driverJets F n) := by
  induction n with
  | zero => exact hF
  | succ n ih => exact ih.fderiv_apply ℝ (0,1)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma driverJets_restriction {F : E × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (n : ℕ)
    (x : E) (b : ℝ) : driverJets F n (x,b) = iteratedDeriv n (fun c => F (x,c)) b := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    have he : iteratedDeriv n (fun c => F (x,c)) = fun c => driverJets F n (x,c) := by
      funext c
      exact (ih c).symm
    rw [iteratedDeriv_succ,he]
    have hd := ((driverJets_smooth hF n).differentiable (by simp) (x,b)).hasFDerivAt.comp_hasDerivAt b
      ((hasDerivAt_const b x).prodMk (hasDerivAt_id b))
    exact hd.deriv.symm

 

omit [SecondCountableTopology E] in
theorem exists_smoothTest_of_compact (F : E × ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (hK : HasCompactSupport F) :
    ∃ A : SmoothTest E, A.F = fun x b => F (x,b) := by
  let D : E × ℝ → E →L[ℝ] ℝ := fun q =>
    (fderiv ℝ F q).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hD : ContDiff ℝ ∞ D :=
    (contDiff_infty_iff_fderiv.mp hF).2.clm_comp contDiff_const
  have hDK : HasCompactSupport D := by
    exact (hK.fderiv ℝ).comp_left (g := fun A : E × ℝ →L[ℝ] ℝ => A.comp (ContinuousLinearMap.inl ℝ E ℝ)) (show (0 : E × ℝ →L[ℝ] ℝ).comp (ContinuousLinearMap.inl ℝ E ℝ) = 0 from rfl)
  obtain ⟨C₀,hC₀⟩ := hK.exists_bound_of_continuous hF.continuous
  obtain ⟨C₁,hC₁⟩ := (driverJets_compact hK 1).exists_bound_of_continuous
    (driverJets_smooth hF 1).continuous
  obtain ⟨C₂,hC₂⟩ := (driverJets_compact hK 2).exists_bound_of_continuous
    (driverJets_smooth hF 2).continuous
  obtain ⟨C₃,hC₃⟩ := (driverJets_compact hK 3).exists_bound_of_continuous
    (driverJets_smooth hF 3).continuous
  obtain ⟨Cx,hCx⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hDK hD (by simp)
  obtain ⟨Cc,hCc⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (driverJets_compact hK 2)
    (driverJets_smooth hF 2) (by simp)
  have hj1 (x : E) (b : ℝ) : driverJets F 1 (x,b) = deriv (fun c => F (x,c)) b := by
    simpa using driverJets_restriction hF 1 x b
  have hj2 (x : E) (b : ℝ) : driverJets F 2 (x,b) = deriv (deriv (fun c => F (x,c))) b := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using driverJets_restriction hF 2 x b
  refine ⟨{
    F := fun x b => F (x,b)
    D := fun x b => D (x,b)
    C₀ := C₀
    C₁ := C₁
    C₂ := C₂
    C₃ := max C₃ 0
    Cx := Cx
    Ccross := Cc
    hC₃ := le_max_right _ _
    hCx := Cx.coe_nonneg
    hCcross := Cc.coe_nonneg
    cF := hF.continuous
    mF := hF.continuous.measurable
    mB1 := ?_
    mB2 := ?_
    hD := ?_
    hsm := ?_
    hF := ?_
    hB1 := ?_
    hB2 := ?_
    hB3 := ?_
    hLipD := ?_
    hLipB2 := ?_ }, rfl⟩
  · convert! (driverJets_smooth hF 1).continuous.measurable using 1
    funext q
    exact (hj1 q.1 q.2).symm
  · convert! (driverJets_smooth hF 2).continuous.measurable using 1
    funext q
    exact (hj2 q.1 q.2).symm
  · intro x b
    have hi : HasFDerivAt (fun y : E => (y,b)) (ContinuousLinearMap.inl ℝ E ℝ) x := by
      convert! (hasFDerivAt_id x).prodMk (hasFDerivAt_const b x) using 1
    exact ((hF.differentiable (by simp) (x,b)).hasFDerivAt).comp x hi
  · intro x
    exact (hF.comp (contDiff_const.prodMk contDiff_id)).of_le (WithTop.coe_le_coe.mpr le_top)
  · intro x b
    simpa only [Real.norm_eq_abs] using hC₀ (x,b)
  · intro x b
    simpa only [hj1,Real.norm_eq_abs] using hC₁ (x,b)
  · intro x b
    simpa only [hj2,Real.norm_eq_abs] using hC₂ (x,b)
  · intro x b
    rw [← driverJets_restriction hF 3 x b,← Real.norm_eq_abs]
    exact (hC₃ (x,b)).trans (le_max_left _ _)
  · intro x y b
    simpa [Prod.norm_def] using hCx.norm_sub_le (x,b) (y,b)
  · intro x y b
    simpa [hj2,Prod.norm_def,Real.norm_eq_abs] using hCc.norm_sub_le (x,b) (y,b)

end SLEExactGauge.BrownianCalculus

namespace SLEExactGauge.Localization
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

 

theorem compact_extension {K O : Set E} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (f : E → F) (hf : ContDiffOn ℝ ∞ f O) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ ∀ x ∈ K, g =ᶠ[𝓝 x] f := by
  obtain ⟨L,hL,hKL,hLO⟩ := exists_compact_between hK hO hKO
  obtain ⟨φ,hφ1,hφ0,hφbound⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (𝓘(ℝ,E)) hK.isClosed hKL (n := ⊤)
  have hφsmooth : ContDiff ℝ ∞ (φ : E → ℝ) := contMDiff_iff_contDiff.mp φ.contMDiff
  have hsupp : tsupport (φ : E → ℝ) ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro x hx
    by_contra hn
    exact hx (hφ0 x hn)
  have hφK : HasCompactSupport (φ : E → ℝ) := hL.of_isClosed_subset isClosed_closure hsupp
  refine ⟨fun x => φ x • f x,?_,hφK.smul_right,?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ tsupport (φ : E → ℝ)
    · exact hφsmooth.contDiffAt.smul ((hf x (hLO (hsupp hx))).contDiffAt (hO.mem_nhds (hLO (hsupp hx))))
    · have he : (φ : E → ℝ) =ᶠ[𝓝 x] 0 := by
        exact (notMem_tsupport_iff_eventuallyEq.mp hx)
      apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      filter_upwards [he] with y hy
      simp [hy]
  · intro x hx
    have hnear : ∀ᶠ y in 𝓝 x, φ y = 1 := hφ1.filter_mono (nhds_le_nhdsSet hx)
    filter_upwards [hnear] with y hy
    simp [hy]

end SLEExactGauge.Localization

namespace SLEExactGauge.BrownianCalculus
open Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end SLEExactGauge.BrownianCalculus
end
end
end
end
end
end
end

end OAI
