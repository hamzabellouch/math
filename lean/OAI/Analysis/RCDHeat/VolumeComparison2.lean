import Mathlib
import OAI.Analysis.RCDHeat.VolumeComparison

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: VolumeComparison, RCDVolumeGrowth, RCDConservative, LipschitzProduct, RelaxedProduct, DaviesForm, DaviesWeight. -/



open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal NNReal
namespace RegularPointCoordinates
universe u
open MeasureTheory Set Metric Filter
open scoped ENNReal Topology NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] [MetricSpace X] in
 theorem hausdorff_normalization_pos_ne_top (n : ℕ) :
    0 < (volume (Metric.ball (0 : Euclidean n) 1) / (2:ℝ≥0∞)^n) ∧
      (volume (Metric.ball (0 : Euclidean n) 1) / (2:ℝ≥0∞)^n) ≠ ∞ := by
  have hvol0 := Metric.measure_ball_pos (volume : Measure (Euclidean n)) 0 zero_lt_one
  have hvolt : volume (Metric.ball (0 : Euclidean n) 1) ≠ ∞ := measure_ball_lt_top.ne
  have htwo0 : (2:ℝ≥0∞)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  have htwot : (2:ℝ≥0∞)^n ≠ ∞ := ENNReal.pow_ne_top (by norm_num)
  exact ⟨ENNReal.div_pos hvol0.ne' htwot, ENNReal.div_ne_top hvolt htwo0⟩

 

theorem NoncollapsedRCD.ball_upper_enlargement (K : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (p : X) (R δ : ℝ) (hR : 0 < R) (hδ : 0 < δ) :
    hausdorff n X (ball p R) ≤
      (volume (ball (0 : Euclidean n) 1) / (2:ℝ≥0∞)^n) *
        ENNReal.ofReal (2*(R+δ)*Real.exp (2*(R+δ)*Real.sqrt (|K|/((n:ℝ)-1))))^n := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let := hX.locDoubling K n hn
  let μ := hausdorff n X
  let c := volume (ball (0 : Euclidean n) 1) / (2:ℝ≥0∞)^n
  let A := R+δ
  let E := Real.exp (2*A*Real.sqrt (|K|/((n:ℝ)-1)))
  let V := μ (ball p R)
  let D := ENNReal.ofReal (2*A*E)^n
  have hA : 0 < A := add_pos hR hδ
  have hE : 0 < E := Real.exp_pos _
  apply volume_coefficient_le_of_ball_cost μ n c V D
    (hausdorff_normalization_pos_ne_top n).1.ne'
    (hX.fullSupport p R hR).ne' (hX.finiteOnBounded _ isBounded_ball).ne rfl
    (ball p δ) isOpen_ball (hX.fullSupport p δ hδ).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne
  intro x hx
  refine ⟨A,hA,?_⟩
  intro r hr hrA
  have hsub : ball p R ⊆ ball x A := by
    intro y hy
    have ht := dist_triangle y p x
    rw [dist_comm p x] at ht
    change dist x p < δ at hx
    change dist y p < R at hy
    change dist y x < A
    dsimp [A]
    linarith
  have hratio := hX.cd.ball_ratio μ K n hX.fullSupport hX.finiteOnBounded hn x r A hr hrA
  have hb : distortionFloor K n (2*A) (r/A)^n * V ≤ μ (ball x r) :=
    (mul_le_mul' le_rfl (measure_mono hsub)).trans hratio
  have he : ENNReal.ofReal (2*r) = ENNReal.ofReal (2*A*E) * distortionFloor K n (2*A) (r/A) := by
    unfold distortionFloor
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*A*E)]
    congr 1
    dsimp [E]
    field_simp
  calc
    V * ENNReal.ofReal (2*r)^n = D * (distortionFloor K n (2*A) (r/A)^n * V) := by
      rw [he, mul_pow]
      dsimp [D]
      ac_rfl
    _ ≤ D * μ (ball x r) := mul_le_mul' le_rfl hb
    _ ≤ D * μ (closedBall x r) := mul_le_mul' le_rfl (measure_mono ball_subset_closedBall)

 theorem NoncollapsedRCD.ball_upper (K : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (p : X) (R : ℝ) (hR : 0 < R) :
    hausdorff n X (ball p R) ≤
      (volume (ball (0 : Euclidean n) 1) / (2:ℝ≥0∞)^n) *
        ENNReal.ofReal (2*R*Real.exp (2*R*Real.sqrt (|K|/((n:ℝ)-1))))^n := by
  let c := volume (ball (0 : Euclidean n) 1) / (2:ℝ≥0∞)^n
  have hc : c ≠ ∞ := (hausdorff_normalization_pos_ne_top n).2
  have hh : Continuous (fun δ : ℝ => c *
      ENNReal.ofReal (2*(R+δ)*Real.exp (2*(R+δ)*Real.sqrt (|K|/((n:ℝ)-1))))^n) := by
    apply (ENNReal.continuous_const_mul hc).comp
    have hc' : Continuous (fun δ : ℝ => ENNReal.ofReal
        (2*(R+δ)*Real.exp (2*(R+δ)*Real.sqrt (|K|/((n:ℝ)-1))))) := by
      exact ENNReal.continuous_ofReal.comp (by fun_prop)
    simpa only [ENNReal.rpow_natCast, Function.comp_def] using
      (ENNReal.continuous_rpow_const (y := (n:ℝ))).comp hc'
  have hlim := (hh.continuousAt (x := (0:ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  have hbound : ∀ᶠ δ : ℝ in 𝓝[>] 0, hausdorff n X (ball p R) ≤ c *
      ENNReal.ofReal (2*(R+δ)*Real.exp (2*(R+δ)*Real.sqrt (|K|/((n:ℝ)-1))))^n := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hX.ball_upper_enlargement K n hn p R δ hR hδ
  simpa only [add_zero] using ge_of_tendsto hlim hbound

section RCDVolumeGrowth
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

 theorem NoncollapsedRCD.exponential_volume (K : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (p : X) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ R : ℝ, 1 ≤ R →
      (hausdorff n X).real (Metric.closedBall p (2*R)) ≤ A*Real.exp (B*R) := by
  let c := volume (Metric.ball (0 : Euclidean n) 1) / (2:ℝ≥0∞)^n
  let S := Real.sqrt (|K|/((n:ℝ)-1))
  have hc : c ≠ ∞ := (hausdorff_normalization_pos_ne_top n).2
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  refine ⟨c.toReal*6^n, (n:ℝ)*(1+6*S), by positivity, by positivity, ?_⟩
  intro R hR
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hsub : Metric.closedBall p (2*R) ⊆ Metric.ball p (3*R) :=
    Metric.closedBall_subset_ball (by linarith)
  have hbound := (measure_mono hsub).trans (hX.ball_upper K n hn p (3*R) (by linarith))
  change hausdorff n X (Metric.closedBall p (2*R)) ≤
    c * ENNReal.ofReal (2*(3*R)*Real.exp (2*(3*R)*S))^n at hbound
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top hc (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)) hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)] at hreal
  have hRexp : R ≤ Real.exp R := le_trans (by linarith : R ≤ R+1) (Real.add_one_le_exp R)
  have hs : 2*(3*R)*Real.exp (2*(3*R)*S) ≤ 6*Real.exp ((1+6*S)*R) := by
    calc
      2*(3*R)*Real.exp (2*(3*R)*S) = 6*R*Real.exp (6*S*R) := by ring_nf
      _ ≤ 6*Real.exp R*Real.exp (6*S*R) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hRexp (by norm_num)) (Real.exp_pos _).le
      _ = 6*Real.exp ((1+6*S)*R) := by rw [show (1+6*S)*R = R+6*S*R by ring, Real.exp_add]; ring
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 2*(3*R)*Real.exp (2*(3*R)*S)) hs n
  calc
    (hausdorff n X).real (Metric.closedBall p (2*R)) ≤
      c.toReal*(2*(3*R)*Real.exp (2*(3*R)*S))^n := hreal
    _ ≤ c.toReal*(6*Real.exp ((1+6*S)*R))^n := mul_le_mul_of_nonneg_left hp ENNReal.toReal_nonneg
    _ = c.toReal*6^n*Real.exp ((n:ℝ)*(1+6*S)*R) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      have he : (n:ℝ)*((1+6*S)*R) = (n:ℝ)*(1+6*S)*R := by ring
      rw [he]
      ring
end RCDVolumeGrowth

section RCDConservative
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

 theorem NoncollapsedRCD.conservative (K : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (p : X) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ (f : Lp ℝ 2 (hausdorff n X)), 0 ≤ f → Integrable f (hausdorff n X) →
      ∀ t : ℝ, 0 ≤ t →
      (∫ x, heatAt (hausdorff n X) hX.quadratic t f x ∂hausdorff n X) =
        ∫ x, f x ∂hausdorff n X := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  intro f hf hfi t ht
  obtain ⟨A,B,hA,hB,hvol⟩ := hX.exponential_volume K n hn p
  exact heatAt_integral_eq_of_exponential_volume _ hX.quadratic p hA hB hvol f hf hfi ht
end RCDConservative

section LipschitzProduct
variable {X : Type u} [MetricSpace X]

 theorem lipschitz_mul_constant_outside_compact {θ g : X → ℝ} {C D B : ℝ≥0}
    (hθ : LipschitzWith C θ) (hg : LipschitzWith D g) (c : ℝ)
    (hs : HasCompactSupport (fun x => θ x-c)) (hb : ∀ x, |θ x| ≤ B) :
    ∃ L : ℝ≥0, LipschitzWith L (fun x => θ x*g x) := by
  obtain ⟨A, hA⟩ := hs.exists_bound_of_continuousOn hg.continuous.continuousOn
  let A' : ℝ≥0 := ⟨max A 0, le_max_right _ _⟩
  have hθc : LipschitzWith C (fun x => θ x-c) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa [Real.dist_eq] using hθ.dist_le_mul x y
  have hb' (x : X) : |θ x-c| ≤ (B+‖c‖₊ : ℝ≥0) := by
    calc
      |θ x-c| ≤ |θ x| +|c| := abs_sub _ _
      _ ≤ (B:ℝ)+|c| := by linarith [hb x]
      _ = _ := by simp only [NNReal.coe_add, coe_nnnorm, Real.norm_eq_abs]
  have hA' (x : X) (hx : x ∈ Function.support (fun x => θ x-c)) : |g x| ≤ A' := by
    have hx' : |g x| ≤ A := by simpa only [Real.norm_eq_abs] using hA x (subset_tsupport _ hx)
    exact hx'.trans (le_max_left _ _)
  have he := lipschitzWith_mul_of_support_bound hθc hg hb' hA'
  refine ⟨(B+‖c‖₊)*D+A'*C+‖c‖₊*D, ?_⟩
  convert! he.add (lipschitzWith_const_mul_real hg c) using 1
  funext x
  ring
end LipschitzProduct

section RelaxedProduct
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X)

 theorem IsRelaxedSlope.mul_lipschitz {f G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ f G)
    {θ η : X → ℝ} {C B : ℝ≥0} (hθ : LipschitzWith C θ)
    (c : ℝ) (hs : HasCompactSupport (fun x => θ x-c))
    (hb : ∀ x, |θ x| ≤ B) (hθn : ∀ x, 0 ≤ θ x)
    (hηn : ∀ x, 0 ≤ η x) (hηs : ∀ x, localSlope θ x ≤ ENNReal.ofReal (η x))
    (θlp ηlp : Lp ℝ ∞ μ) (hθlp : ⇑θlp =ᵐ[μ] θ) (hηlp : ⇑ηlp =ᵐ[μ] η) :
    IsRelaxedSlope μ (lpMultiplier μ θlp f)
      (lpMultiplier μ θlp G + lpMultiplier μ ηlp (lpAbs μ f)) := by
  obtain ⟨us, gs, Gs, hl, ha, hm, hu, hc⟩ := hG
  let ws := fun i => lpMultiplier μ θlp (us i)
  let ks := fun i x => θ x*gs i x
  let Ws := fun i => lpMultiplier μ θlp (Gs i) + lpMultiplier μ ηlp (lpAbs μ (us i))
  refine ⟨ws, ks, Ws, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨D,hD⟩ := hl i
    exact lipschitz_mul_constant_outside_compact hθ hD c hs hb
  · intro i
    filter_upwards [lpMultiplier_coe μ θlp (us i), ha i, hθlp] with x he hu hθx
    exact he.trans (by rw [hu, hθx])
  · intro i
    obtain ⟨D,hD⟩ := hl i
    filter_upwards [Lp.coeFn_add (lpMultiplier μ θlp (Gs i)) (lpMultiplier μ ηlp (lpAbs μ (us i))),
      lpMultiplier_coe μ θlp (Gs i), lpMultiplier_coe μ ηlp (lpAbs μ (us i)),
      lpAbs_coe μ (us i), ha i, hm i, hθlp, hηlp] with x hadd hmul hmul' habs hu hm hθx hηx
    change 0 ≤ Ws i x ∧ localSlope (ks i) x ≤ ENNReal.ofReal (Ws i x)
    have he : Ws i x = θ x*Gs i x+η x*|gs i x| := by
      change (lpMultiplier μ θlp (Gs i)+lpMultiplier μ ηlp (lpAbs μ (us i))) x = _
      simp only [Pi.add_apply] at hadd
      rw [hadd, hmul, hmul', habs, hu, hθx, hηx]
    rw [he]
    refine ⟨add_nonneg (mul_nonneg (hθn x) hm.1) (mul_nonneg (hηn x) (abs_nonneg _)), ?_⟩
    calc
      localSlope (ks i) x ≤ ENNReal.ofReal |θ x| *localSlope (gs i) x+
          ENNReal.ofReal |gs i x| *localSlope θ x :=
        localSlope_mul_le hθ.continuous.continuousAt
          (ne_top_of_le_ne_top ENNReal.coe_ne_top (localSlope_le_of_lipschitz hD x))
      _ ≤ ENNReal.ofReal (θ x)*ENNReal.ofReal (Gs i x)+
          ENNReal.ofReal |gs i x| *ENNReal.ofReal (η x) := by
        rw [abs_of_nonneg (hθn x)]
        exact add_le_add (mul_le_mul' le_rfl hm.2) (mul_le_mul' le_rfl (hηs x))
      _ = _ := by
        rw [← ENNReal.ofReal_mul (hθn x), ← ENNReal.ofReal_mul (abs_nonneg _),
          ← ENNReal.ofReal_add (mul_nonneg (hθn x) hm.1) (mul_nonneg (abs_nonneg _) (hηn x))]
        congr 1
        ring
  · exact (lpMultiplier μ θlp).continuous.continuousAt.tendsto.comp hu
  · exact ((lpMultiplier μ θlp).continuous.continuousAt.tendsto.comp hc).add
      ((lpMultiplier μ ηlp).continuous.continuousAt.tendsto.comp
        ((lpAbs_continuous μ).continuousAt.tendsto.comp hu))
end RelaxedProduct

section DaviesForm
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem mul_lipschitz_finiteEnergy (f : SobolevSpace μ hQ)
    {v : X → ℝ} {C B : ℝ≥0} (hv : LipschitzWith C v)
    (c : ℝ) (hs : HasCompactSupport (fun x => v x-c))
    (hb : ∀ x, |v x| ≤ B) (hn : ∀ x, 0 ≤ v x)
    (V : Lp ℝ ∞ μ) (hV : ⇑V =ᵐ[μ] v) :
    energyLp μ (lpMultiplier μ V (SobolevSpace.toLp μ hQ f)) ≠ ∞ := by
  let W := boundedMultiplier μ (fun _ : X => (C : ℝ)) measurable_const C
    (fun _ => abs_of_nonneg C.coe_nonneg |>.le)
  have hr := (SobolevSpace.minimalSlope_isRelaxed μ hQ f).mul_lipschitz μ hv c hs hb hn
    (fun _ => C.coe_nonneg) (fun x => by simpa using localSlope_le_of_lipschitz hv x)
    V W hV (boundedMultiplier_coe μ _ _ _ _)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hr.energy_le μ)

noncomputable def SobolevSpace.mulLipschitz (f : SobolevSpace μ hQ)
    {v : X → ℝ} {C B : ℝ≥0} (hv : LipschitzWith C v)
    (c : ℝ) (hs : HasCompactSupport (fun x => v x-c))
    (hb : ∀ x, |v x| ≤ B) (hn : ∀ x, 0 ≤ v x)
    (V : Lp ℝ ∞ μ) (hV : ⇑V =ᵐ[μ] v) : SobolevSpace μ hQ :=
  ⟨lpMultiplier μ V (SobolevSpace.toLp μ hQ f),
    mul_lipschitz_finiteEnergy μ hQ f hv c hs hb hn V hV⟩

omit [BorelSpace X] in
 theorem form_sub_smul (f g : SobolevSpace μ hQ) (δ : ℝ) :
    2 * SobolevSpace.energy μ hQ (f-δ • g) =
      2 * SobolevSpace.energy μ hQ f - 2*δ*energyForm μ hQ f g +
        2*δ^2*SobolevSpace.energy μ hQ g := by
  rw [← energyForm_self, energyForm_sub_left, energyForm_comm μ hQ f (f-δ • g),
    energyForm_sub_left, energyForm_smul_left,
    energyForm_comm μ hQ (δ • g) (f-δ • g), energyForm_sub_left,
    energyForm_smul_left, energyForm_comm μ hQ g (δ • g), energyForm_smul_left,
    energyForm_self, energyForm_self, energyForm_comm μ hQ g f,
    energyForm_comm μ hQ f (δ • g), energyForm_smul_left, energyForm_comm μ hQ g f]
  ring

 theorem energyForm_lower_of_slope_variations (f g : SobolevSpace μ hQ)
    (H : Lp ℝ 2 μ) {r : ℝ} (hr : 0 < r)
    (hv : ∀ δ ∈ Ioo 0 r, IsRelaxedSlope μ (SobolevSpace.toLp μ hQ (f-δ • g))
      (SobolevSpace.minimalSlope μ hQ f-δ • H)) :
    inner ℝ (SobolevSpace.minimalSlope μ hQ f) H ≤ energyForm μ hQ f g := by
  have he (δ : ℝ) (hδ : δ ∈ Ioo 0 r) :
      inner ℝ (SobolevSpace.minimalSlope μ hQ f) H ≤ energyForm μ hQ f g +
        δ * (‖H‖^2/2 - SobolevSpace.energy μ hQ g) := by
    have h := ENNReal.toReal_le_of_le_ofReal (by positivity) ((hv δ hδ).energy_le μ)
    change SobolevSpace.energy μ hQ (f-δ • g) ≤ _ at h
    rw [norm_sub_sq_real, norm_smul, real_inner_smul_right,
      mul_pow, Real.norm_eq_abs, sq_abs, SobolevSpace.minimalSlope_norm_sq] at h
    have hform := form_sub_smul μ hQ f g δ
    have hmul : δ * (inner ℝ (SobolevSpace.minimalSlope μ hQ f) H) ≤
        δ * (energyForm μ hQ f g+δ*(‖H‖^2/2-SobolevSpace.energy μ hQ g)) := by
      nlinarith
    exact (mul_le_mul_iff_of_pos_left hδ.1).mp hmul
  have hn : Ioo 0 r ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hr
  have hl : Tendsto (fun δ : ℝ => energyForm μ hQ f g+
      δ*(‖H‖^2/2-SobolevSpace.energy μ hQ g)) (𝓝[>] 0) (𝓝 (energyForm μ hQ f g)) := by
    have hid : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    simpa using ((tendsto_const_nhds (x := energyForm μ hQ f g)).add
      (hid.mul_const (‖H‖^2/2-SobolevSpace.energy μ hQ g)))
  exact ge_of_tendsto hl (Filter.Eventually.mono hn fun δ hδ => he δ hδ)

end DaviesForm

variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem energyForm_weight_lower_inner (f g : SobolevSpace μ hQ)
    {v : X → ℝ} {C B : ℝ≥0} (hv : LipschitzWith C v)
    (c : ℝ) (hs : HasCompactSupport (fun x => v x-c))
    (hb : ∀ x, |v x| ≤ B) (hn : ∀ x, 0 ≤ v x)
    (V : Lp ℝ ∞ μ) (hV : ⇑V =ᵐ[μ] v)
    (hfg : SobolevSpace.toLp μ hQ g = lpMultiplier μ V (SobolevSpace.toLp μ hQ f))
    {L : ℝ} (hL : 0 ≤ L) (hvs : ∀ x, localSlope v x ≤ ENNReal.ofReal (L*v x)) :
    inner ℝ (SobolevSpace.minimalSlope μ hQ f)
      (lpMultiplier μ V (SobolevSpace.minimalSlope μ hQ f) -
        L • lpMultiplier μ V (lpAbs μ (SobolevSpace.toLp μ hQ f))) ≤ energyForm μ hQ f g := by
  let F := SobolevSpace.toLp μ hQ f
  let G := SobolevSpace.minimalSlope μ hQ f
  let H := lpMultiplier μ V G-L • lpMultiplier μ V (lpAbs μ F)
  apply energyForm_lower_of_slope_variations μ hQ f g H
    (r := 1/((B : ℝ)+1)) (by positivity)
  intro δ hδ
  have hdB : δ * (B : ℝ) < 1 := by
    have hz := (lt_div_iff₀ (show 0 < (B : ℝ)+1 by positivity)).mp hδ.2
    nlinarith [hδ.1]
  let θ : X → ℝ := fun x => 1-δ*v x
  have ht (x : X) : 0 ≤ θ x ∧ θ x ≤ 1 := by
    have hvx := (le_abs_self (v x)).trans (hb x)
    have hmul := mul_le_mul_of_nonneg_left hvx hδ.1.le
    have h0 := mul_nonneg hδ.1.le (hn x)
    dsimp [θ]
    constructor <;> linarith
  have htLip : LipschitzWith (‖δ‖₊*C) θ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have he := (lipschitzWith_const_mul_real hv δ).dist_le_mul x y
    simpa only [θ, Real.dist_eq, sub_sub_sub_cancel_left, abs_sub_comm] using he
  have htC : HasCompactSupport (fun x => θ x-(1-δ*c)) := by
    convert! (hs.mul_left (f := fun _ : X => (-δ))) using 1
    funext x
    dsimp [θ]
    ring
  have htB (x : X) : |θ x| ≤ (1 : ℝ≥0) := by
    rw [abs_of_nonneg (ht x).1]
    exact (ht x).2
  have htS (x : X) : localSlope θ x ≤ ENNReal.ofReal (δ*L*v x) := by
    have he : θ = fun x => (-δ)*v x-(-1) := by funext x; dsimp [θ]; ring
    rw [he, localSlope_sub_const, localSlope_const_mul, abs_neg, abs_of_pos hδ.1]
    calc
      _ ≤ ENNReal.ofReal δ * ENNReal.ofReal (L*v x) := mul_le_mul' le_rfl (hvs x)
      _ = _ := by rw [← ENNReal.ofReal_mul hδ.1.le]; congr 1; ring
  let T := boundedMultiplier μ θ htLip.continuous.measurable 1 htB
  have hT : ⇑T =ᵐ[μ] θ := boundedMultiplier_coe μ _ _ _ _
  let W : Lp ℝ ∞ μ := (δ*L) • V
  have hW : ⇑W =ᵐ[μ] (fun x => δ*L*v x) := by
    filter_upwards [Lp.coeFn_smul (δ*L) V, hV] with x hx hvx
    rw [hx, Pi.smul_apply, smul_eq_mul, hvx]
  have hr := (SobolevSpace.minimalSlope_isRelaxed μ hQ f).mul_lipschitz μ
    htLip (1-δ*c) htC htB (fun x => (ht x).1)
    (fun x => mul_nonneg (mul_nonneg hδ.1.le hL) (hn x)) htS T W hT hW
  have hTF : lpMultiplier μ T F = SobolevSpace.toLp μ hQ (f-δ • g) := by
    rw [map_sub, map_smul, hfg]
    apply Lp.ext
    filter_upwards [lpMultiplier_coe μ T F, lpMultiplier_coe μ V F,
      Lp.coeFn_sub F (δ • lpMultiplier μ V F), Lp.coeFn_smul δ (lpMultiplier μ V F), hT, hV]
      with x htF hvF hsub hsm ht0 hv0
    rw [htF, hsub, Pi.sub_apply, hsm, Pi.smul_apply, smul_eq_mul, ht0, hvF, hv0]
    dsimp [θ]
    ring
  have hTH : lpMultiplier μ T G+lpMultiplier μ W (lpAbs μ F) = G-δ • H := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (lpMultiplier μ T G) (lpMultiplier μ W (lpAbs μ F)),
      Lp.coeFn_sub G (δ • H), Lp.coeFn_smul δ H,
      Lp.coeFn_sub (lpMultiplier μ V G) (L • lpMultiplier μ V (lpAbs μ F)),
      Lp.coeFn_smul L (lpMultiplier μ V (lpAbs μ F)),
      lpMultiplier_coe μ T G, lpMultiplier_coe μ W (lpAbs μ F),
      lpMultiplier_coe μ V G, lpMultiplier_coe μ V (lpAbs μ F), hT, hV, hW]
      with x hadd hsub hsm hH hL0 htG hwF hvG hvF ht0 hv0 hw0
    dsimp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at *
    rw [hadd, hsub, hsm, htG, hwF, ht0, hw0]
    change H x = _ at hH
    rw [hH, hL0, hvG, hvF, hv0]
    dsimp only [θ]
    ring
  rwa [hTF, hTH] at hr

end RegularPointCoordinates

end OAI
