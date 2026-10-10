import Mathlib
import OAI.Analysis.RCDHeat.StrongLimit

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: PoissonExp, HeatMarkov, UniformContractions, HeatUniform, BoundedGeneratorRight, HeatGenerator. -/



open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
namespace RegularPointCoordinates
universe u
open Metric
section PoissonExp
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

 omit [CompleteSpace H] in
 theorem exp_smul_identity (a : ℝ) :
    NormedSpace.exp (a • (1 : H →L[ℝ] H)) = Real.exp a • (1 : H →L[ℝ] H) := by
  have h := NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := H →L[ℝ] H) a
  simpa only [Algebra.algebraMap_eq_smul_one, ← Real.exp_eq_exp_ℝ] using h.symm

 theorem exp_operator_poisson (R : H →L[ℝ] H) (a : ℝ) :
    NormedSpace.exp (a • (R-1)) = Real.exp (-a) • NormedSpace.exp (a • R) := by
  let : NormedAlgebra ℚ (H →L[ℝ] H) := NormedAlgebra.restrictScalars ℚ ℝ _
  have he : a • (R-1) = (-a) • (1 : H →L[ℝ] H) + a • R := by module
  rw [he, NormedSpace.exp_add_of_commute
    (((Commute.one_left R).smul_left (-a)).smul_right a), exp_smul_identity,
    smul_mul_assoc, one_mul]

 theorem poisson_weights_hasSum (a : ℝ) :
    HasSum (fun n : ℕ => Real.exp (-a) * ((n.factorial : ℝ)⁻¹ * a^n)) 1 := by
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a).mul_left (Real.exp (-a))
  simpa only [smul_eq_mul, ← Real.exp_eq_exp_ℝ, ← Real.exp_add, neg_add_cancel, Real.exp_zero] using h

 theorem poisson_operator_hasSum (R : H →L[ℝ] H) (a : ℝ) (x : H) :
    HasSum (fun n : ℕ => (Real.exp (-a) * ((n.factorial : ℝ)⁻¹ * a^n)) • (R^n) x)
      (NormedSpace.exp (a • (R-1)) x) := by
  have h := (ContinuousLinearMap.apply ℝ H x).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (a • R))
  have hs := h.const_smul (Real.exp (-a))
  simpa only [exp_operator_poisson, smul_pow, smul_apply, smul_smul,
    ContinuousLinearMap.apply_apply] using hs

 theorem exp_operator_mem_of_invariant {K : Set H} (hK : Convex ℝ K) (h0 : (0 : H) ∈ K)
    (hClosed : IsClosed K) (R : H →L[ℝ] H) (hR : ∀ x ∈ K, R x ∈ K)
    (a : ℝ) (ha : 0 ≤ a) (x : H) (hx : x ∈ K) :
    NormedSpace.exp (a • (R-1)) x ∈ K := by
  have hw (n : ℕ) : 0 ≤ Real.exp (-a) * ((n.factorial : ℝ)⁻¹ * a^n) := by positivity
  have hz (n : ℕ) : (R^n) x ∈ K := by
    induction n with
    | zero => simpa only [pow_zero, one_apply_eq_self] using hx
    | succ n ih => simpa only [pow_succ', mul_apply_eq_comp] using hR _ ih
  apply hClosed.mem_of_tendsto (poisson_operator_hasSum R a x).tendsto_sum_nat
  apply Eventually.of_forall
  intro n
  apply convex_sum_mem_of_le_one hK h0 (Finset.range n) _ _ (fun i _ => hw i) _
    (fun i _ => hz i)
  have hs := (poisson_weights_hasSum a).summable.sum_le_tsum (Finset.range n) (fun i _ => hw i)
  simpa only [(poisson_weights_hasSum a).tsum_eq] using hs

end PoissonExp

section HeatMarkov
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem heatApprox_poisson (t : ℝ) (i : ℕ) :
    heatApprox μ hQ t i = NormedSpace.exp
      ((t / heatStep i) • (resolventLp μ hQ (heatStep i) (heatStep_pos i) - 1)) := by
  dsimp [heatApprox, expNeg, yosida]
  congr 1
  rw [← smul_neg, neg_sub, smul_smul, div_eq_mul_inv]

 omit [MetricSpace X] in
 theorem lp_upper_convex (c : ℝ) : Convex ℝ {f : Lp ℝ 2 μ | ∀ᵐ x ∂μ, f x ≤ c} := by
  intro f hf g hg a b ha hb hab
  filter_upwards [hf, hg, Lp.coeFn_add (a • f) (b • g), Lp.coeFn_smul a f,
    Lp.coeFn_smul b g] with x hfx hgx hadd haf hbg
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hadd haf hbg
  rw [hadd, haf, hbg]
  calc
    _ ≤ a * c + b * c := add_le_add (mul_le_mul_of_nonneg_left hfx ha)
      (mul_le_mul_of_nonneg_left hgx hb)
    _ = c := by rw [← add_mul, hab, one_mul]

 omit [MetricSpace X] in
 theorem lp_upper_closed (c : ℝ) (hc : 0 ≤ c) :
    IsClosed {f : Lp ℝ 2 μ | ∀ᵐ x ∂μ, f x ≤ c} := by
  let hφ : LipschitzWith 1 (fun x : ℝ => min x c) := LipschitzWith.id.min_const c
  have hφ0 : min (0 : ℝ) c = 0 := min_eq_left hc
  have heq : {f : Lp ℝ 2 μ | ∀ᵐ x ∂μ, f x ≤ c} =
      {f : Lp ℝ 2 μ | hφ.compLp hφ0 f = f} := by
    ext f
    constructor
    · intro hf
      apply Lp.ext
      filter_upwards [hf, hφ.coeFn_compLp hφ0 f] with x hx hφx
      exact hφx.trans (min_eq_left hx)
    · intro hf
      have hae := hφ.coeFn_compLp hφ0 f
      rw [hf] at hae
      exact hae.mono fun x hx => by rw [hx]; exact min_le_right _ _
  rw [heq]
  exact isClosed_eq (hφ.continuous_compLp hφ0) continuous_id

 omit [MetricSpace X] in
 theorem lp_nonneg_convex : Convex ℝ (Set.Ici (0 : Lp ℝ 2 μ)) := by
  intro f hf g hg a b ha hb _
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [(Lp.coeFn_nonneg f).mpr hf, (Lp.coeFn_nonneg g).mpr hg,
    Lp.coeFn_add (a • f) (b • g), Lp.coeFn_smul a f, Lp.coeFn_smul b g]
    with x hfx hgx hadd haf hbg
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hadd haf hbg
  rw [hadd, haf, hbg]
  exact add_nonneg (mul_nonneg ha hfx) (mul_nonneg hb hgx)

 theorem heatApprox_nonneg (t : ℝ) (ht : 0 ≤ t) (i : ℕ) (f : Lp ℝ 2 μ)
    (hf : 0 ≤ f) : 0 ≤ heatApprox μ hQ t i f := by
  rw [heatApprox_poisson]
  exact exp_operator_mem_of_invariant (lp_nonneg_convex μ) (by exact Set.self_mem_Ici) isClosed_Ici
    (resolventLp μ hQ (heatStep i) (heatStep_pos i))
    (fun f hf => resolventLp_nonneg μ hQ _ _ f hf) _
    (div_nonneg ht (heatStep_pos i).le) f hf

 theorem heatApprox_le_const (t : ℝ) (ht : 0 ≤ t) (i : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (f : Lp ℝ 2 μ) (hf : ∀ᵐ x ∂μ, f x ≤ c) : ∀ᵐ x ∂μ, heatApprox μ hQ t i f x ≤ c := by
  rw [heatApprox_poisson]
  apply exp_operator_mem_of_invariant (lp_upper_convex μ c) _ (lp_upper_closed μ c hc)
    (resolventLp μ hQ (heatStep i) (heatStep_pos i))
    (fun f hf => resolventLp_le_const μ hQ _ _ hc f hf) _
    (div_nonneg ht (heatStep_pos i).le) f hf
  exact Lp.coeFn_zero ℝ 2 μ |>.mono fun x hx => by simpa only [hx, Pi.zero_apply] using hc

variable [ProperSpace X] [BorelSpace X] [μ.Regular]

 theorem heatFlow_nonneg (t : ℝ) (ht : 0 ≤ t) (f : Lp ℝ 2 μ) (hf : 0 ≤ f) :
    0 ≤ heatFlow μ hQ t ht f :=
  (isClosed_Ici (a := (0 : Lp ℝ 2 μ))).mem_of_tendsto (heatApprox_tendsto μ hQ t ht f)
    (Eventually.of_forall fun i => heatApprox_nonneg μ hQ t ht i f hf)

 theorem heatFlow_le_const (t : ℝ) (ht : 0 ≤ t) {c : ℝ} (hc : 0 ≤ c)
    (f : Lp ℝ 2 μ) (hf : ∀ᵐ x ∂μ, f x ≤ c) : ∀ᵐ x ∂μ, heatFlow μ hQ t ht f x ≤ c :=
  (lp_upper_closed μ c hc).mem_of_tendsto (heatApprox_tendsto μ hQ t ht f)
    (Eventually.of_forall fun i => heatApprox_le_const μ hQ t ht i hc f hf)

 theorem heatFlow_mono (t : ℝ) (ht : 0 ≤ t) {f g : Lp ℝ 2 μ} (hfg : f ≤ g) :
    heatFlow μ hQ t ht f ≤ heatFlow μ hQ t ht g := by
  have h := heatFlow_nonneg μ hQ t ht (g-f) (sub_nonneg.mpr hfg)
  simpa only [map_sub, sub_nonneg] using h

end HeatMarkov

section UniformContractions
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  {ι α : Type*} {l : Filter ι} {s : Set α}

 theorem tendstoUniformlyOn_contractions_of_denseRange {D : H → H} (hD : DenseRange D)
    {A : ι → α → H →L[ℝ] H} {B : α → H →L[ℝ] H}
    (hA : ∀ i t, t ∈ s → ‖A i t‖ ≤ 1) (hB : ∀ t ∈ s, ‖B t‖ ≤ 1)
    (hC : ∀ y, TendstoUniformlyOn (fun i t => A i t (D y)) (fun t => B t (D y)) l s)
    (x : H) : TendstoUniformlyOn (fun i t => A i t x) (fun t => B t x) l s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨y, hy⟩ := Metric.denseRange_iff.mp hD x (ε/4) (by linarith)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hC y) (ε/2) (by linarith)] with i hi
  intro t ht
  have hclose (T : H →L[ℝ] H) (hT : ‖T‖ ≤ 1) (u v : H) :
      dist (T u) (T v) ≤ dist u v := by
    simp only [dist_eq_norm, ← map_sub]
    simpa only [one_mul] using T.le_of_opNorm_le hT (u-v)
  calc
    dist (B t x) (A i t x) ≤ dist (B t x) (B t (D y)) +
        dist (B t (D y)) (A i t (D y)) + dist (A i t (D y)) (A i t x) := by
      grw [dist_triangle (B t x) (B t (D y)) (A i t x),
        dist_triangle (B t (D y)) (A i t (D y)) (A i t x)]
      ring_nf
      exact le_rfl
    _ ≤ dist x (D y) + dist (B t (D y)) (A i t (D y)) + dist (D y) x :=
      add_le_add (add_le_add (hclose _ (hB t ht) x (D y)) le_rfl)
        (hclose _ (hA i t ht) (D y) x)
    _ < ε := by
      have h := hi t ht
      rw [dist_comm (D y) x]
      linarith

 theorem tendstoUniformlyOn_contraction_apply
    {A : ι → α → H →L[ℝ] H} {B : α → H →L[ℝ] H}
    (hA : ∀ i t, t ∈ s → ‖A i t‖ ≤ 1)
    (hB : ∀ x, TendstoUniformlyOn (fun i t => A i t x) (fun t => B t x) l s)
    {v : ι → H} {w : H} (hv : Tendsto v l (𝓝 w)) :
    TendstoUniformlyOn (fun i t => A i t (v i)) (fun t => B t w) l s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hB w) (ε/2) (by linarith),
    Metric.tendsto_nhds.mp hv (ε/2) (by linarith)] with i hi hvi
  intro t ht
  have hn := (A i t).le_of_opNorm_le (hA i t ht) (w-v i)
  simp only [map_sub, one_mul, ← dist_eq_norm] at hn
  calc
    dist (B t w) (A i t (v i)) ≤ dist (B t w) (A i t w) + dist (A i t w) (A i t (v i)) :=
      dist_triangle _ _ _
    _ ≤ dist (B t w) (A i t w) + dist w (v i) := add_le_add le_rfl hn
    _ < ε := by rw [dist_comm w (v i)]; linarith [hi t ht]

end UniformContractions

section HeatUniform
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem heatStep_tendsto : Tendsto heatStep atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

 theorem resolventLp_one_error (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    ‖resolventLp μ hQ t ht (resolventLp μ hQ 1 zero_lt_one f) -
      resolventLp μ hQ 1 zero_lt_one f‖ ≤ t * (2*‖f‖) := by
  have he := congrArg (fun C : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ =>
    C (resolventLp μ hQ 1 zero_lt_one f)) (yosida_smul μ hQ t ht)
  simp only [smul_apply, sub_apply, one_apply_eq_self] at he
  calc
    _ = ‖resolventLp μ hQ 1 zero_lt_one f -
        resolventLp μ hQ t ht (resolventLp μ hQ 1 zero_lt_one f)‖ := norm_sub_rev _ _
    _ = t * ‖yosida μ hQ t ht (resolventLp μ hQ 1 zero_lt_one f)‖ := by
      rw [← he, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    _ ≤ _ := mul_le_mul_of_nonneg_left (yosida_resolvent_one_norm_le μ hQ t ht f) ht.le

variable [ProperSpace X] [BorelSpace X] [μ.Regular]

 theorem resolvent_heatStep_tendsto (f : Lp ℝ 2 μ) :
    Tendsto (fun i => resolventLp μ hQ (heatStep i) (heatStep_pos i) f) atTop (𝓝 f) := by
  change Tendsto _ atTop (𝓝 ((1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) f))
  apply tendsto_contraction_of_denseRange (resolventLp_denseRange μ hQ 1 zero_lt_one)
    (fun i => resolventLp_norm_le μ hQ (heatStep i) (heatStep_pos i))
    ContinuousLinearMap.norm_id_le
  intro g
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun i => norm_nonneg _) (fun i => resolventLp_one_error μ hQ _ _ g)
  simpa only [zero_mul] using heatStep_tendsto.mul_const (2*‖g‖)

 theorem yosida_heatStep_core_tendsto (f : Lp ℝ 2 μ) :
    Tendsto (fun i => yosida μ hQ (heatStep i) (heatStep_pos i)
      (resolventLp μ hQ 1 zero_lt_one f)) atTop
      (𝓝 (f-resolventLp μ hQ 1 zero_lt_one f)) := by
  have he (i : ℕ) := congrArg (fun C : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => C f)
    (yosida_resolvent_one μ hQ (heatStep i) (heatStep_pos i))
  simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self] at he
  simpa only [he] using resolvent_heatStep_tendsto μ hQ (f-resolventLp μ hQ 1 zero_lt_one f)

 

noncomputable def heatAt (t : ℝ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  heatFlow μ hQ (max t 0) (le_max_right _ _)

 theorem heatAt_of_nonneg (t : ℝ) (ht : 0 ≤ t) : heatAt μ hQ t = heatFlow μ hQ t ht := by
  simp only [heatAt, max_eq_left ht]

 theorem heatAt_zero : heatAt μ hQ 0 = 1 := by rw [heatAt_of_nonneg μ hQ 0 le_rfl, heatFlow_zero]

 theorem heatAt_continuous (f : Lp ℝ 2 μ) : Continuous (fun t : ℝ => heatAt μ hQ t f) := by
  let q : ℝ → ℝ≥0 := fun t => ⟨max t 0, le_max_right t 0⟩
  have hq : Continuous q :=
    ((continuous_id : Continuous (fun t : ℝ => t)).max continuous_const).subtype_mk _
  change Continuous ((fun t : ℝ≥0 => heatFlow μ hQ t t.coe_nonneg f) ∘ q)
  exact (heatFlow_continuous μ hQ f).comp hq

 theorem heatAt_norm_le (t : ℝ) : ‖heatAt μ hQ t‖ ≤ 1 := heatFlow_norm_le μ hQ _ _

 theorem heatApprox_core_error (t : ℝ) (ht : 0 ≤ t) (i : ℕ) (f : Lp ℝ 2 μ) :
    ‖heatApprox μ hQ t i (resolventLp μ hQ 1 zero_lt_one (resolventLp μ hQ 1 zero_lt_one f)) -
      heatFlow μ hQ t ht (resolventLp μ hQ 1 zero_lt_one (resolventLp μ hQ 1 zero_lt_one f))‖ ≤
      (4*t*‖f‖) * heatStep i := by
  apply le_of_tendsto (tendsto_const_nhds.sub (heatApprox_tendsto μ hQ t ht _)).norm
  filter_upwards [eventually_ge_atTop i] with j hij
  have hs : heatStep j ≤ heatStep i := pow_le_pow_of_le_one (by norm_num) (by norm_num) hij
  have hd : |heatStep j-heatStep i| ≤ heatStep i := by
    rw [abs_of_nonpos (sub_nonpos.mpr hs)]
    linarith [heatStep_pos j]
  calc
    _ ≤ t * ‖(yosida μ hQ (heatStep i) (heatStep_pos i) -
        yosida μ hQ (heatStep j) (heatStep_pos j))
        (resolventLp μ hQ 1 zero_lt_one (resolventLp μ hQ 1 zero_lt_one f))‖ :=
      expNeg_difference_bound (yosida_nonneg μ hQ _ _) (yosida_nonneg μ hQ _ _)
        (yosida_commute μ hQ _ _ _ _) t ht _
    _ ≤ t * (4 * |heatStep j-heatStep i| * ‖f‖) :=
      mul_le_mul_of_nonneg_left (yosida_difference_on_core_norm_le μ hQ _ _ _ _ f) ht
    _ ≤ (4*t*‖f‖) * heatStep i := by
      nlinarith [mul_le_mul_of_nonneg_left hd (mul_nonneg ht (norm_nonneg f))]

 theorem heatApprox_uniform (T : ℝ) (f : Lp ℝ 2 μ) :
    TendstoUniformlyOn (fun i t => heatApprox μ hQ t i f) (fun t => heatAt μ hQ t f)
      atTop (Icc 0 T) := by
  apply tendstoUniformlyOn_contractions_of_denseRange
    (resolventLp_sq_denseRange μ hQ 1 zero_lt_one)
    (fun i t ht => heatApprox_norm_le μ hQ t ht.1 i)
    (fun t _ => heatAt_norm_le μ hQ t)
  intro g
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hz : Tendsto (fun i => (4*T*‖g‖) * heatStep i) atTop (𝓝 0) := by
    simpa only [mul_zero] using heatStep_tendsto.const_mul (4*T*‖g‖)
  filter_upwards [hz.eventually (gt_mem_nhds hε)] with i hi
  intro t ht
  rw [heatAt_of_nonneg μ hQ t ht.1, dist_eq_norm, norm_sub_rev]
  apply lt_of_le_of_lt (heatApprox_core_error μ hQ t ht.1 i g)
  calc
    (4*t*‖g‖) * heatStep i ≤ (4*T*‖g‖) * heatStep i := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht.2 (by norm_num)) (norm_nonneg g))
        (heatStep_pos i).le
    _ < ε := hi

end HeatUniform

section BoundedGeneratorRight
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

 theorem expNeg_apply_hasDerivAt_right (A : H →L[ℝ] H) (x : H) (t : ℝ) :
    HasDerivAt (fun s => expNeg A s x) (- expNeg A t (A x)) t := by
  have hc : Commute A (expNeg A t) := ((Commute.refl A).neg_right.smul_right t).exp_right
  have he := congrArg (fun C : H →L[ℝ] H => C x) hc.eq
  simp only [mul_apply_eq_comp] at he
  simpa only [he] using expNeg_apply_hasDerivAt A x t

end BoundedGeneratorRight

variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem yosida_resolvent_commute (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    Commute (yosida μ hQ r hr) (resolventLp μ hQ s hs) := by
  let : SMulCommClass ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :=
    Algebra.to_smulCommClass (R := ℝ) (A := Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
  let : IsScalarTower ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :=
    IsScalarTower.right (R := ℝ) (A := Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
  exact ((Commute.one_left _).sub_left (resolventLp_commute μ hQ r s hr hs)).smul_left r⁻¹

 theorem heatApprox_resolvent_commute (t s : ℝ) (hs : 0 < s) (i : ℕ) :
    Commute (heatApprox μ hQ t i) (resolventLp μ hQ s hs) := by
  let : SMulCommClass ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :=
    Algebra.to_smulCommClass (R := ℝ) (A := Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
  let : IsScalarTower ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :=
    IsScalarTower.right (R := ℝ) (A := Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
  exact ((yosida_resolvent_commute μ hQ (heatStep i) s (heatStep_pos i) hs).neg_left.smul_left t).exp_left

 theorem heatApprox_core_hasDerivAt (t : ℝ) (i : ℕ) (f : Lp ℝ 2 μ) :
    HasDerivAt (fun s => heatApprox μ hQ s i (resolventLp μ hQ 1 zero_lt_one f))
      (-heatApprox μ hQ t i
        (yosida μ hQ (heatStep i) (heatStep_pos i) (resolventLp μ hQ 1 zero_lt_one f))) t :=
  expNeg_apply_hasDerivAt_right _ _ _

variable [ProperSpace X] [BorelSpace X] [μ.Regular]

 theorem heatAt_resolvent_commute (t s : ℝ) (hs : 0 < s) :
    Commute (heatAt μ hQ t) (resolventLp μ hQ s hs) := by
  show _ * _ = _ * _
  apply ContinuousLinearMap.ext
  intro f
  have he (i : ℕ) := congrArg (fun C : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => C f)
    (heatApprox_resolvent_commute μ hQ (max t 0) s hs i).eq
  simp only [mul_apply_eq_comp] at he
  apply tendsto_nhds_unique (heatApprox_tendsto μ hQ (max t 0) (le_max_right _ _) _)
  exact ((resolventLp μ hQ s hs).continuous.continuousAt.tendsto.comp
    (heatApprox_tendsto μ hQ (max t 0) (le_max_right _ _) f)).congr'
    (Eventually.of_forall fun i => (he i).symm)

 theorem heatAt_core_hasDerivAt (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    HasDerivAt (fun s => heatAt μ hQ s (resolventLp μ hQ 1 zero_lt_one f))
      (-heatAt μ hQ t (f-resolventLp μ hQ 1 zero_lt_one f)) t := by
  have huni := (tendstoUniformlyOn_contraction_apply
    (fun i s (hs : s ∈ Icc (0 : ℝ) (t+1)) => heatApprox_norm_le μ hQ s hs.1 i)
    (heatApprox_uniform μ hQ (t+1)) (yosida_heatStep_core_tendsto μ hQ f)).neg
  apply hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo (huni.mono Ioo_subset_Icc_self)
    (Eventually.of_forall fun i s (_ : s ∈ Ioo (0 : ℝ) (t+1)) =>
      heatApprox_core_hasDerivAt μ hQ s i f) _ ⟨ht, by linarith⟩
  intro s hs
  rw [heatAt_of_nonneg μ hQ s hs.1.le]
  exact heatApprox_tendsto μ hQ s hs.1.le _

 
noncomputable def heatCore (t : ℝ) (f : Lp ℝ 2 μ) : SobolevSpace μ hQ :=
  SobolevSpace.resolventAt μ hQ 1 zero_lt_one (heatAt μ hQ t f)

 theorem heatCore_toLp (t : ℝ) (f : Lp ℝ 2 μ) :
    SobolevSpace.toLp μ hQ (heatCore μ hQ t f) =
      heatAt μ hQ t (resolventLp μ hQ 1 zero_lt_one f) := by
  have he := congrArg (fun C : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => C f)
    (heatAt_resolvent_commute μ hQ t 1 zero_lt_one).eq
  exact he.symm

 theorem heatCore_laplacian (t : ℝ) (f : Lp ℝ 2 μ) :
    IsWeakLaplacian μ hQ (heatCore μ hQ t f)
      (heatAt μ hQ t (resolventLp μ hQ 1 zero_lt_one f-f)) := by
  have h := SobolevSpace.resolventAt_weak_laplacian μ hQ 1 zero_lt_one (heatAt μ hQ t f)
  change IsWeakLaplacian μ hQ (heatCore μ hQ t f)
    (1⁻¹ • (SobolevSpace.toLp μ hQ (heatCore μ hQ t f) - heatAt μ hQ t f)) at h
  simpa only [inv_one, one_smul, heatCore_toLp, map_sub] using h

 theorem heatCore_hasDerivAt (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    HasDerivAt (fun s => SobolevSpace.toLp μ hQ (heatCore μ hQ s f))
      (heatAt μ hQ t (resolventLp μ hQ 1 zero_lt_one f-f)) t := by
  simpa only [heatCore_toLp, map_sub, neg_sub] using heatAt_core_hasDerivAt μ hQ t ht f

end RegularPointCoordinates

end OAI
