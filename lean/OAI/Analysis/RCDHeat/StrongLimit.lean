import Mathlib
import OAI.Analysis.RCDHeat.ResolventFamily

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: StrongLimit, StrongApply, HeatFlow, BoundedTime, DenseTendsto, HeatContinuity, ParameterizedMarkov, ConvexSum. -/



open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
namespace RegularPointCoordinates
universe u
open Metric
section StrongLimit
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

 theorem bounded_cauchy_of_denseRange {D : H → H} (hD : DenseRange D)
    (A : ℕ → H →L[ℝ] H) (hA : ∀ i, ‖A i‖ ≤ 1)
    (hC : ∀ x, CauchySeq (fun i => A i (D x))) (x : H) :
    CauchySeq (fun i => A i x) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨y, hy⟩ := Metric.denseRange_iff.mp hD x (ε/4) (by linarith)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hC y) (ε/2) (by linarith)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hclose (i : ℕ) (u v : H) : dist (A i u) (A i v) ≤ dist u v := by
    simp only [dist_eq_norm, ← map_sub]
    simpa only [one_mul] using (A i).le_of_opNorm_le (hA i) (u-v)
  calc
    dist (A m x) (A n x) ≤ dist (A m x) (A m (D y)) +
        dist (A m (D y)) (A n (D y)) + dist (A n (D y)) (A n x) := by
      grw [dist_triangle (A m x) (A m (D y)) (A n x),
        dist_triangle (A m (D y)) (A n (D y)) (A n x)]
      ring_nf
      exact le_rfl
    _ ≤ dist x (D y) + dist (A m (D y)) (A n (D y)) + dist (D y) x :=
      add_le_add (add_le_add (hclose m x (D y)) le_rfl) (hclose n (D y) x)
    _ < ε := by
      have h := hN m hm n hn
      rw [dist_comm (D y) x]
      linarith

variable [CompleteSpace H]

 
noncomputable def contractionStrongLimit (A : ℕ → H →L[ℝ] H)
    (hA : ∀ i, ‖A i‖ ≤ 1) (hC : ∀ x, CauchySeq (fun i => A i x)) : H →L[ℝ] H :=
  ContinuousLinearMap.ofTendstoOfBoundedRange
    (fun x => atTop.limUnder (fun i => A i x)) A
    (tendsto_pi_nhds.mpr fun x => tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hC x)))
    (isBounded_iff_forall_norm_le.mpr ⟨1, fun _ ⟨i, hi⟩ => hi ▸ hA i⟩)

 theorem contractionStrongLimit_tendsto (A : ℕ → H →L[ℝ] H)
    (hA : ∀ i, ‖A i‖ ≤ 1) (hC : ∀ x, CauchySeq (fun i => A i x)) (x : H) :
    Tendsto (fun i => A i x) atTop (𝓝 (contractionStrongLimit A hA hC x)) :=
  tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hC x))

 theorem contractionStrongLimit_norm_le (A : ℕ → H →L[ℝ] H)
    (hA : ∀ i, ‖A i‖ ≤ 1) (hC : ∀ x, CauchySeq (fun i => A i x)) :
    ‖contractionStrongLimit A hA hC‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  exact le_of_tendsto (contractionStrongLimit_tendsto A hA hC x).norm
    (Eventually.of_forall fun i => (A i).le_of_opNorm_le (hA i) x)

end StrongLimit

section StrongApply
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  {α : Type*} {l : Filter α}

 theorem tendsto_contraction_apply {A : α → H →L[ℝ] H} {B : H →L[ℝ] H}
    (hA : ∀ i, ‖A i‖ ≤ 1) (hB : ∀ x, Tendsto (fun i => A i x) l (𝓝 (B x)))
    {v : α → H} {w : H} (hv : Tendsto v l (𝓝 w)) :
    Tendsto (fun i => A i (v i)) l (𝓝 (B w)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun i => norm_nonneg _) (fun i => ?_)
    (by simpa only [add_zero] using
      ((tendsto_iff_norm_sub_tendsto_zero.mp hv).add
        (tendsto_iff_norm_sub_tendsto_zero.mp (hB w))))
  have h := (A i).le_of_opNorm_le (hA i) (v i-w)
  simp only [map_sub, one_mul] at h
  calc
    ‖A i (v i) - B w‖ ≤ ‖A i (v i) - A i w‖ + ‖A i w - B w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖v i-w‖ + ‖A i w-B w‖ := add_le_add h le_rfl

end StrongApply

section HeatFlow
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 
noncomputable def heatStep (i : ℕ) : ℝ := (1/2 : ℝ)^i

 theorem heatStep_pos (i : ℕ) : 0 < heatStep i := by
  exact pow_pos (by norm_num) _

 
noncomputable def heatApprox (t : ℝ) (i : ℕ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  expNeg (yosida μ hQ (heatStep i) (heatStep_pos i)) t

 theorem heatApprox_norm_le (t : ℝ) (ht : 0 ≤ t) (i : ℕ) :
    ‖heatApprox μ hQ t i‖ ≤ 1 :=
  expNeg_norm_le _ (yosida_nonneg μ hQ _ _) t ht

 theorem heatApprox_core_cauchy (t : ℝ) (ht : 0 ≤ t) (f : Lp ℝ 2 μ) :
    CauchySeq (fun i => heatApprox μ hQ t i
      (resolventLp μ hQ 1 zero_lt_one (resolventLp μ hQ 1 zero_lt_one f))) := by
  apply cauchySeq_of_le_tendsto_0' (fun i => (4*t*‖f‖) * heatStep i)
  · intro i j hij
    have hs : heatStep j ≤ heatStep i :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hij
    have hd : |heatStep j-heatStep i| ≤ heatStep i := by
      rw [abs_of_nonpos (sub_nonpos.mpr hs)]
      linarith [heatStep_pos j]
    rw [dist_eq_norm]
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
  · simpa only [heatStep, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num : (1/2 : ℝ) < 1)).const_mul (4*t*‖f‖)

variable [ProperSpace X] [BorelSpace X] [μ.Regular]

 theorem heatApprox_cauchy (t : ℝ) (ht : 0 ≤ t) (f : Lp ℝ 2 μ) :
    CauchySeq (fun i => heatApprox μ hQ t i f) :=
  bounded_cauchy_of_denseRange (resolventLp_sq_denseRange μ hQ 1 zero_lt_one)
    (heatApprox μ hQ t) (heatApprox_norm_le μ hQ t ht)
    (heatApprox_core_cauchy μ hQ t ht) f

 
noncomputable def heatFlow (t : ℝ) (ht : 0 ≤ t) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  contractionStrongLimit (heatApprox μ hQ t) (heatApprox_norm_le μ hQ t ht)
    (heatApprox_cauchy μ hQ t ht)

 theorem heatApprox_tendsto (t : ℝ) (ht : 0 ≤ t) (f : Lp ℝ 2 μ) :
    Tendsto (fun i => heatApprox μ hQ t i f) atTop (𝓝 (heatFlow μ hQ t ht f)) :=
  contractionStrongLimit_tendsto _ _ _ f

 theorem heatFlow_norm_le (t : ℝ) (ht : 0 ≤ t) : ‖heatFlow μ hQ t ht‖ ≤ 1 :=
  contractionStrongLimit_norm_le _ _ _

 theorem heatFlow_zero : heatFlow μ hQ 0 le_rfl = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply tendsto_nhds_unique (heatApprox_tendsto μ hQ 0 le_rfl f)
  simpa only [heatApprox, expNeg_zero, one_apply_eq_self] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => f) atTop (𝓝 f))

 theorem heatFlow_add (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    heatFlow μ hQ (s+t) (add_nonneg hs ht) = heatFlow μ hQ s hs * heatFlow μ hQ t ht := by
  apply ContinuousLinearMap.ext
  intro f
  apply tendsto_nhds_unique (heatApprox_tendsto μ hQ (s+t) (add_nonneg hs ht) f)
  have h := tendsto_contraction_apply (heatApprox_norm_le μ hQ s hs)
    (heatApprox_tendsto μ hQ s hs) (heatApprox_tendsto μ hQ t ht f)
  simpa only [heatApprox, expNeg_add, mul_apply_eq_comp] using h

 theorem heatFlow_commute (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Commute (heatFlow μ hQ s hs) (heatFlow μ hQ t ht) := by
  show _ * _ = _ * _
  rw [← heatFlow_add, ← heatFlow_add]
  congr 1
  exact add_comm s t

end HeatFlow

section BoundedTime
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

 theorem expNeg_time_difference_bound (A : H →L[ℝ] H)
    (hA : ∀ x : H, 0 ≤ inner ℝ x (A x)) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (x : H) :
    ‖expNeg A s x - expNeg A t x‖ ≤ |s-t| * ‖A x‖ := by
  have hsA (x : H) : 0 ≤ inner ℝ x ((s • A) x) := by
    simp only [smul_apply, real_inner_smul_right]
    exact mul_nonneg hs (hA x)
  have htA (x : H) : 0 ≤ inner ℝ x ((t • A) x) := by
    simp only [smul_apply, real_inner_smul_right]
    exact mul_nonneg ht (hA x)
  have h := expNeg_difference_bound hsA htA
    (((Commute.refl A).smul_left s).smul_right t) 1 zero_le_one x
  simpa only [expNeg, one_smul, smul_neg, sub_apply, smul_apply,
    ← sub_smul, norm_smul, Real.norm_eq_abs, one_mul] using h

end BoundedTime

section DenseTendsto
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  {α : Type*} {l : Filter α}

 theorem tendsto_contraction_of_denseRange {D : H → H} (hD : DenseRange D)
    {A : α → H →L[ℝ] H} {B : H →L[ℝ] H}
    (hA : ∀ i, ‖A i‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hC : ∀ x, Tendsto (fun i => A i (D x)) l (𝓝 (B (D x)))) (x : H) :
    Tendsto (fun i => A i x) l (𝓝 (B x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨y, hy⟩ := Metric.denseRange_iff.mp hD x (ε/4) (by linarith)
  filter_upwards [Metric.tendsto_nhds.mp (hC y) (ε/2) (by linarith)] with i hi
  have hc (C : H →L[ℝ] H) (hC : ‖C‖ ≤ 1) (v w : H) : dist (C v) (C w) ≤ dist v w := by
    simp only [dist_eq_norm, ← map_sub]
    simpa only [one_mul] using C.le_of_opNorm_le hC (v-w)
  calc
    dist (A i x) (B x) ≤ dist (A i x) (A i (D y)) +
        dist (A i (D y)) (B (D y)) + dist (B (D y)) (B x) := by
      grw [dist_triangle (A i x) (A i (D y)) (B x),
        dist_triangle (A i (D y)) (B (D y)) (B x)]
      ring_nf
      exact le_rfl
    _ ≤ dist x (D y) + dist (A i (D y)) (B (D y)) + dist (D y) x :=
      add_le_add (add_le_add (hc _ (hA i) _ _) le_rfl) (hc _ hB _ _)
    _ < ε := by
      rw [dist_comm (D y) x]
      linarith

end DenseTendsto

section HeatContinuity
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem yosida_resolvent_one_norm_le (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    ‖yosida μ hQ t ht (resolventLp μ hQ 1 zero_lt_one f)‖ ≤ 2 * ‖f‖ := by
  have he := congrArg (fun C : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => C f)
    (yosida_resolvent_one μ hQ t ht)
  simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self] at he
  rw [he]
  have hf := (resolventLp μ hQ 1 zero_lt_one).le_of_opNorm_le
    (resolventLp_norm_le μ hQ 1 zero_lt_one) f
  have hg := (resolventLp μ hQ t ht).le_of_opNorm_le
    (resolventLp_norm_le μ hQ t ht) (f-resolventLp μ hQ 1 zero_lt_one f)
  simp only [one_mul] at hf hg
  exact hg.trans ((norm_sub_le _ _).trans (by linarith))

variable [ProperSpace X] [BorelSpace X] [μ.Regular]

 theorem heatFlow_core_time_bound (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (f : Lp ℝ 2 μ) :
    ‖heatFlow μ hQ s hs (resolventLp μ hQ 1 zero_lt_one f) -
      heatFlow μ hQ t ht (resolventLp μ hQ 1 zero_lt_one f)‖ ≤ |s-t| * (2*‖f‖) := by
  apply le_of_tendsto ((heatApprox_tendsto μ hQ s hs _).sub
    (heatApprox_tendsto μ hQ t ht _)).norm
  apply Eventually.of_forall
  intro i
  exact (expNeg_time_difference_bound _ (yosida_nonneg μ hQ _ _) s t hs ht _).trans
    (mul_le_mul_of_nonneg_left (yosida_resolvent_one_norm_le μ hQ _ _ f) (abs_nonneg _))

 theorem heatFlow_core_lipschitz (f : Lp ℝ 2 μ) :
    LipschitzWith (2*‖f‖₊) (fun t : ℝ≥0 =>
      heatFlow μ hQ t t.coe_nonneg (resolventLp μ hQ 1 zero_lt_one f)) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro s t
  simpa only [dist_eq_norm, NNReal.dist_eq, Real.norm_eq_abs,
    NNReal.coe_mul, NNReal.coe_ofNat, coe_nnnorm, mul_comm (2*‖f‖)] using
    heatFlow_core_time_bound μ hQ s t s.coe_nonneg t.coe_nonneg f

 theorem heatFlow_continuous (f : Lp ℝ 2 μ) :
    Continuous (fun t : ℝ≥0 => heatFlow μ hQ t t.coe_nonneg f) := by
  rw [continuous_iff_continuousAt]
  intro t
  apply tendsto_contraction_of_denseRange (resolventLp_denseRange μ hQ 1 zero_lt_one)
    (fun s : ℝ≥0 => heatFlow_norm_le μ hQ s s.coe_nonneg)
    (heatFlow_norm_le μ hQ t t.coe_nonneg)
  intro g
  exact (heatFlow_core_lipschitz μ hQ g).continuous.tendsto t

 theorem heatFlow_tendsto_zero (f : Lp ℝ 2 μ) :
    Tendsto (fun t : ℝ≥0 => heatFlow μ hQ t t.coe_nonneg f) (𝓝 0) (𝓝 f) := by
  simpa only [NNReal.coe_zero, heatFlow_zero, one_apply_eq_self] using
    (heatFlow_continuous μ hQ f).tendsto 0

end HeatContinuity

section ParameterizedMarkov
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem SobolevSpace.resolventAt_contraction_fixed (t : ℝ) (ht : 0 < t)
    {φ : ℝ → ℝ} (hφ : LipschitzWith 1 φ) (hφ0 : φ 0 = 0) (f : Lp ℝ 2 μ)
    (hf : (fun x => φ (f x)) =ᵐ[μ] f) :
    SobolevSpace.compContraction μ hQ hφ hφ0 (SobolevSpace.resolventAt μ hQ t ht f) =
      SobolevSpace.resolventAt μ hQ t ht f := by
  let r := SobolevSpace.resolventAt μ hQ t ht f
  let v := SobolevSpace.compContraction μ hQ hφ hφ0 r
  have hfFixed : hφ.compLp hφ0 f = f :=
    Lp.ext ((hφ.coeFn_compLp hφ0 f).trans hf)
  have hn : ‖SobolevSpace.toLp μ hQ v - f‖ ≤ ‖SobolevSpace.toLp μ hQ r - f‖ := by
    change ‖hφ.compLp hφ0 (SobolevSpace.toLp μ hQ r) - f‖ ≤ _
    simpa only [hfFixed, NNReal.coe_one, one_mul] using
      hφ.norm_compLp_sub_le hφ0 (SobolevSpace.toLp μ hQ r) f
  have he := SobolevSpace.energy_compContraction_le μ hQ hφ hφ0 r
  have hv := SobolevSpace.resolventAt_variational_identity μ hQ t ht f v
  change _ = _ + _ + SobolevSpace.resolventForm μ hQ t (v-r) (v-r) at hv
  rw [SobolevSpace.resolventForm_self, map_sub] at hv
  have hs : ‖SobolevSpace.toLp μ hQ v - f‖ ^ 2 ≤
      ‖SobolevSpace.toLp μ hQ r - f‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn
  have he' : SobolevSpace.energy μ hQ v ≤ SobolevSpace.energy μ hQ r := he
  have hz : ‖SobolevSpace.toLp μ hQ v - SobolevSpace.toLp μ hQ r‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖SobolevSpace.toLp μ hQ v-SobolevSpace.toLp μ hQ r‖,
      mul_nonneg ht.le (SobolevSpace.energy_nonneg μ hQ (v-r))]
  apply Subtype.ext
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

 theorem resolventLp_nonneg (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) (hf : 0 ≤ f) :
    0 ≤ resolventLp μ hQ t ht f := by
  have hφ := Lp.lipschitzWith_pos_part
  have hφ0 : max (0 : ℝ) 0 = 0 := max_self _
  have hfix : (fun x => max (f x) 0) =ᵐ[μ] f :=
    (Lp.coeFn_nonneg f).mpr hf |>.mono fun _ hx => max_eq_left hx
  have heq := congrArg (SobolevSpace.toLp μ hQ)
    (SobolevSpace.resolventAt_contraction_fixed μ hQ t ht hφ hφ0 f hfix)
  rw [SobolevSpace.compContraction_toLp] at heq
  have hae := hφ.coeFn_compLp hφ0 (resolventLp μ hQ t ht f)
  change hφ.compLp hφ0 (resolventLp μ hQ t ht f) = resolventLp μ hQ t ht f at heq
  rw [heq] at hae
  apply (Lp.coeFn_nonneg _).mp
  exact hae.mono fun _ hx => by rw [hx]; exact le_max_right _ _

 theorem resolventLp_le_const (t : ℝ) (ht : 0 < t) {c : ℝ} (hc : 0 ≤ c)
    (f : Lp ℝ 2 μ) (hf : ∀ᵐ x ∂μ, f x ≤ c) :
    ∀ᵐ x ∂μ, resolventLp μ hQ t ht f x ≤ c := by
  have hφ : LipschitzWith 1 (fun x : ℝ => min x c) := LipschitzWith.id.min_const c
  have hφ0 : min (0 : ℝ) c = 0 := min_eq_left hc
  have hfix : (fun x => min (f x) c) =ᵐ[μ] f := hf.mono fun _ hx => min_eq_left hx
  have heq := congrArg (SobolevSpace.toLp μ hQ)
    (SobolevSpace.resolventAt_contraction_fixed μ hQ t ht hφ hφ0 f hfix)
  rw [SobolevSpace.compContraction_toLp] at heq
  have hae := hφ.coeFn_compLp hφ0 (resolventLp μ hQ t ht f)
  change hφ.compLp hφ0 (resolventLp μ hQ t ht f) = resolventLp μ hQ t ht f at heq
  rw [heq] at hae
  exact hae.mono fun _ hx => by rw [hx]; exact min_le_right _ _

 theorem yosida_selfAdjoint (t : ℝ) (ht : 0 < t) : IsSelfAdjoint (yosida μ hQ t ht) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro left right
  change inner ℝ (yosida μ hQ t ht left) right = inner ℝ left (yosida μ hQ t ht right)
  simp only [yosida, smul_apply, sub_apply, one_apply_eq_self, real_inner_smul_left,
    real_inner_smul_right, inner_sub_left, inner_sub_right, resolventLp_inner]

 theorem heatApprox_selfAdjoint (t : ℝ) (i : ℕ) : IsSelfAdjoint (heatApprox μ hQ t i) :=
  ((IsSelfAdjoint.all t).smul (yosida_selfAdjoint μ hQ _ _).neg).exp

variable [ProperSpace X] [BorelSpace X] [μ.Regular]

 theorem heatFlow_inner (t : ℝ) (ht : 0 ≤ t) (f g : Lp ℝ 2 μ) :
    inner ℝ (heatFlow μ hQ t ht f) g = inner ℝ f (heatFlow μ hQ t ht g) := by
  have hi (i : ℕ) : inner ℝ (heatApprox μ hQ t i f) g = inner ℝ f (heatApprox μ hQ t i g) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (heatApprox_selfAdjoint μ hQ t i) f g
  exact tendsto_nhds_unique ((heatApprox_tendsto μ hQ t ht f).inner tendsto_const_nhds)
    ((tendsto_const_nhds.inner (heatApprox_tendsto μ hQ t ht g)).congr' (Eventually.of_forall fun i => (hi i).symm))

 theorem heatFlow_selfAdjoint (t : ℝ) (ht : 0 ≤ t) : IsSelfAdjoint (heatFlow μ hQ t ht) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  exact heatFlow_inner μ hQ t ht

end ParameterizedMarkov

variable {H : Type*} [AddCommGroup H] [Module ℝ H]

 theorem convex_sum_mem_of_le_one {K : Set H} (hK : Convex ℝ K) (h0 : (0 : H) ∈ K)
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (z : ι → H)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i ≤ 1) (hz : ∀ i ∈ s, z i ∈ K) :
    (∑ i ∈ s, w i • z i) ∈ K := by
  by_cases hsum : ∑ i ∈ s, w i = 0
  · have hi := (Finset.sum_eq_zero_iff_of_nonneg hw).mp hsum
    have hzsum : ∑ i ∈ s, w i • z i = 0 :=
      Finset.sum_eq_zero fun i hi' => by rw [hi i hi', zero_smul]
    rw [hzsum]
    exact h0
  · have hp : 0 < ∑ i ∈ s, w i := lt_of_le_of_ne (Finset.sum_nonneg hw) (Ne.symm hsum)
    have hc := hK.centerMass_mem hw hp hz
    have hm := hK.smul_mem_of_zero_mem h0 hc ⟨hp.le, hs⟩
    simpa only [Finset.centerMass, smul_smul, mul_inv_cancel₀ hsum, one_smul] using hm

end RegularPointCoordinates

end OAI
