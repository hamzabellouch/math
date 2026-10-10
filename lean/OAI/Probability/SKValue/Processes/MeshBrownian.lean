import Mathlib
import OAI.Probability.SKValue.Evolution.MeanDerivativeContinuous
import OAI.Probability.SKValue.Equations.RawIncrement

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

lemma coupled_terminal_second_moment_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {X : ℝ → Ω → ℝ} {T K L Lu : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : GradientStrip T γ u K L) (hLu : 0≤Lu)
    (huLip : ∀ x y, |u T x-u T y|≤Lu*|x-y|)
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hpaths : ∀ᵐ ω ∂μ,
      (∀ t∈Icc (0 : ℝ) T, X t ω=B (Real.toNNReal t) ω+
        ∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) ∧ X 0 ω=0)
    {N : ℕ} (hN : 0<N) :
    |(∫ z, (meshTerminal T N γ u z)^2 ∂gaussianProduct (Fin (N+1)))-
      (∫ ω, (u T (X T ω))^2 ∂μ)| ≤
      (2*Lu)*Real.sqrt (∫ ω, (meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ) := by
  let F (ω : Ω) := u T (coupledEuler T γ u B N N ω)
  let G (ω : Ω) := u T (X T ω)
  let E := meshMaxError T X (coupledEuler T γ u B) N
  have ht : T∈Icc (0 : ℝ) T := ⟨hT.le,le_rfl⟩
  have hd := (h.smooth T ht).continuous
  have hFM : MemLp F 2 μ := MemLp.of_bound
    (hd.measurable.comp_aemeasurable (coupled_euler_measurable hB hT h N N le_rfl).aemeasurable).aestronglyMeasurable 1
      (Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs, F] using h.bounded T ht _))
  have hGM : MemLp G 2 μ := MemLp.of_bound
    (hd.measurable.comp_aemeasurable (hXM T ht).aemeasurable).aestronglyMeasurable 1
      (Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs, G] using h.bounded T ht _))
  have hEM : MemLp E 2 μ := coupled_mesh_error_memLp hB hT h hXM hpaths hN
  have hlast : meshTime T N N = T := by dsimp [meshTime, stepSize]; field_simp
  have hFG (ω : Ω) : |F ω-G ω|≤Lu*|E ω| := by
    have he : |coupledEuler T γ u B N N ω-X T ω|≤E ω := by
      change |coupledEuler T γ u B N N ω-X T ω| ≤ initialMax _ N
      have hm := le_initialMax (f := fun k ↦ |coupledEuler T γ u B N k ω-X (meshTime T N k) ω|) (le_refl N)
      change |coupledEuler T γ u B N N ω-X (meshTime T N N) ω| ≤ initialMax _ N at hm
      rw [hlast] at hm
      exact hm

    exact (huLip _ _).trans (mul_le_mul_of_nonneg_left (he.trans (le_abs_self _)) hLu)
  have hlaw := coupledCoordinates_hasLaw hB hT hN
  have heq : (∫ z, (meshTerminal T N γ u z)^2 ∂gaussianProduct (Fin (N+1)))=∫ ω, (F ω)^2 ∂μ := by
    rw [←hlaw.integral_comp ((mesh_terminal_measurable hT.le h hN).pow_const 2).aestronglyMeasurable]
    simp only [Function.comp_apply, F, meshTerminal, coupledEuler, ite_eq_right (Nat.ne_of_gt hN)]
  rw [heq]
  simpa only [mul_one] using second_moment_perturbation hFM hGM hEM (by norm_num : (0 : ℝ)≤1) hLu
    (Eventually.of_forall (fun ω ↦ ⟨h.bounded T ht _, h.bounded T ht _, hFG ω⟩))

theorem diffusion_gradient_isometry
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {X : ℝ → Ω → ℝ} {T K L D Lu La : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : GradientStrip T γ u K L)
    (hD0 : 0≤D) (hLu : 0≤Lu) (hLa : 0≤La)
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    (huLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y|≤Lu*(|s-t|+|x-y|))
    (haLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |deriv (u s) x-deriv (u t) y|≤La*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hpaths : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      (∀ t∈Icc (0 : ℝ) T, X t ω = B (Real.toNNReal t) ω+
        ∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) ∧ X 0 ω=0) :
    (∫ ω, (u T (X T ω))^2 ∂μ) =
      ∫ t in (0 : ℝ)..T, ∫ ω, (deriv (u t) (X t ω))^2 ∂μ := by
  let E (N : ℕ) := ∫ ω, (meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ
  have hE : Tendsto E atTop (𝓝 0) := coupled_euler_L2_convergence hB hT h hLu huLip hXM hpaths
  have hEs : Tendsto (fun N ↦ Real.sqrt (E N)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hE
  have ht : T∈Icc (0 : ℝ) T := ⟨hT.le,le_rfl⟩
  have hmoment : Tendsto (fun N ↦ ∫ z, (meshTerminal T N γ u z)^2 ∂gaussianProduct (Fin (N+1)))
      atTop (𝓝 (∫ ω, (u T (X T ω))^2 ∂μ)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _)) ?_
      (by simpa only [mul_zero] using hEs.const_mul (2*Lu))
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [Real.norm_eq_abs]
    exact coupled_terminal_second_moment_bound hB hT h hLu
      (fun x y ↦ by simpa only [sub_self, abs_zero, zero_add] using huLip T ht T ht x y)
      hXM (hpaths.mono (fun _ hω ↦ hω.2.2)) hN
  have hmean := mean_derivative_square_continuous hD0 hLa
    (fun t ht ↦ (h.smooth t ht).continuous_deriv (by norm_num)) hD haLip hXM
    (hpaths.mono (fun _ hω ↦ hω.1))
  have hquadrature : Tendsto (fun N ↦ stepSize T N * ∑ i : Fin N,
      ∫ z, (meshRaw T N γ u i z)^2 ∂gaussianProduct (Fin (N+1))) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, ∫ ω, (deriv (u t) (X t ω))^2 ∂μ)) := by
    apply perturbed_grid_riemann_tendsto (r := fun N ↦ (2*D*La)*Real.sqrt (E N)) hT hmean
      (by simpa only [mul_zero] using hEs.const_mul (2*D*La))
    filter_upwards [eventually_gt_atTop 0] with N hN i
    exact (coupled_mesh_general_moment_bounds hB hT h hD0 hLa hD
      (fun t ht x y ↦ by simpa only [sub_self, abs_zero, zero_add] using haLip t ht t ht x y)
      hXM (hpaths.mono (fun _ hω ↦ hω.2.2)) hN i).1
  have herror : Tendsto (fun N ↦
      (∫ z, (meshTerminal T N γ u z)^2 ∂gaussianProduct (Fin (N+1)))-
      stepSize T N * ∑ i : Fin N, ∫ z, (meshRaw T N γ u i z)^2 ∂gaussianProduct (Fin (N+1)))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun N ↦
      Real.sqrt (gradientMeshError T N γ u) * Real.sqrt (2*(1+T*D^2)))
    · filter_upwards [eventually_gt_atTop 0] with N hN
      rw [Real.norm_eq_abs]
      exact mesh_terminal_stochastic_second_moment_error hT h hD0 hD hN
    · simpa only [Real.sqrt_zero, zero_mul, Function.comp_def] using
        ((Real.continuous_sqrt.tendsto 0).comp (gradientMeshError_tendsto_zero hT hT1 h)).mul_const
          (Real.sqrt (2*(1+T*D^2)))
  have hlimit := herror.add hquadrature
  simp only [sub_add_cancel, zero_add] at hlimit
  exact tendsto_nhds_unique hmoment hlimit

lemma weighted_first_moment_perturbation {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g e b : Ω → ℝ} {L : ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (he : MemLp e 2 μ) (hb : MemLp b 2 μ) (hL : 0≤L)
    (hfg : ∀ᵐ ω ∂μ, |f ω-g ω|≤L*|e ω|) :
    |(∫ ω, f ω*b ω ∂μ)-(∫ ω, g ω*b ω ∂μ)| ≤
      L*Real.sqrt (∫ ω, (e ω)^2 ∂μ)*Real.sqrt (∫ ω, (b ω)^2 ∂μ) := by
  rw [←integral_sub (f := fun ω ↦ f ω*b ω) (g := fun ω ↦ g ω*b ω) (hf.integrable_mul hb) (hg.integrable_mul hb)]
  have heq : (fun ω ↦ f ω*b ω-g ω*b ω)=(fun ω ↦ (f ω-g ω)*b ω) := by funext ω; ring
  rw [heq]
  calc
    _ ≤ ∫ ω, |(f ω-g ω)*b ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, L*(|e ω| * |b ω|) ∂μ := by
      apply integral_mono_ae ((hf.sub hg).integrable_mul hb).abs ((he.abs.integrable_mul hb.abs).const_mul L)
      filter_upwards [hfg] with ω hω
      change |(f ω-g ω)*b ω| ≤ L*(|e ω| * |b ω|)
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hω (abs_nonneg _)).trans_eq (mul_assoc _ _ _)
    _ = L*(∫ ω, |e ω| * |b ω| ∂μ) := integral_const_mul _ _
    _ ≤ L*(Real.sqrt (∫ ω, (e ω)^2 ∂μ)*Real.sqrt (∫ ω, (b ω)^2 ∂μ)) := by
      have hcs := integral_product_CS he.abs hb.abs
      change |∫ ω, |e ω| * |b ω| ∂μ|≤Real.sqrt (∫ ω, |e ω|^2 ∂μ)*Real.sqrt (∫ ω, |b ω|^2 ∂μ) at hcs
      simp only [sq_abs] at hcs
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans hcs) hL
    _ = _ := by ring

lemma brownian_eval_second_moment {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (t : ℝ≥0) :
    (∫ ω, (B t ω)^2 ∂μ)=(t : ℝ) := by
  have hv := (hB.hasLaw_eval t).variance_eq
  rw [variance_eq_integral (hB.aemeasurable t), hB.integral_eval t] at hv
  simpa using hv

noncomputable def meshBrownian (T : ℝ) (N : ℕ) (z : Fin (N+1) → ℝ) : ℝ :=
  ∑ j : Fin N, Real.sqrt (stepSize T N)*coordinate N j z

lemma meshBrownian_measurable (T : ℝ) (N : ℕ) : Measurable (meshBrownian T N) := by
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.mul (measurable_coordinate N i)

lemma meshBrownian_memLp (T : ℝ) (N : ℕ) :
    MemLp (meshBrownian T N) 2 (gaussianProduct (Fin (N+1))) := by
  convert memLp_finsetSum' Finset.univ (fun i : Fin N ↦ fun _ ↦
    (gaussian_memLp (coordinate_hasLaw N i) 2 (by norm_num)).const_mul (Real.sqrt (stepSize T N))) using 1
  funext z
  simp only [meshBrownian, Finset.sum_apply]

lemma coupled_meshBrownian {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) {T : ℝ} (hT : 0<T)
    {N : ℕ} (hN : 0<N) (ω : Ω) :
    meshBrownian T N (coupledCoordinates T N B ω)=B (Real.toNNReal T) ω-B 0 ω := by
  have hlast : (N : ℝ)*(T/N)=T := by field_simp
  unfold meshBrownian
  have heq (j : Fin N) := coupled_coordinate_exact B hT hN (show (j : ℕ)<N+1 by omega) ω
  simp_rw [stepSize, heq]
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ B (Real.toNNReal (((j+1 : ℕ) : ℝ)*(T/N))) ω-
    B (Real.toNNReal ((j : ℝ)*(T/N))) ω), Finset.sum_range_sub (fun j : ℕ ↦ B (Real.toNNReal ((j : ℝ)*(T/N))) ω) N]
  simp only [Nat.cast_zero, zero_mul, Real.toNNReal_zero, hlast]

lemma meshBrownian_second_moment {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) {T : ℝ} (hT : 0<T)
    {N : ℕ} (hN : 0<N) :
    (∫ z, (meshBrownian T N z)^2 ∂gaussianProduct (Fin (N+1)))=T := by
  rw [←(coupledCoordinates_hasLaw hB hT hN).integral_comp
    ((meshBrownian_measurable T N).pow_const 2).aestronglyMeasurable]
  have heq : (fun ω ↦ (meshBrownian T N (coupledCoordinates T N B ω))^2)=ᵐ[μ]
      (fun ω ↦ (B (Real.toNNReal T) ω)^2) := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
    simp only [coupled_meshBrownian B hT hN ω, hω, sub_zero]
  exact (integral_congr_ae heq).trans ((brownian_eval_second_moment hB _).trans
    (Real.coe_toNNReal _ hT.le))

lemma mesh_terminal_brownian_error {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {T K L D : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : GradientStrip T γ u K L)
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D) {N : ℕ} (hN : 0<N) :
    |(∫ z, meshTerminal T N γ u z * meshBrownian T N z ∂gaussianProduct (Fin (N+1)))-
      stepSize T N * ∑ i : Fin N, ∫ z, meshRaw T N γ u i z ∂gaussianProduct (Fin (N+1))| ≤
    Real.sqrt (gradientMeshError T N γ u)*Real.sqrt T := by
  have hm (i : Fin N) := mesh_raw_measurable hT.le h hN i.isLt.le
  have hp (i : Fin N) := mesh_raw_depends T i.isLt.le γ u
  have hH (i : Fin N) := mesh_raw_memLp hT.le h hD hN i.isLt.le
  have hu := mesh_terminal_memLp hT.le h hN
  have hr := finiteRaw_memLp (δ := stepSize T N) hm hp hH
  have hb := meshBrownian_memLp T N
  rw [←finiteRaw_brownian_covariance (δ := stepSize T N) (div_nonneg hT.le (Nat.cast_nonneg N)) hm hp hH]
  change |(∫ z, meshTerminal T N γ u z * meshBrownian T N z ∂gaussianProduct (Fin (N+1)))-
      (∫ z, finiteRawMartingale (stepSize T N) (fun i : Fin N ↦ meshRaw T N γ u i) z * meshBrownian T N z ∂gaussianProduct (Fin (N+1)))|≤_
  rw [←integral_sub (f := fun z ↦ meshTerminal T N γ u z * meshBrownian T N z)
    (g := fun z ↦ finiteRawMartingale (stepSize T N) (fun i : Fin N ↦ meshRaw T N γ u i) z * meshBrownian T N z)
    (hu.integrable_mul hb) (hr.integrable_mul hb)]
  simp_rw [←sub_mul]
  have hcs := integral_product_CS (hu.sub hr) hb
  rw [meshBrownian_second_moment hB hT hN] at hcs
  exact hcs

lemma coupled_terminal_brownian_error {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {X : ℝ → Ω → ℝ} {T K L Lu : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : GradientStrip T γ u K L) (hLu : 0≤Lu)
    (huLip : ∀ x y, |u T x-u T y|≤Lu*|x-y|)
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hpaths : ∀ᵐ ω ∂μ,
      (∀ t∈Icc (0 : ℝ) T, X t ω=B (Real.toNNReal t) ω+
        ∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) ∧ X 0 ω=0)
    {N : ℕ} (hN : 0<N) :
    |(∫ z, meshTerminal T N γ u z * meshBrownian T N z ∂gaussianProduct (Fin (N+1)))-
      (∫ ω, u T (X T ω)*B (Real.toNNReal T) ω ∂μ)| ≤
      Lu*Real.sqrt (∫ ω, (meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ)*Real.sqrt T := by
  let F (ω : Ω) := u T (coupledEuler T γ u B N N ω)
  let G (ω : Ω) := u T (X T ω)
  let E := meshMaxError T X (coupledEuler T γ u B) N
  have ht : T∈Icc (0 : ℝ) T := ⟨hT.le,le_rfl⟩
  have hd := (h.smooth T ht).continuous
  have hFM : MemLp F 2 μ := MemLp.of_bound
    (hd.measurable.comp_aemeasurable (coupled_euler_measurable hB hT h N N le_rfl).aemeasurable).aestronglyMeasurable 1
      (Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs, F] using h.bounded T ht _))
  have hGM : MemLp G 2 μ := MemLp.of_bound
    (hd.measurable.comp_aemeasurable (hXM T ht).aemeasurable).aestronglyMeasurable 1
      (Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs, G] using h.bounded T ht _))
  have hEM : MemLp E 2 μ := coupled_mesh_error_memLp hB hT h hXM hpaths hN
  have hlast : meshTime T N N = T := by dsimp [meshTime, stepSize]; field_simp
  have hFG (ω : Ω) : |F ω-G ω|≤Lu*|E ω| := by
    have he : |coupledEuler T γ u B N N ω-X T ω|≤E ω := by
      change |coupledEuler T γ u B N N ω-X T ω| ≤ initialMax _ N
      have hm := le_initialMax (f := fun k ↦ |coupledEuler T γ u B N k ω-X (meshTime T N k) ω|) (le_refl N)
      rw [hlast] at hm
      exact hm
    exact (huLip _ _).trans (mul_le_mul_of_nonneg_left (he.trans (le_abs_self _)) hLu)
  have hlaw := coupledCoordinates_hasLaw hB hT hN
  have heq : (∫ z, meshTerminal T N γ u z * meshBrownian T N z ∂gaussianProduct (Fin (N+1)))=
      ∫ ω, F ω*B (Real.toNNReal T) ω ∂μ := by
    have hm : AEStronglyMeasurable (fun z ↦ meshTerminal T N γ u z * meshBrownian T N z) (gaussianProduct (Fin (N+1))) :=
      ((mesh_terminal_measurable hT.le h hN).mul (meshBrownian_measurable T N)).aestronglyMeasurable
    rw [←hlaw.integral_comp hm]
    apply integral_congr_ae
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
    simp only [Function.comp_apply, F, meshTerminal, coupledEuler, ite_eq_right (Nat.ne_of_gt hN),
      coupled_meshBrownian B hT hN ω, hω, sub_zero]
  rw [heq]
  have hh := weighted_first_moment_perturbation hFM hGM hEM (hB.hasLaw_eval T.toNNReal).hasGaussianLaw.memLp_two hLu
    (Eventually.of_forall hFG)
  rw [brownian_eval_second_moment hB,Real.coe_toNNReal _ hT.le] at hh
  exact hh

theorem diffusion_gradient_brownian_covariance
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {X : ℝ → Ω → ℝ} {T K L D Lu La : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : GradientStrip T γ u K L)
    (hD0 : 0≤D) (hLu : 0≤Lu) (hLa : 0≤La)
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    (huLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y|≤Lu*(|s-t|+|x-y|))
    (haLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |deriv (u s) x-deriv (u t) y|≤La*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hpaths : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      (∀ t∈Icc (0 : ℝ) T, X t ω = B (Real.toNNReal t) ω+
        ∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) ∧ X 0 ω=0) :
    (∫ ω, u T (X T ω)*B (Real.toNNReal T) ω ∂μ) =
      ∫ t in (0 : ℝ)..T, ∫ ω, deriv (u t) (X t ω) ∂μ := by
  let E (N : ℕ) := ∫ ω, (meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ
  have hE : Tendsto E atTop (𝓝 0) := coupled_euler_L2_convergence hB hT h hLu huLip hXM hpaths
  have hEs : Tendsto (fun N ↦ Real.sqrt (E N)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hE
  have ht : T∈Icc (0 : ℝ) T := ⟨hT.le,le_rfl⟩
  have hcovariance : Tendsto (fun N ↦ ∫ z, meshTerminal T N γ u z * meshBrownian T N z
      ∂gaussianProduct (Fin (N+1))) atTop
      (𝓝 (∫ ω, u T (X T ω)*B T.toNNReal ω ∂μ)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _)) ?_
      (by simpa only [mul_zero, zero_mul] using (hEs.const_mul Lu).mul_const (Real.sqrt T))
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [Real.norm_eq_abs]
    exact coupled_terminal_brownian_error hB hT h hLu
      (fun x y ↦ by simpa only [sub_self, abs_zero, zero_add] using huLip T ht T ht x y)
      hXM (hpaths.mono (fun _ hω ↦ hω.2.2)) hN
  have hmean := mean_derivative_continuous hLa
    (fun t ht ↦ (h.smooth t ht).continuous_deriv (by norm_num)) hD haLip hXM
    (hpaths.mono (fun _ hω ↦ hω.1))
  have hquadrature : Tendsto (fun N ↦ stepSize T N * ∑ i : Fin N,
      ∫ z, meshRaw T N γ u i z ∂gaussianProduct (Fin (N+1))) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, ∫ ω, deriv (u t) (X t ω) ∂μ)) := by
    apply perturbed_grid_riemann_tendsto (r := fun N ↦ La*Real.sqrt (E N)) hT hmean
      (by simpa only [mul_zero] using hEs.const_mul La)
    filter_upwards [eventually_gt_atTop 0] with N hN i
    exact (coupled_mesh_general_moment_bounds hB hT h hD0 hLa hD
      (fun t ht x y ↦ by simpa only [sub_self, abs_zero, zero_add] using haLip t ht t ht x y)
      hXM (hpaths.mono (fun _ hω ↦ hω.2.2)) hN i).2
  have herror : Tendsto (fun N ↦
      (∫ z, meshTerminal T N γ u z * meshBrownian T N z ∂gaussianProduct (Fin (N+1)))-
      stepSize T N * ∑ i : Fin N, ∫ z, meshRaw T N γ u i z ∂gaussianProduct (Fin (N+1)))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun N ↦
      Real.sqrt (gradientMeshError T N γ u) * Real.sqrt T)
    · filter_upwards [eventually_gt_atTop 0] with N hN
      rw [Real.norm_eq_abs]
      exact mesh_terminal_brownian_error hB hT h hD hN
    · simpa only [Real.sqrt_zero, zero_mul, Function.comp_def] using
        ((Real.continuous_sqrt.tendsto 0).comp (gradientMeshError_tendsto_zero hT hT1 h)).mul_const
          (Real.sqrt T)
  have hlimit := herror.add hquadrature
  simp only [sub_add_cancel, zero_add] at hlimit
  exact tendsto_nhds_unique hcovariance hlimit

end SKValue

end

end OAI
