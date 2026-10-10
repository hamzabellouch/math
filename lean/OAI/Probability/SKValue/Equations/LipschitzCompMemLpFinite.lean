import Mathlib
import OAI.Probability.SKValue.Processes.EulerMemLp
import OAI.Probability.SKValue.Evolution.MonotoneWeightedGridBound

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

lemma lipschitz_comp_memLp_finite {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {q : ℝ → ℝ} {C : ℝ≥0} (hq : LipschitzWith C q)
    {Y : Ω → ℝ} (hY : MemLp Y 2 μ) : MemLp (fun ω ↦ q (Y ω)) 2 μ := by
  have hl : LipschitzWith C (fun x ↦ q x-q 0) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa only [dist_sub_right] using hq.dist_le_mul x y
  have hh := hl.comp_memLp (by simp) hY
  convert hh.add (memLp_const (q 0)) using 1
  funext ω
  simp

lemma coupled_euler_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ} (hT : 0<T)
    (h : GradientStrip T γ u K L) {N : ℕ} (hN : 0<N) {j : ℕ} (hj : j≤N) :
    MemLp (coupledEuler T γ u B N j) 2 μ := by
  have hlaw := coupledCoordinates_hasLaw hB hT hN
  have hm := euler_memLp T N γ u
    (fun k hk ↦ (h.smooth _ (mesh_time_mem hT.le hN hk.le)).continuous.measurable)
    (fun k hk x ↦ h.bounded _ (mesh_time_mem hT.le hN hk.le) x) j hj
  have hh := (hlaw.map_eq.symm ▸ hm).comp_of_map hlaw.aemeasurable
  change MemLp (fun ω ↦ if N=0 then 0 else euler T N γ u (coupledCoordinates T N B ω) j) 2 μ
  simpa only [Function.comp_def, ite_eq_right (Nat.ne_of_gt hN)] using hh

lemma coupled_lipschitz_expectation_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {X : ℝ → Ω → ℝ} {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : GradientStrip T γ u K L)
    (hXM : ∀ t∈Icc (0 : ℝ) T, MemLp (X t) 2 μ)
    (hpaths : ∀ᵐ ω ∂μ,
      (∀ t∈Icc (0 : ℝ) T, X t ω=B (Real.toNNReal t) ω+
        ∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) ∧ X 0 ω=0)
    {N : ℕ} (hN : 0<N) {j : ℕ} (hj : j≤N) {q : ℝ → ℝ} {C : ℝ≥0}
    (hq : LipschitzWith C q) :
    |(∫ z, q (euler T N γ u z j) ∂gaussianProduct (Fin (N+1)))-
      ∫ ω, q (X (meshTime T N j) ω) ∂μ| ≤
      (C : ℝ)*Real.sqrt (∫ ω, (meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ) := by
  let E := meshMaxError T X (coupledEuler T γ u B) N
  have ht := mesh_time_mem hT.le hN hj
  have hFM := lipschitz_comp_memLp_finite hq (coupled_euler_memLp hB hT h hN hj)
  have hGM := lipschitz_comp_memLp_finite hq (hXM _ ht)
  have hEM := coupled_mesh_error_memLp hB hT h (fun t ht ↦ (hXM t ht).aestronglyMeasurable) hpaths hN
  have hFG (ω : Ω) : |q (coupledEuler T γ u B N j ω)-q (X (meshTime T N j) ω)|≤(C : ℝ)*|E ω| := by
    have he : |coupledEuler T γ u B N j ω-X (meshTime T N j) ω|≤E ω :=
      le_initialMax (f := fun k ↦ |coupledEuler T γ u B N k ω-X (meshTime T N k) ω|) hj
    have hl : |q (coupledEuler T γ u B N j ω)-q (X (meshTime T N j) ω)|≤
        (C : ℝ)*|coupledEuler T γ u B N j ω-X (meshTime T N j) ω| := by
      simpa only [Real.dist_eq] using
        hq.dist_le_mul (coupledEuler T γ u B N j ω) (X (meshTime T N j) ω)
    exact hl.trans (mul_le_mul_of_nonneg_left (he.trans (le_abs_self _)) C.coe_nonneg)
  have hlaw := coupledCoordinates_hasLaw hB hT hN
  have hm := measurable_euler T N γ u (fun k hk ↦
    (h.smooth _ (mesh_time_mem hT.le hN hk.le)).continuous.measurable) j hj
  have heq : (∫ z, q (euler T N γ u z j) ∂gaussianProduct (Fin (N+1)))=
      ∫ ω, q (coupledEuler T γ u B N j ω) ∂μ := by
    have he := hlaw.integral_comp (hq.continuous.measurable.comp hm).aestronglyMeasurable
    simpa only [Function.comp_apply, coupledEuler, ite_eq_right (Nat.ne_of_gt hN)] using he.symm
  rw [heq]
  exact first_moment_perturbation hFM hGM hEM C.coe_nonneg (Eventually.of_forall hFG)

lemma perturbed_monotone_weighted_grid_tendsto {γ f : ℝ → ℝ} {T K : ℝ}
    {a : (N : ℕ) → Fin N → ℝ} {r : ℕ → ℝ}
    (hT : 0<T) (hK : 0≤K) (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) (hγ0 : 0≤γ 0)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) (hfB : ∀ s∈Icc (0 : ℝ) T, |f s|≤K)
    (hr : Tendsto r atTop (𝓝 0))
    (ha : ∀ᶠ N in atTop, ∀ j : Fin N, |a N j-f (meshTime T N j)|≤r N) :
    Tendsto (fun N ↦ stepSize T N * ∑ j : Fin N, γ (meshTime T N j)*a N j) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, γ t*f t)) := by
  have hG : 0≤γ T := hγ0.trans (hγ ⟨le_rfl,hT.le⟩ ⟨hT.le,le_rfl⟩ hT.le)
  have hR := monotone_weighted_grid_tendsto hT hK hγ hγ0 hf hfB
  have herr : Tendsto (fun N ↦ stepSize T N * (∑ j : Fin N, γ (meshTime T N j)*a N j)-
      stepSize T N * (∑ j : Fin N, γ (meshTime T N j)*f (meshTime T N j))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun N ↦ T*γ T*r N)
    · filter_upwards [ha, eventually_gt_atTop 0] with N hNa hN
      have hδ : 0 ≤ stepSize T N := div_nonneg hT.le (Nat.cast_nonneg N)
      have hconstant : stepSize T N * ∑ _ : Fin N, γ T*r N=T*γ T*r N := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, stepSize]
        field_simp
      rw [Real.norm_eq_abs, ←mul_sub, abs_mul, abs_of_nonneg hδ, ←Finset.sum_sub_distrib]
      calc
        _ ≤ stepSize T N * ∑ j : Fin N, |γ (meshTime T N j)*a N j-γ (meshTime T N j)*f (meshTime T N j)| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hδ
        _ ≤ stepSize T N * ∑ _ : Fin N, γ T*r N := by
          apply mul_le_mul_of_nonneg_left _ hδ
          apply Finset.sum_le_sum
          intro j _
          have ht := mesh_time_mem hT.le hN j.isLt.le
          have hg0 : 0≤γ (meshTime T N j) := hγ0.trans (hγ ⟨le_rfl,hT.le⟩ ht ht.1)
          have hgT := hγ ht ⟨hT.le,le_rfl⟩ ht.2
          rw [←mul_sub, abs_mul, abs_of_nonneg hg0]
          exact (mul_le_mul_of_nonneg_right hgT (abs_nonneg _)).trans
            (mul_le_mul_of_nonneg_left (hNa j) hG)
        _ = _ := hconstant
    · simpa only [mul_zero] using hr.const_mul (T*γ T)
  have hR' : Tendsto (fun N ↦ stepSize T N * ∑ j : Fin N, γ (meshTime T N j)*f (meshTime T N j))
      atTop (𝓝 (∫ t in (0 : ℝ)..T, γ t*f t)) := by
    convert hR using 1
    funext N
    dsimp only [stepSize, meshTime]
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ γ ((j : ℝ)*(T/N))*f ((j : ℝ)*(T/N))) ]
  simpa only [sub_add_cancel, zero_add] using herr.add hR'

end SKValue

namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

lemma ValueStrip.product_lipschitzWith {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : ValueStrip T γ V K L) {t : ℝ} (ht : t∈Icc (0 : ℝ) T) :
    LipschitzWith (Real.toNNReal L) (fun x ↦ (1/2 : ℝ)*(deriv (V t) x)^2) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [Real.coe_toNNReal _ h.L_nonneg, Real.dist_eq, Real.dist_eq]
  simpa only [sub_self, abs_zero, zero_add] using h.product_lipschitz t ht t ht y x

lemma valueMeshEnergy_expectation {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : ValueStrip T γ V K L) {N : ℕ} (hN : 0<N) :
    (∫ z, valueMeshEnergy T N γ V N z ∂gaussianProduct (Fin (N+1)))=
      stepSize T N * ∑ j : Fin N, γ (meshTime T N j)*
        (∫ z, (1/2 : ℝ)*(deriv (V (meshTime T N j))
          (euler T N γ (fun t ↦ deriv (V t)) z j))^2 ∂gaussianProduct (Fin (N+1))) := by
  have hm (j : ℕ) (hj : j<N) : MemLp
      (fun z ↦ (1/2 : ℝ)*(deriv (V (meshTime T N j))
        (euler T N γ (fun t ↦ deriv (V t)) z j))^2) 2 (gaussianProduct (Fin (N+1))) := by
    apply MemLp.of_bound
      ((h.product_lipschitzWith (mesh_time_mem hT.le hN hj.le)).continuous.measurable.comp
        (measurable_euler T N γ (fun t ↦ deriv (V t)) (fun i hi ↦
          ((h.smooth _ (mesh_time_mem hT.le hN hi.le)).continuous_deriv (by norm_num)).measurable)
            j hj.le)).aestronglyMeasurable K
    exact Eventually.of_forall (fun z ↦ by
      simpa only [Real.norm_eq_abs, Function.comp_apply] using h.product_bound _ (mesh_time_mem hT.le hN hj.le) _)
  have heq (z : Fin (N+1) → ℝ) : valueMeshEnergy T N γ V N z =
      ∑ j ∈ Finset.range N, stepSize T N*γ (meshTime T N j)*
        ((1/2 : ℝ)*(deriv (V (meshTime T N j))
          (euler T N γ (fun t ↦ deriv (V t)) z j))^2) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [heq]
  rw [integral_finsetSum _ (fun j hj ↦ ((hm j (Finset.mem_range.mp hj)).integrable (by norm_num)).const_mul _)]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ γ (meshTime T N j)*
    ∫ z, (1/2 : ℝ)*(deriv (V (meshTime T N j))
      (euler T N γ (fun t ↦ deriv (V t)) z j))^2 ∂gaussianProduct (Fin (N+1)))]
  simp_rw [integral_const_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem diffusion_value_expectation
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {X : ℝ → Ω → ℝ} {T K L Kg Lg Lu : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : ValueStrip T γ V K L)
    (hg : GradientStrip T γ (fun t ↦ deriv (V t)) Kg Lg) (hLu : 0≤Lu)
    (huLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |deriv (V s) x-deriv (V t) y|≤Lu*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T, MemLp (X t) 2 μ)
    (hpaths : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*deriv (V s) (X s ω)) volume 0 T ∧
      (∀ t∈Icc (0 : ℝ) T, X t ω = B (Real.toNNReal t) ω+
        ∫ s in (0 : ℝ)..t, γ s*deriv (V s) (X s ω)) ∧ X 0 ω=0) :
    (∫ ω, V T (X T ω) ∂μ) = V 0 0+
      (1/2 : ℝ)*(∫ t in (0 : ℝ)..T, γ t*(∫ ω, (deriv (V t) (X t ω))^2 ∂μ)) := by
  let u := fun t ↦ deriv (V t)
  let E (N : ℕ) := ∫ ω, (meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ
  let f (t : ℝ) := ∫ ω, (1/2 : ℝ)*(deriv (V t) (X t ω))^2 ∂μ
  have hXa (t : ℝ) (ht : t∈Icc (0 : ℝ) T) := (hXM t ht).aestronglyMeasurable
  have hE : Tendsto E atTop (𝓝 0) := coupled_euler_L2_convergence hB hT hg hLu huLip hXa hpaths
  have hEs : Tendsto (fun N ↦ Real.sqrt (E N)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hE
  have ht : T∈Icc (0 : ℝ) T := ⟨hT.le,le_rfl⟩
  have hvalue : Tendsto (fun N ↦ ∫ z, V T (euler T N γ u z N) ∂gaussianProduct (Fin (N+1)))
      atTop (𝓝 (∫ ω, V T (X T ω) ∂μ)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _)) ?_ hEs
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hh := coupled_lipschitz_expectation_bound hB hT hg hXM
      (hpaths.mono (fun _ hω ↦ hω.2.2)) hN (le_refl N) (h.value_lipschitz ht)
    have hn : (N : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hN
    have hlast : meshTime T N N=T := by dsimp only [meshTime, stepSize]; field_simp
    simpa only [Real.norm_eq_abs, hlast, NNReal.coe_one, one_mul] using hh
  have hf : ContinuousOn f (Icc (0 : ℝ) T) := by
    have hc := (mean_derivative_square_continuous (by norm_num : (0 : ℝ)≤1) hLu
      (fun t ht ↦ (h.smooth t ht).continuous_deriv (by norm_num)) h.bounded huLip hXa
      (hpaths.mono (fun _ hω ↦ hω.1))).const_mul (1/2 : ℝ)
    simpa only [f, integral_const_mul] using hc
  have hfB (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : |f t|≤K := by
    simpa only [f, Real.norm_eq_abs, probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := μ) (C := K)
        (f := fun ω ↦ (1/2 : ℝ)*(deriv (V t) (X t ω))^2)
        (Eventually.of_forall (fun ω ↦ by
          simpa only [Real.norm_eq_abs] using h.product_bound t ht (X t ω))))
  have henergy : Tendsto (fun N ↦ ∫ z, valueMeshEnergy T N γ V N z ∂gaussianProduct (Fin (N+1)))
      atTop (𝓝 (∫ t in (0 : ℝ)..T, γ t*f t)) := by
    have hq : Tendsto (fun N ↦ stepSize T N * ∑ j : Fin N, γ (meshTime T N j)*
        (∫ z, (1/2 : ℝ)*(deriv (V (meshTime T N j))) (euler T N γ u z j)^2
          ∂gaussianProduct (Fin (N+1)))) atTop (𝓝 (∫ t in (0 : ℝ)..T, γ t*f t)) := by
      apply perturbed_monotone_weighted_grid_tendsto (r := fun N ↦ L*Real.sqrt (E N)) hT h.K_nonneg
        h.gamma_mono (h.gamma_nonneg 0 ⟨le_rfl,hT.le⟩) hf hfB
        (by simpa only [mul_zero] using hEs.const_mul L)
      filter_upwards [eventually_gt_atTop 0] with N hN j
      have hh := coupled_lipschitz_expectation_bound hB hT hg hXM
        (hpaths.mono (fun _ hω ↦ hω.2.2)) hN j.isLt.le
          (h.product_lipschitzWith (mesh_time_mem hT.le hN j.isLt.le))
      simpa only [Real.coe_toNNReal _ h.L_nonneg] using hh
    apply hq.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (valueMeshEnergy_expectation hT h hN).symm
  have hlim := (hvalue.sub_const (V 0 0)).sub henergy
  have hzero := value_mesh_expectation_error_tendsto hT hT1 h
  have he : (∫ ω, V T (X T ω) ∂μ)-V 0 0-(∫ t in (0 : ℝ)..T, γ t*f t)=0 :=
    tendsto_nhds_unique hlim hzero
  have hfeq : (∫ t in (0 : ℝ)..T, γ t*f t)=
      (1/2 : ℝ)*(∫ t in (0 : ℝ)..T, γ t*(∫ ω, (deriv (V t) (X t ω))^2 ∂μ)) := by
    dsimp only [f]
    simp_rw [integral_const_mul]
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [hfeq] at he
  linarith

end SKValue

end

end OAI
