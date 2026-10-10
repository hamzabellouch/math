import Mathlib
import OAI.Probability.SKValue.Evolution.UniformGridRiemannBound
import OAI.Probability.SKValue.Equations.FirstMomentPerturbation

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

noncomputable def rawIncrement {N : ℕ} (H : (Fin (N+1) → ℝ) → ℝ) (j : ℕ) :
    (Fin (N+1) → ℝ) → ℝ := fun z ↦ H z * coordinate N j z

lemma rawIncrement_memLp {N j : ℕ} {H : (Fin (N+1) → ℝ) → ℝ}
    (hj : j<N+1) (hm : Measurable H) (hp : DependsBefore j H)
    (hH : MemLp H 2 (gaussianProduct (Fin (N+1)))) :
    MemLp (rawIncrement H j) 2 (gaussianProduct (Fin (N+1))) := by
  apply (memLp_two_iff_integrable_sq
    (hm.aestronglyMeasurable.mul (measurable_coordinate N j).aestronglyMeasurable)).2
  have hind := (hp.independent hj hm).comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have hi := hind.integrable_mul hH.integrable_sq
      (gaussian_memLp (coordinate_hasLaw N j) 2 (by norm_num)).integrable_sq
  change Integrable (fun z ↦ (H z)^2 * (coordinate N j z)^2) _ at hi
  simpa only [rawIncrement, Pi.mul_apply, mul_pow] using hi

lemma rawIncrement_mean {N j : ℕ} {H : (Fin (N+1) → ℝ) → ℝ}
    (hj : j<N+1) (hm : Measurable H) (hp : DependsBefore j H) :
    (∫ z, rawIncrement H j z ∂gaussianProduct (Fin (N+1))) = 0 := by
  have hi := (hp.independent hj hm).integral_mul_eq_mul_integral
    hm.aestronglyMeasurable (measurable_coordinate N j).aestronglyMeasurable
  change (∫ z, H z * coordinate N j z ∂gaussianProduct (Fin (N+1))) = _ at hi
  change (∫ z, H z * coordinate N j z ∂gaussianProduct (Fin (N+1))) = 0
  rw [hi, gaussian_mean (coordinate_hasLaw N j), mul_zero]

lemma rawIncrement_variance {N j : ℕ} {H : (Fin (N+1) → ℝ) → ℝ}
    (hj : j<N+1) (hm : Measurable H) (hp : DependsBefore j H) :
    (∫ z, (rawIncrement H j z)^2 ∂gaussianProduct (Fin (N+1))) =
      ∫ z, (H z)^2 ∂gaussianProduct (Fin (N+1)) := by
  have hind := (hp.independent hj hm).comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have hi := hind.integral_mul_eq_mul_integral
    (hm.pow_const 2).aestronglyMeasurable ((measurable_coordinate N j).pow_const 2).aestronglyMeasurable
  change (∫ z, (H z)^2 * (coordinate N j z)^2 ∂gaussianProduct (Fin (N+1))) = (∫ z, (H z)^2 ∂gaussianProduct (Fin (N+1))) *
      (∫ z, (coordinate N j z)^2 ∂gaussianProduct (Fin (N+1))) at hi
  simp only [rawIncrement, mul_pow]
  rw [hi, gaussian_second_moment (coordinate_hasLaw N j), mul_one]

lemma rawIncrement_depends {N j : ℕ} {H : (Fin (N+1) → ℝ) → ℝ}
    (hj : j<N+1) (hp : DependsBefore j H) : DependsBefore (j+1) (rawIncrement H j) := by
  intro z z' hz
  dsimp only [rawIncrement]
  rw [hp z z' (fun i hi ↦ hz i (by omega)), coordinate_eq_apply hj, coordinate_eq_apply hj,
    hz ⟨j,hj⟩ (by simp)]

lemma rawIncrement_past_product {N j : ℕ} {H F : (Fin (N+1) → ℝ) → ℝ}
    (hj : j<N+1) (hm : Measurable H) (fm : Measurable F)
    (hp : DependsBefore j H) (fp : DependsBefore j F) :
    (∫ z, F z * rawIncrement H j z ∂gaussianProduct (Fin (N+1)))=0 := by
  have hi := ((fp.mul hp).independent hj (fm.mul hm)).integral_mul_eq_mul_integral
    (fm.mul hm).aestronglyMeasurable (measurable_coordinate N j).aestronglyMeasurable
  change (∫ z, (F z*H z)*coordinate N j z ∂gaussianProduct (Fin (N+1)))=_ at hi
  simp only [rawIncrement, ←mul_assoc]
  rw [hi, gaussian_mean (coordinate_hasLaw N j), mul_zero]

lemma rawIncrement_pair {N : ℕ} {H : Fin N → (Fin (N+1) → ℝ) → ℝ}
    (hm : ∀ i, Measurable (H i)) (hp : ∀ i : Fin N, DependsBefore (i : ℕ) (H i))
    (i j : Fin N) (hij : i ≠ j) :
    (∫ z, rawIncrement (H i) i z * rawIncrement (H j) j z
      ∂gaussianProduct (Fin (N+1)))=0 := by
  rcases lt_or_gt_of_ne hij with hij|hij
  · exact rawIncrement_past_product (by omega) (hm j)
      ((hm i).mul (measurable_coordinate N i)) (hp j)
      ((rawIncrement_depends (by omega) (hp i)).mono (by exact Nat.succ_le_of_lt hij))
  · rw [show (fun z ↦ rawIncrement (H i) i z * rawIncrement (H j) j z) =
        (fun z ↦ rawIncrement (H j) j z * rawIncrement (H i) i z) by funext z; ring]
    exact rawIncrement_past_product (by omega) (hm i)
      ((hm j).mul (measurable_coordinate N j)) (hp i)
      ((rawIncrement_depends (by omega) (hp j)).mono (by exact Nat.succ_le_of_lt hij))

lemma finiteRaw_memLp {N : ℕ} {δ : ℝ} {H : Fin N → (Fin (N+1) → ℝ) → ℝ}
    (hm : ∀ i, Measurable (H i)) (hp : ∀ i : Fin N, DependsBefore (i : ℕ) (H i))
    (hH : ∀ i, MemLp (H i) 2 (gaussianProduct (Fin (N+1)))) :
    MemLp (finiteRawMartingale δ H) 2 (gaussianProduct (Fin (N+1))) := by
  have hc := memLp_linearCombination
    (fun i : Fin N ↦ rawIncrement_memLp (by omega) (hm i) (hp i) (hH i)) (fun _ ↦ Real.sqrt δ)
  change MemLp (fun z ↦ ∑ i : Fin N, Real.sqrt δ * H i z * coordinate N i z) 2 _
  convert hc using 1
  funext z
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [rawIncrement]
  ring

lemma finiteRaw_isometry {N : ℕ} {δ : ℝ} (hδ : 0≤δ)
    {H : Fin N → (Fin (N+1) → ℝ) → ℝ}
    (hm : ∀ i, Measurable (H i)) (hp : ∀ i : Fin N, DependsBefore (i : ℕ) (H i))
    (hH : ∀ i, MemLp (H i) 2 (gaussianProduct (Fin (N+1)))) :
    (∫ z, (finiteRawMartingale δ H z)^2 ∂gaussianProduct (Fin (N+1))) =
      δ * ∑ i : Fin N, ∫ z, (H i z)^2 ∂gaussianProduct (Fin (N+1)) := by
  have hm' (i : Fin N) := (rawIncrement_memLp (by omega) (hm i) (hp i) (hH i)).const_mul (Real.sqrt δ)
  have ho : ∀ i j : Fin N, i≠j →
      (∫ z, (Real.sqrt δ*rawIncrement (H i) i z)*(Real.sqrt δ*rawIncrement (H j) j z)
        ∂gaussianProduct (Fin (N+1)))=0 := by
    intro i j hij
    simp_rw [show ∀ a b : ℝ, (Real.sqrt δ*a)*(Real.sqrt δ*b)=δ*(a*b) by
      intro a b
      rw [show (Real.sqrt δ*a)*(Real.sqrt δ*b)=(Real.sqrt δ)^2*(a*b) by ring, Real.sq_sqrt hδ]]
    rw [integral_const_mul, rawIncrement_pair hm hp i j hij, mul_zero]
  have heq := orthogonal_sum_square hm' ho
  simp only [finiteRawMartingale, ←mul_assoc, rawIncrement] at heq ⊢
  rw [heq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_assoc, mul_pow, Real.sq_sqrt hδ, integral_const_mul]
  congr 1
  simpa only [rawIncrement, mul_pow] using rawIncrement_variance (by omega) (hm i) (hp i)

lemma coupled_mesh_general_moment_bounds {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {X : ℝ → Ω → ℝ} {T K L D La : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : GradientStrip T γ u K L) (hD0 : 0≤D) (hLa : 0≤La)
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    (hLip : ∀ t∈Icc (0 : ℝ) T, ∀ x y, |deriv (u t) x-deriv (u t) y|≤La*|x-y|)
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hpaths : ∀ᵐ ω ∂μ,
      (∀ t∈Icc (0 : ℝ) T, X t ω=B (Real.toNNReal t) ω+
        ∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) ∧ X 0 ω=0)
    {N : ℕ} (hN : 0<N) (j : Fin N) :
    |(∫ z, (meshRaw T N γ u j z)^2 ∂gaussianProduct (Fin (N+1)))-
      (∫ ω, (deriv (u (meshTime T N j)) (X (meshTime T N j) ω))^2 ∂μ)|≤
      (2*D*La)*Real.sqrt (∫ ω, (meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ) ∧
    |(∫ z, meshRaw T N γ u j z ∂gaussianProduct (Fin (N+1)))-
      ∫ ω, deriv (u (meshTime T N j)) (X (meshTime T N j) ω) ∂μ|≤
      La*Real.sqrt (∫ ω, (meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ) := by
  let t := meshTime T N j
  let F (ω : Ω) := deriv (u t) (coupledEuler T γ u B N j ω)
  let G (ω : Ω) := deriv (u t) (X t ω)
  let E := meshMaxError T X (coupledEuler T γ u B) N
  have ht : t∈Icc (0 : ℝ) T := mesh_time_mem hT.le hN j.isLt.le
  have hd : Continuous (deriv (u t)) := (h.smooth t ht).continuous_deriv (by norm_num)
  have hFM : MemLp F 2 μ := MemLp.of_bound
    (hd.measurable.comp_aemeasurable (coupled_euler_measurable hB hT h N j j.isLt.le).aemeasurable).aestronglyMeasurable D
      (Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs, F] using hD t ht _))
  have hGM : MemLp G 2 μ := MemLp.of_bound
    (hd.measurable.comp_aemeasurable (hXM t ht).aemeasurable).aestronglyMeasurable D
      (Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs, G] using hD t ht _))
  have hEM : MemLp E 2 μ := coupled_mesh_error_memLp hB hT h hXM hpaths hN
  have hFG (ω : Ω) : |F ω-G ω|≤La*|E ω| := by
    have he : |coupledEuler T γ u B N j ω-X t ω|≤E ω :=
      le_initialMax (f := fun k ↦ |coupledEuler T γ u B N k ω-X (meshTime T N k) ω|) j.isLt.le
    calc
      _ ≤ La*|coupledEuler T γ u B N j ω-X t ω| := hLip t ht _ _
      _ ≤ La*(E ω) := mul_le_mul_of_nonneg_left he hLa
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_abs_self _) hLa
  have hlaw := coupledCoordinates_hasLaw hB hT hN
  have hmraw := mesh_raw_measurable hT.le h hN j.isLt.le
  have heq1 : (∫ z, meshRaw T N γ u j z ∂gaussianProduct (Fin (N+1)))=∫ ω, F ω ∂μ := by
    rw [←hlaw.integral_comp hmraw.aestronglyMeasurable]
    simp only [Function.comp_apply, F, meshRaw, t, coupledEuler, ite_eq_right (Nat.ne_of_gt hN)]
  have heq2 : (∫ z, (meshRaw T N γ u j z)^2 ∂gaussianProduct (Fin (N+1)))=∫ ω, (F ω)^2 ∂μ := by
    rw [←hlaw.integral_comp (hmraw.pow_const 2).aestronglyMeasurable]
    simp only [Function.comp_apply, F, meshRaw, t, coupledEuler, ite_eq_right (Nat.ne_of_gt hN)]
  constructor
  · rw [heq2]
    exact second_moment_perturbation hFM hGM hEM hD0 hLa
      (Eventually.of_forall (fun ω ↦ ⟨hD t ht _,hD t ht _,hFG ω⟩))
  · rw [heq1]
    exact first_moment_perturbation hFM hGM hEM hLa (Eventually.of_forall hFG)

lemma integral_product_CS {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ ω, f ω*g ω ∂μ| ≤ Real.sqrt (∫ ω, (f ω)^2 ∂μ) * Real.sqrt (∫ ω, (g ω)^2 ∂μ) := by
  have hp : (2 : ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have hh := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := f) (g := g) hp
    (by simpa using hf) (by simpa using hg)
  simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs, ←Real.sqrt_eq_rpow] at hh
  exact (abs_integral_le_integral_abs.trans_eq
    (integral_congr_ae (Eventually.of_forall (fun _ ↦ abs_mul _ _)))).trans hh

lemma rawIncrement_coordinate_pair {N : ℕ} {H : (Fin (N+1) → ℝ) → ℝ}
    {i j : ℕ} (hi : i<N+1) (hj : j<N+1) (hm : Measurable H) (hp : DependsBefore i H) :
    (∫ z, rawIncrement H i z * coordinate N j z ∂gaussianProduct (Fin (N+1))) =
      if i=j then ∫ z, H z ∂gaussianProduct (Fin (N+1)) else 0 := by
  split_ifs with hij
  · subst j
    have hind := (hp.independent hi hm).comp measurable_id (measurable_id.pow_const 2)
    have heq := hind.integral_mul_eq_mul_integral
      hm.aestronglyMeasurable ((measurable_coordinate N i).pow_const 2).aestronglyMeasurable
    change (∫ z, H z*(coordinate N i z)^2 ∂gaussianProduct (Fin (N+1))) =
      (∫ z, H z ∂gaussianProduct (Fin (N+1))) *
      (∫ z, (coordinate N i z)^2 ∂gaussianProduct (Fin (N+1))) at heq
    simp only [rawIncrement, mul_assoc, ←pow_two]
    rw [heq, gaussian_second_moment (coordinate_hasLaw N i), mul_one]
  · rcases lt_or_gt_of_ne hij with hij|hij
    · have hp' : DependsBefore j (rawIncrement H i) :=
        (rawIncrement_depends hi hp).mono (Nat.succ_le_of_lt hij)
      have heq := (hp'.independent hj (hm.mul (measurable_coordinate N i))).integral_mul_eq_mul_integral
        (hm.mul (measurable_coordinate N i)).aestronglyMeasurable (measurable_coordinate N j).aestronglyMeasurable
      change (∫ z, rawIncrement H i z * coordinate N j z ∂gaussianProduct (Fin (N+1)))=_ at heq
      rw [heq, gaussian_mean (coordinate_hasLaw N j), mul_zero]
    · have hp' : DependsBefore i (coordinate N j) := by
        intro z z' hz
        rw [coordinate_eq_apply hj, coordinate_eq_apply hj, hz ⟨j,hj⟩ hij]
      rw [show (fun z ↦ rawIncrement H i z*coordinate N j z)=
        (fun z ↦ coordinate N j z*rawIncrement H i z) by funext z; ring]
      exact rawIncrement_past_product hi hm (measurable_coordinate N j) hp hp'

lemma finiteRaw_coordinate_coefficient {N : ℕ} {δ : ℝ}
    {H : Fin N → (Fin (N+1) → ℝ) → ℝ}
    (hm : ∀ i, Measurable (H i)) (hp : ∀ i : Fin N, DependsBefore (i : ℕ) (H i))
    (hH : ∀ i, MemLp (H i) 2 (gaussianProduct (Fin (N+1)))) (j : Fin N) :
    (∫ z, finiteRawMartingale δ H z * coordinate N j z ∂gaussianProduct (Fin (N+1))) =
      Real.sqrt δ * ∫ z, H j z ∂gaussianProduct (Fin (N+1)) := by
  have hf : finiteRawMartingale δ H = fun z ↦ ∑ i : Fin N, Real.sqrt δ*rawIncrement (H i) i z := by
    funext z
    apply Finset.sum_congr rfl
    intro i _
    dsimp [rawIncrement]
    ring
  rw [hf, integral_linearCombination_mul
    (fun i : Fin N ↦ rawIncrement_memLp (by omega) (hm i) (hp i) (hH i))
    (gaussian_memLp (coordinate_hasLaw N j) 2 (by norm_num))]
  have hpairs (i : Fin N) :
      (∫ z, rawIncrement (H i) i z * coordinate N j z ∂gaussianProduct (Fin (N+1))) =
        if i=j then ∫ z, H i z ∂gaussianProduct (Fin (N+1)) else 0 := by
    simpa only [Fin.val_inj] using
      rawIncrement_coordinate_pair (by omega) (by omega) (hm i) (hp i) (j := (j : ℕ))
  simp_rw [hpairs]
  simp only [ mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma finiteRaw_brownian_covariance {N : ℕ} {δ : ℝ} (hδ : 0≤δ)
    {H : Fin N → (Fin (N+1) → ℝ) → ℝ}
    (hm : ∀ i, Measurable (H i)) (hp : ∀ i : Fin N, DependsBefore (i : ℕ) (H i))
    (hH : ∀ i, MemLp (H i) 2 (gaussianProduct (Fin (N+1)))) :
    (∫ z, finiteRawMartingale δ H z *
      (∑ j : Fin N, Real.sqrt δ * coordinate N j z) ∂gaussianProduct (Fin (N+1))) =
      δ * ∑ j : Fin N, ∫ z, H j z ∂gaussianProduct (Fin (N+1)) := by
  have hR := finiteRaw_memLp hm hp hH (δ := δ)
  simp_rw [Finset.mul_sum, show ∀ r d z : ℝ, r*(d*z)=d*(r*z) by intros; ring]
  have hi (j : Fin N) : Integrable (fun z ↦ Real.sqrt δ *
      (finiteRawMartingale δ H z * coordinate N j z)) (gaussianProduct (Fin (N+1))) :=
    (hR.integrable_mul (gaussian_memLp (coordinate_hasLaw N j) 2 (by norm_num))).const_mul (Real.sqrt δ)
  rw [integral_finsetSum Finset.univ (fun j _ ↦ hi j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, finiteRaw_coordinate_coefficient hm hp hH,
    ←mul_assoc, ←pow_two, Real.sq_sqrt hδ]

lemma second_moment_L2_perturbation {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} {C : ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hC : (∫ ω, (f ω)^2 ∂μ)+(∫ ω, (g ω)^2 ∂μ)≤C) :
    |(∫ ω, (f ω)^2 ∂μ)-(∫ ω, (g ω)^2 ∂μ)| ≤
      Real.sqrt (∫ ω, (f ω-g ω)^2 ∂μ) * Real.sqrt (2*C) := by
  have heq : (∫ ω, (f ω)^2 ∂μ)-(∫ ω, (g ω)^2 ∂μ)=
      ∫ ω, (f ω-g ω)*(f ω+g ω) ∂μ := by
    rw [←integral_sub hf.integrable_sq hg.integrable_sq]
    apply integral_congr_ae
    exact Eventually.of_forall (fun _ ↦ by ring)
  rw [heq]
  apply (integral_product_CS (hf.sub hg) (hf.add hg)).trans
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ ∫ ω, 2*(f ω)^2+2*(g ω)^2 ∂μ := by
      apply integral_mono (hf.add hg).integrable_sq
        ((hf.integrable_sq.const_mul 2).add (hg.integrable_sq.const_mul 2))
      intro ω
      dsimp only [Pi.add_apply]
      nlinarith [sq_nonneg (f ω-g ω)]
    _ = 2*((∫ ω, (f ω)^2 ∂μ)+(∫ ω, (g ω)^2 ∂μ)) := by
      rw [integral_add (hf.integrable_sq.const_mul 2) (hg.integrable_sq.const_mul 2),
        integral_const_mul, integral_const_mul]
      ring
    _ ≤ 2*C := by linarith

lemma perturbed_grid_riemann_tendsto {f : ℝ → ℝ} {T : ℝ}
    {v : (N : ℕ) → Fin N → ℝ} {r : ℕ → ℝ}
    (hT : 0<T) (hf : ContinuousOn f (Icc (0 : ℝ) T))
    (hr0 : Tendsto r atTop (𝓝 0))
    (hv : ∀ᶠ N in atTop, ∀ i : Fin N, |v N i-f ((i : ℕ)*(T/N))|≤r N) :
    Tendsto (fun N : ℕ ↦ (T/N)*(∑ i : Fin N, v N i)) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, f t)) := by
  have herr : Tendsto (fun N : ℕ ↦ (T/N)*(∑ i : Fin N, v N i)-
      (T/N)*(∑ i : Fin N, f ((i : ℕ)*(T/N)))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun N ↦ T*r N)
    · filter_upwards [hv, eventually_gt_atTop 0] with N hNv hN
      have hδ : 0≤T/(N : ℝ) := div_nonneg hT.le (Nat.cast_nonneg _)
      have hmul : (T/(N : ℝ))*(N : ℝ)=T := by field_simp
      rw [Real.norm_eq_abs, ←mul_sub, ←Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hδ]
      calc
        _ ≤ (T/N)*(∑ _ : Fin N, r N) := by
          apply mul_le_mul_of_nonneg_left _ hδ
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ ↦ hNv i))
        _ = T*r N := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ←mul_assoc, hmul]
    · simpa only [mul_zero] using hr0.const_mul T
  have hR : Tendsto (fun N : ℕ ↦ (T/N)*(∑ i : Fin N, f ((i : ℕ)*(T/N)))) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, f t)) := by
    convert uniform_grid_riemann_tendsto hT hf using 1
    funext N
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ f ((j : ℝ)*(T/N)))]
  simpa only [sub_add_cancel, zero_add] using herr.add hR

lemma derivative_joint_continuous {u : ℝ → ℝ → ℝ} {T La : ℝ} (hLa : 0≤La)
    (hLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |deriv (u s) x-deriv (u t) y|≤La*(|s-t|+|x-y|)) :
    ContinuousOn (fun p : ℝ×ℝ ↦ deriv (u p.1) p.2) {p | p.1∈Icc (0 : ℝ) T} := by
  apply (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal (2*La)) ?_).continuousOn
  intro p hp q hq
  rw [Real.coe_toNNReal _ (by positivity), Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
  calc
    _ ≤ La*(|p.1-q.1|+|p.2-q.2|) := hLip p.1 hp q.1 hq p.2 q.2
    _ ≤ _ := by
      have h₁ := le_max_left |p.1-q.1| |p.2-q.2|
      have h₂ := le_max_right |p.1-q.1| |p.2-q.2|
      nlinarith

lemma mean_derivative_square_continuous {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℝ → Ω → ℝ} {T D La : ℝ} {u : ℝ → ℝ → ℝ}
    (hD0 : 0≤D) (hLa : 0≤La)
    (hd : ∀ t∈Icc (0 : ℝ) T, Continuous (deriv (u t)))
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    (hLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |deriv (u s) x-deriv (u t) y|≤La*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hXC : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T)) :
    ContinuousOn (fun t ↦ ∫ ω, (deriv (u t) (X t ω))^2 ∂μ) (Icc (0 : ℝ) T) := by
  apply continuousOn_of_dominated (bound := fun _ ↦ D^2)
  · intro t ht
    exact (((hd t ht).measurable.comp_aemeasurable (hXM t ht).aemeasurable).pow_const 2).aestronglyMeasurable
  · intro t ht
    exact Eventually.of_forall (fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hh := hD t ht (X t ω)
      nlinarith [sq_abs (deriv (u t) (X t ω)), abs_nonneg (deriv (u t) (X t ω))])
  · exact integrable_const _
  · filter_upwards [hXC] with ω hω
    exact ((derivative_joint_continuous hLa hLip).comp
      (continuousOn_id.prodMk hω) (fun t ht ↦ ht)).pow 2

lemma mesh_terminal_memLp {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0≤T) (h : GradientStrip T γ u K L) {N : ℕ} (hN : 0<N) :
    MemLp (meshTerminal T N γ u) 2 (gaussianProduct (Fin (N+1))) := by
  apply MemLp.of_bound (mesh_terminal_measurable hT h hN).aestronglyMeasurable 1
  exact Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs, meshTerminal] using h.bounded T ⟨hT,le_rfl⟩ _)

lemma bounded_second_moment {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} {D : ℝ} (hf : MemLp f 2 μ)
    (hD : 0≤D) (hb : ∀ᵐ ω ∂μ, |f ω|≤D) : (∫ ω, (f ω)^2 ∂μ)≤D^2 := by
  calc
    _ ≤ ∫ _ : Ω, D^2 ∂μ := by
      apply integral_mono_ae hf.integrable_sq (integrable_const _)
      filter_upwards [hb] with ω hω
      nlinarith [sq_abs (f ω), abs_nonneg (f ω)]
    _ = _ := by simp

lemma mesh_raw_stochastic_square_bound {T K L D : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : GradientStrip T γ u K L) (hD0 : 0≤D)
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    {N : ℕ} (hN : 0<N) :
    (∫ z, (finiteRawMartingale (stepSize T N) (fun i : Fin N ↦ meshRaw T N γ u i) z)^2
      ∂gaussianProduct (Fin (N+1))) ≤ T*D^2 := by
  have hδ : 0 ≤ stepSize T N := div_nonneg hT.le (Nat.cast_nonneg _)
  rw [finiteRaw_isometry hδ (fun i ↦ mesh_raw_measurable hT.le h hN i.isLt.le)
    (fun i ↦ mesh_raw_depends T i.isLt.le γ u)
    (fun i ↦ mesh_raw_memLp hT.le h hD hN i.isLt.le)]
  calc
    _ ≤ stepSize T N * ∑ _ : Fin N, D^2 := by
      apply mul_le_mul_of_nonneg_left _ hδ
      apply Finset.sum_le_sum
      intro i _
      exact bounded_second_moment (mesh_raw_memLp hT.le h hD hN i.isLt.le) hD0
        (Eventually.of_forall (fun z ↦ hD _ (mesh_time_mem hT.le hN i.isLt.le) _))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, stepSize]
      field_simp

lemma mesh_terminal_stochastic_second_moment_error {T K L D : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : GradientStrip T γ u K L) (hD0 : 0≤D)
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    {N : ℕ} (hN : 0<N) :
    |(∫ z, (meshTerminal T N γ u z)^2 ∂gaussianProduct (Fin (N+1)))-
      (stepSize T N)*∑ i : Fin N, ∫ z, (meshRaw T N γ u i z)^2 ∂gaussianProduct (Fin (N+1))|≤
      Real.sqrt (gradientMeshError T N γ u) * Real.sqrt (2*(1+T*D^2)) := by
  have hU := mesh_terminal_memLp hT.le h hN
  have hR := finiteRaw_memLp (δ := stepSize T N)
    (fun i : Fin N ↦ mesh_raw_measurable hT.le h hN i.isLt.le)
    (fun i : Fin N ↦ mesh_raw_depends T i.isLt.le γ u)
    (fun i : Fin N ↦ mesh_raw_memLp hT.le h hD hN i.isLt.le)
  have hU2 : (∫ z, (meshTerminal T N γ u z)^2 ∂gaussianProduct (Fin (N+1)))≤1 := by
    simpa only [one_pow] using bounded_second_moment hU (by norm_num : (0 : ℝ)≤1)
      (Eventually.of_forall (fun z ↦ h.bounded T ⟨hT.le,le_rfl⟩ _))
  have hR2 := mesh_raw_stochastic_square_bound hT h hD0 hD hN
  have herr := second_moment_L2_perturbation hU hR (add_le_add hU2 hR2)
  have hδ : 0 ≤ stepSize T N := div_nonneg hT.le (Nat.cast_nonneg _)
  rw [finiteRaw_isometry hδ (fun i : Fin N ↦ mesh_raw_measurable hT.le h hN i.isLt.le)
    (fun i : Fin N ↦ mesh_raw_depends T i.isLt.le γ u)
    (fun i : Fin N ↦ mesh_raw_memLp hT.le h hD hN i.isLt.le)] at herr
  exact herr

end SKValue
end

end OAI
