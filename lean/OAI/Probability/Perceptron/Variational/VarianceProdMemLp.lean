import Mathlib
import OAI.Probability.Perceptron.Variational.Trial
import OAI.Probability.Perceptron.Pressure.VectorPartition
import OAI.Probability.Perceptron.Interpolation.GibbsReplicaMean

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
namespace SphericalPerceptronFreeEnergy

section
section GeneralProductVariance
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

lemma variance_prod_le_memLp {F : X × Y → ℝ}
    (hp : MemLp F 2 (μ.prod ν)) (hs : ∀ x, MemLp (fun y => F (x,y)) 2 ν)
    (hh : MemLp (fun x => ∫ y, F (x,y) ∂ν) 2 μ) {A B : ℝ}
    (hA : ∀ x, variance (fun y => F (x,y)) ν ≤ A)
    (hB : variance (fun x => ∫ y, F (x,y) ∂ν) μ ≤ B) :
    variance F (μ.prod ν) ≤ A+B := by
  have hi : (∫ x, ∫ y, F (x,y)^2 ∂ν ∂μ) ≤ A+∫ x, (∫ y, F (x,y) ∂ν)^2 ∂μ := by
    calc
      _ ≤ ∫ x, (A+(∫ y, F (x,y) ∂ν)^2) ∂μ := by
        apply integral_mono hp.integrable_sq.integral_prod_left
          ((integrable_const A).add hh.integrable_sq)
        intro x
        have hv := hA x
        rw [variance_eq_sub (hs x)] at hv
        simpa only [Pi.pow_apply, Pi.add_apply] using sub_le_iff_le_add.mp hv
      _ = _ := by rw [integral_add (integrable_const _) hh.integrable_sq]; simp
  rw [variance_eq_sub hh] at hB
  rw [variance_eq_sub hp]
  simp only [Pi.pow_apply] at hB ⊢
  rw [integral_prod _ hp.integrable_sq,
    integral_prod _ (hp.integrable (by norm_num))]
  linarith

end GeneralProductVariance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {S : Type*} [MeasurableSpace S] (ρ : Measure S) [IsProbabilityMeasure ρ]

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorLogPartition_bound {W : S → ℝ} {V : S → StrongDual ℝ E}
    (hWm : Measurable W) (hVm : Measurable V) {K C : ℝ}
    (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) (x : E) :
    |vectorLogPartition ρ W V x| ≤ K+C*‖x‖ := by
  have hh := abs_log_integral_exp_sub_le ρ
    (vectorPartition_integrable ρ hWm hVm hW hV x)
    (show Integrable (fun _ : S => Real.exp 0) ρ by simp)
    (vectorPartition_pos ρ hWm hVm hW hV x)
    (show 0 < ∫ _ : S, Real.exp 0 ∂ρ by simp)
    (c := K+C*‖x‖) (fun s => by simpa using vectorEnergy_bound hW hV x s)
  simpa [vectorLogPartition,vectorPartition] using hh

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorLogPartition_data_bound {W W' : S → ℝ} {V : S → StrongDual ℝ E}
    (hWm : Measurable W) (hWm' : Measurable W') (hVm : Measurable V) {K K' C c : ℝ}
    (hW : ∀ s, |W s| ≤ K) (hW' : ∀ s, |W' s| ≤ K') (hV : ∀ s, ‖V s‖ ≤ C)
    (hWc : ∀ s, |W s-W' s| ≤ c) (x : E) :
    |vectorLogPartition ρ W V x-vectorLogPartition ρ W' V x| ≤ c := by
  exact abs_log_integral_exp_sub_le ρ
    (vectorPartition_integrable ρ hWm hVm hW hV x)
    (vectorPartition_integrable ρ hWm' hVm hW' hV x)
    (vectorPartition_pos ρ hWm hVm hW hV x)
    (vectorPartition_pos ρ hWm' hVm hW' hV x)
    (fun s => by simpa only [add_sub_add_right_eq_sub] using hWc s)

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [Nonempty X] (μ : Measure X) [IsProbabilityMeasure μ]

lemma vectorLogPartition_mixed_variance (n : ℕ)
    {W : (Fin n → X) → S → ℝ} {V : S → StrongDual ℝ E}
    (hWm : Measurable (Function.uncurry W)) (hWc : ∀ s, Continuous (fun p => W p s))
    (hVm : Measurable V) {K C c : ℝ} (hC : 0 ≤ C)
    (hW : ∀ p s, |W p s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C)
    (hosc : ∀ p i z s, |W (Function.update p i z) s-W p s| ≤ c) :
    variance (fun p => vectorLogPartition ρ (W p.1) V p.2)
      ((Measure.pi fun _ : Fin n => μ).prod (stdGaussian E)) ≤
      Real.pi^2/8*C^2+(n:ℝ)*c^2 := by
  classical
  let ν := Measure.pi (fun _ : Fin n => μ)
  let γ := stdGaussian E
  let F := fun (p : Fin n → X) (g : E) => vectorLogPartition ρ (W p) V g
  have hWm' (p) : Measurable (W p) := hWm.comp (measurable_const.prodMk measurable_id)
  have hFm : Measurable (Function.uncurry F) := by
    have hm : Measurable (fun p : ((Fin n → X)×E)×S =>
        Real.exp (W p.1.1 p.2+V p.2 p.1.2)) := by
      apply Measurable.exp
      exact (hWm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).add
        (((continuous_fst.clm_apply continuous_snd : Continuous
          (fun p : StrongDual ℝ E × E => p.1 p.2)).measurable).comp
          ((hVm.comp measurable_snd).prodMk (measurable_snd.comp measurable_fst)))
    exact hm.stronglyMeasurable.integral_prod_right'.measurable.log
  have hFB (p) (g) : |F p g| ≤ K+C*‖g‖ :=
    vectorLogPartition_bound ρ (hWm' p) hVm (hW p) hV g
  have hGB : MemLp (fun g : E => K+C*‖g‖) 2 γ := by
    exact (memLp_const K).add ((IsGaussian.memLp_id γ 2 (by simp)).norm.const_mul C)
  have hFL (p) : MemLp (F p) 2 γ := hGB.mono'
    ((hFm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (ae_of_all _ fun g => by simpa only [Real.norm_eq_abs] using hFB p g)
  have hFp (g : E) : Continuous (fun p => F p g) := by
    have hp : Continuous (fun p => vectorPartition ρ (W p) V g) := by
      apply continuous_of_dominated (bound := fun _ => Real.exp (K+C*‖g‖))
      · intro p; exact (vectorPartition_integrable ρ (hWm' p) hVm (hW p) hV g).aestronglyMeasurable
      · intro p; apply ae_of_all; intro s
        rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr ((le_abs_self _).trans (vectorEnergy_bound (hW p) hV g s))
      · exact integrable_const _
      · exact ae_of_all _ fun s => ((hWc s).add continuous_const).rexp
    exact hp.log (fun p => (vectorPartition_pos ρ (hWm' p) hVm (hW p) hV g).ne')
  have hAc : Continuous (fun p => ∫ g, F p g ∂γ) := by
    apply continuous_of_dominated (bound := fun g => K+C*‖g‖)
    · intro p; exact (hFL p).aestronglyMeasurable
    · intro p; exact ae_of_all _ fun g => by simpa only [Real.norm_eq_abs] using hFB p g
    · exact hGB.integrable (by norm_num)
    · exact ae_of_all _ hFp
  have hAB (p) : |∫ g, F p g ∂γ| ≤ ∫ g, (K+C*‖g‖) ∂γ := by
    exact (norm_integral_le_integral_norm _).trans
      (integral_mono (hFL p |>.integrable (by norm_num) |>.norm)
        (hGB.integrable (by norm_num)) (fun g => by simpa only [Real.norm_eq_abs] using hFB p g))
  have hAL : MemLp (fun p => ∫ g, F p g ∂γ) 2 ν :=
    MemLp.of_bound hAc.aestronglyMeasurable _ (ae_of_all _ hAB)
  apply variance_prod_le_memLp ν γ
    ((hGB.comp_snd ν).mono' hFm.aestronglyMeasurable
      (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs,Function.uncurry] using hFB p.1 p.2)) hFL hAL
  · intro p
    exact vectorLogPartition_gaussian_variance ρ (hWm' p) hVm hC (hW p) hV
  · apply variance_pi_le_of_bounded_differences μ n hAc hAB
    intro p i z
    rw [← integral_sub ((hFL _).integrable (by norm_num)) ((hFL _).integrable (by norm_num))]
    have hh := norm_integral_le_of_norm_le_const (μ := γ)
      (f := fun g => F (Function.update p i z) g-F p g) (C := c)
      (ae_of_all _ fun g => by
        simpa only [Real.norm_eq_abs] using vectorLogPartition_data_bound ρ
          (hWm' _) (hWm' _) hVm (hW _) (hW _) hV (hosc p i z) g)
    simpa using hh

end

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma integral_observable_factorization_bound {F G : S → ℝ}
    (hF : Integrable F μ) (hG : Measurable G) {D : ℝ} (_hD : 0 ≤ D)
    (hGD : ∀ x, |G x| ≤ D) (a : ℝ) :
    |(∫ x, F x*G x ∂μ)-a*(∫ x, G x ∂μ)| ≤ D*∫ x, |F x-a| ∂μ := by
  have hGI : Integrable G μ := Integrable.of_bound hG.aestronglyMeasurable D
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hGD x)
  have hFG := hF.mul_bdd hG.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hGD x)
  have hFA := (hF.sub (integrable_const a)).abs
  have he : (∫ x, F x*G x ∂μ)-a*(∫ x, G x ∂μ) = ∫ x, (F x-a)*G x ∂μ := by
    simp_rw [sub_mul]
    rw [integral_sub hFG (hGI.const_mul a),integral_const_mul]
  rw [he,← integral_const_mul]
  rw [← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono
    ((hF.sub (integrable_const a)).mul_bdd hG.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hGD x)).norm
    (hFA.const_mul D)
  intro x
  dsimp only [Pi.sub_apply]
  rw [Real.norm_eq_abs,abs_mul,mul_comm D]
  exact mul_le_mul_of_nonneg_left (hGD x) (abs_nonneg _)

lemma replicaMean_energy_factorization_bound {H Y : S → ℝ} {n : ℕ} (j : Fin n)
    {G : (Fin n → S) → ℝ} (hH : Measurable H) (hY : Measurable Y) (hG : Measurable G)
    {A B D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (hHA : ∀ x, |H x| ≤ A)
    (hYB : ∀ x, |Y x| ≤ B) (hGD : ∀ x, |G x| ≤ D) (a : ℝ) :
    |gibbsReplicaMean μ H n (fun x => Y (x j)*G x)-a*gibbsReplicaMean μ H n G| ≤
      D*tiltMean μ H (fun x => |Y x-a|) 1 := by
  have := tilt_law_probability μ hH hA hHA 1
  have hYm : Measurable (fun x : Fin n → S => Y (x j)) := hY.comp (measurable_pi_apply j)
  have hYI : Integrable (fun x : Fin n → S => Y (x j))
      (Measure.pi fun _ : Fin n => tiltLaw μ H 1) :=
    Integrable.of_bound hYm.aestronglyMeasurable B
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hYB (x j))
  have hh := integral_observable_factorization_bound
    (Measure.pi fun _ : Fin n => tiltLaw μ H 1) hYI hG hD hGD a
  simp only [gibbsReplicaMean,tilt_replica_integral μ hH hA hHA]
  rw [← tilt_replica_coordinate μ (F := fun x => |Y x-a|) hH (by fun_prop) hA hHA n j 1,
    tilt_replica_integral μ hH hA hHA]
  exact hh

lemma measurable_tiltMean_param {Ω : Type*} [MeasurableSpace Ω] {H Y : Ω → S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y)) :
    Measurable (fun ω => tiltMean μ (H ω) (Y ω) 1) := by
  simp only [tiltMean,tiltIntegral,tiltPartition,one_mul]
  exact ((hH.exp.mul hY).stronglyMeasurable.integral_prod_right'.measurable).div
    hH.exp.stronglyMeasurable.integral_prod_right'.measurable

lemma measurable_replicaMean_param {Ω : Type*} [MeasurableSpace Ω]
    {H : Ω → S → ℝ} {n : ℕ} {Y : Ω → (Fin n → S) → ℝ}
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y)) :
    Measurable (fun ω => gibbsReplicaMean μ (H ω) n (Y ω)) := by
  apply measurable_tiltMean_param _ _ hY
  change Measurable (fun p : Ω×(Fin n → S) => ∑ i, H p.1 (p.2 i))
  exact Finset.measurable_sum _ fun i _ => hH.comp
    (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

lemma annealed_replica_energy_factorization_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {H Y : Ω → S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y))
    {A B : Ω → ℝ} (hA : ∀ ω, 0 ≤ A ω) (hB : ∀ ω, 0 ≤ B ω)
    (hHA : ∀ ω x, |H ω x| ≤ A ω) (hYB : ∀ ω x, |Y ω x| ≤ B ω)
    (hBI : Integrable B P) {n : ℕ} (j : Fin n) {G : (Fin n → S) → ℝ}
    (hG : Measurable G) {D : ℝ} (hD : 0 ≤ D) (hGD : ∀ x, |G x| ≤ D) (a : ℝ) :
    |(∫ ω, gibbsReplicaMean μ (H ω) n (fun x => Y ω (x j)*G x) ∂P) -
      a*(∫ ω, gibbsReplicaMean μ (H ω) n G ∂P)| ≤
      D*(∫ ω, tiltMean μ (H ω) (fun x => |Y ω x-a|) 1 ∂P) := by
  have hHm (ω) : Measurable (H ω) := hH.comp (measurable_const.prodMk measurable_id)
  have hYm (ω) : Measurable (Y ω) := hY.comp (measurable_const.prodMk measurable_id)
  have hFGm : Measurable (fun ω => gibbsReplicaMean μ (H ω) n (fun x => Y ω (x j)*G x)) := by
    apply measurable_replicaMean_param μ hH
    exact (hY.comp (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))).mul
      (hG.comp measurable_snd)
  have hFGI : Integrable (fun ω => gibbsReplicaMean μ (H ω) n (fun x => Y ω (x j)*G x)) P := by
    apply (hBI.mul_const D).mono' hFGm.aestronglyMeasurable
    exact ae_of_all _ fun ω => by
      simpa only [Real.norm_eq_abs, Pi.mul_def, Function.comp_def] using replicaMean_bound μ (hHm ω)
        (((hYm ω).comp (measurable_pi_apply j)).mul hG) (hA ω) (mul_nonneg (hB ω) hD)
        (hHA ω) (fun x => by simp only [Pi.mul_apply, Function.comp_apply]; rw [abs_mul]; exact mul_le_mul (hYB ω _) (hGD x) (abs_nonneg _) (hB ω))
  have hGI : Integrable (fun ω => gibbsReplicaMean μ (H ω) n G) P :=
    Integrable.of_bound (replicaMean_measurable μ hH hG).aestronglyMeasurable D
      (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using replicaMean_bound μ (hHm ω) hG (hA ω) hD (hHA ω) hGD)
  have hAI : Integrable (fun ω => tiltMean μ (H ω) (fun x => |Y ω x-a|) 1) P := by
    apply (hBI.add (integrable_const |a|)).mono'
      (measurable_tiltMean_param μ hH (show Measurable (Function.uncurry (fun ω x => |Y ω x-a|)) from (hY.sub_const a).abs)).aestronglyMeasurable
    exact ae_of_all _ fun ω => by
      simpa only [Real.norm_eq_abs, Pi.sub_apply, Pi.add_apply] using tilt_mean_bound μ (hHm ω) ((hYm ω).sub measurable_const |>.abs)
        (hA ω) (add_nonneg (hB ω) (abs_nonneg a)) (hHA ω)
        (fun x => by rw [abs_abs]; exact (abs_sub _ _).trans (add_le_add (hYB ω x) le_rfl)) 1
  rw [← integral_const_mul,← integral_sub hFGI (hGI.const_mul a),← integral_const_mul]
  rw [← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono (hFGI.sub (hGI.const_mul a)).norm (hAI.const_mul D)
  intro ω
  simpa only [Real.norm_eq_abs,Pi.sub_apply] using replicaMean_energy_factorization_bound μ j (hHm ω) (hYm ω) hG (hA ω) hD (hHA ω) (hYB ω) hGD a

end SphericalPerceptronFreeEnergy

end

end OAI
