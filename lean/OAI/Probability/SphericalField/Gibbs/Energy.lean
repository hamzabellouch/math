import Mathlib
import OAI.Probability.SphericalField.Heat.Logarithm
import OAI.Probability.SphericalField.Gibbs.ReplicaIdentity

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace

namespace SphericalPerceptron
section EnergyFactorization
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

end EnergyFactorization
end SphericalPerceptron

namespace SphericalPerceptron

lemma localMax_second_deriv_nonpos {f : ℝ → ℝ} {u : ℝ}
    (hm : IsLocalMax f u) (hc : ContinuousAt f u) : deriv (deriv f) u ≤ 0 := by
  by_contra! h
  have hn := isLocalMin_of_deriv_deriv_pos h hm.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 u] (fun _ => f u) := by
    filter_upwards [hm,hn] with x hx hy
    exact le_antisymm hx hy
  have hz := he.deriv.deriv_eq
  simp at hz
  linarith

lemma quadratic_contact_second_deriv {A D : ℝ → ℝ} {u a c v : ℝ}
    (hD : ∀ t, HasDerivAt A (D t) t) (hv : HasDerivAt D v u)
    (hmin : IsLocalMin (fun t => c*(t-a)^2-A t) u) : v ≤ 2*c := by
  let f := fun t => A t-c*(t-a)^2
  have hmax : IsLocalMax f u := by
    simpa only [f,neg_sub] using hmin.neg
  have hd (t : ℝ) : HasDerivAt f (D t-2*c*(t-a)) t := by
    convert! (hD t).sub (((hasDerivAt_id t).sub_const a).pow 2 |>.const_mul c) using 1
    simp
    ring
  have hderiv : deriv f = fun t => D t-2*c*(t-a) := funext fun t => (hd t).deriv
  have h2 : HasDerivAt (deriv f) (v-2*c) u := by
    rw [hderiv]
    simpa only [Pi.sub_def,id_eq,one_mul,mul_one] using hv.sub (((hasDerivAt_id u).sub_const a).const_mul (2*c))
  have hh := localMax_second_deriv_nonpos hmax (hd u).continuousAt
  rw [h2.deriv] at hh
  linarith

end SphericalPerceptron

end
end
end

end OAI
