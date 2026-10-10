import Mathlib
import OAI.Probability.Perceptron.Interpolation.CountableGaussianReplicaIBP
import OAI.Probability.Perceptron.Interpolation.NonlinearReplicaIBP

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma nonlinear_pattern_direction_ibp {m n : ℕ} (j : Fin n) (f : Jet3)
    {v : Fin (m+1) → S → ℝ} {h : S → ℝ} {w : Fin (m+1) → (Fin n → S) → ℝ}
    (hv : ∀ i, Measurable (v i)) (hh : Measurable h) (hw : ∀ i, Measurable (w i))
    {A C D : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hhA : ∀ x, |h x| ≤ A) (hvC : ∀ i x, |v i x| ≤ C) (hwD : ∀ i x, |w i x| ≤ D) :
    let b := gaussianField (m+1) v
    let H := fun g x => h x+f.f (b g x)
    let K := fun (x : Fin n→S) y => ∑ i, w i x*v i y
    (∫ g, gibbsReplicaMean μ (H g) n
      (fun x => f.d1 (b g (x j))*(∑ i, g i*w i x))
      ∂Measure.pi (fun _ => gaussianReal 0 1)) =
    ∫ g, gibbsReplicaMean μ (H g) n
      (fun x => (∑ l, f.d1 (b g (x l))*f.d1 (b g (x j))*K x (x l))+
        f.d2 (b g (x j))*K x (x j)) -
      n*gibbsReplicaMean μ (H g) (n+1)
        (fun x => f.d1 (b g (x 0))*f.d1 (b g (x j.succ))*K (fun l => x l.succ) (x 0))
      ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  dsimp only
  let γ := Measure.pi (fun _ : Fin (m+1) => gaussianReal 0 1)
  let b := gaussianField (m+1) v
  let H := fun g x => h x+f.f (b g x)
  let F := fun i g (x : Fin n→S) => f.d1 (b g (x j))*w i x
  let U := fun i g (x : Fin n→S) =>
    ((∑ l, f.d1 (b g (x l))*v i (x l))*f.d1 (b g (x j))+
      f.d2 (b g (x j))*v i (x j))*w i x
  let V := fun i g (x : Fin (n+1)→S) =>
    f.d1 (b g (x 0))*v i (x 0)*(f.d1 (b g (x j.succ))*w i (fun l => x l.succ))
  have hb : Measurable (Function.uncurry b) := gaussianField_measurable hv
  have hH : Measurable (Function.uncurry H) :=
    (hh.comp measurable_snd).add (f.f.continuous.measurable.comp hb)
  have hHA (g x) : |H g x| ≤ A+‖f.f‖ :=
    (abs_add_le _ _).trans (add_le_add (hhA x) (f.f.norm_coe_le_norm _))
  have he (r : ℕ) (i : Fin r) : Measurable
      (fun p : (Fin (m+1)→ℝ)×(Fin r→S) => b p.1 (p.2 i)) :=
    hb.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hFm (i) : Measurable (Function.uncurry (F i)) :=
    (f.d1.measurable.comp (he n j)).mul ((hw i).comp measurable_snd)
  have hUm (i) : Measurable (Function.uncurry (U i)) := by
    exact (((Finset.measurable_sum _ fun l _ => (f.d1.measurable.comp (he n l)).mul
      ((hv i).comp ((measurable_pi_apply l).comp measurable_snd))).mul
      (f.d1.measurable.comp (he n j))).add ((f.d2.measurable.comp (he n j)).mul
      ((hv i).comp ((measurable_pi_apply j).comp measurable_snd)))).mul ((hw i).comp measurable_snd)
  have hVm (i) : Measurable (Function.uncurry (V i)) := by
    exact ((f.d1.measurable.comp (he (n+1) 0)).mul
      ((hv i).comp ((measurable_pi_apply 0).comp measurable_snd))).mul
      ((f.d1.measurable.comp (he (n+1) j.succ)).mul
        ((hw i).comp ((Measurable.of_eval fun index : Fin n => measurable_pi_apply index.succ).comp measurable_snd)))
  have hFB (i g x) : |F i g x| ≤ ‖f.d1‖*D := by
    dsimp [F]; rw [abs_mul]
    exact mul_le_mul (f.d1.norm_coe_le_norm _) (hwD i x) (abs_nonneg _) (norm_nonneg _)
  have hsB (i g) (x : Fin n→S) : |∑ l, f.d1 (b g (x l))*v i (x l)| ≤ n*(‖f.d1‖*C) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _ : Fin n, ‖f.d1‖*C := Finset.sum_le_sum fun l _ => by
        rw [abs_mul]; exact mul_le_mul (f.d1.norm_coe_le_norm _) (hvC i _) (abs_nonneg _) (norm_nonneg _)
      _ = _ := by simp
  have hUB (i g x) : |U i g x| ≤ ((n:ℝ)*(‖f.d1‖*C)*‖f.d1‖+‖f.d2‖*C)*D := by
    dsimp only [U]; rw [abs_mul]
    apply mul_le_mul _ (hwD i x) (abs_nonneg _) (by positivity)
    apply (abs_add_le _ _).trans
    apply add_le_add
    · rw [abs_mul]; exact mul_le_mul (hsB i g x) (f.d1.norm_coe_le_norm _) (abs_nonneg _) (by positivity)
    · rw [abs_mul]; exact mul_le_mul (f.d2.norm_coe_le_norm _) (hvC i _) (abs_nonneg _) (norm_nonneg _)
  have hVB (i g x) : |V i g x| ≤ (‖f.d1‖*C)*(‖f.d1‖*D) := by
    dsimp only [V]; rw [abs_mul,abs_mul,abs_mul]
    exact mul_le_mul (mul_le_mul (f.d1.norm_coe_le_norm _) (hvC i _) (abs_nonneg _) (norm_nonneg _))
      (mul_le_mul (f.d1.norm_coe_le_norm _) (hwD i _) (abs_nonneg _) (norm_nonneg _)) (by positivity) (by positivity)
  have hiU (i) : Integrable (fun g => gibbsReplicaMean μ (H g) n (U i g)) γ := by
    apply Integrable.of_bound (replicaMean_varying_measurable μ hH (hUm i)).aestronglyMeasurable
      (((n:ℝ)*(‖f.d1‖*C)*‖f.d1‖+‖f.d2‖*C)*D)
    exact ae_of_all _ fun g => by
      simpa only [Real.norm_eq_abs] using replicaMean_bound μ hH.of_uncurry_left (hUm i).of_uncurry_left
        (by positivity) (by positivity) (hHA g) (hUB i g)
  have hiV (i) : Integrable (fun g => gibbsReplicaMean μ (H g) (n+1) (V i g)) γ := by
    apply Integrable.of_bound (replicaMean_varying_measurable μ hH (hVm i)).aestronglyMeasurable
      ((‖f.d1‖*C)*(‖f.d1‖*D))
    exact ae_of_all _ fun g => by
      simpa only [Real.norm_eq_abs] using replicaMean_bound μ hH.of_uncurry_left (hVm i).of_uncurry_left
        (by positivity) (by positivity) (hHA g) (hVB i g)
  have hiF (i) : Integrable (fun g => g i*gibbsReplicaMean μ (H g) n (F i g)) γ := by
    have hg : Integrable (fun g : Fin (m+1)→ℝ => g i) γ :=
      ((measurePreserving_eval (fun _ : Fin (m+1) => gaussianReal 0 1) i).integrable_comp
        measurable_id.aestronglyMeasurable).mpr
        ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num))
    exact hg.mul_bdd (replicaMean_varying_measurable μ hH (hFm i)).aestronglyMeasurable
      (ae_of_all _ fun g => by
        simpa only [Real.norm_eq_abs] using replicaMean_bound μ hH.of_uncurry_left (hFm i).of_uncurry_left
          (by positivity) (by positivity) (hHA g) (hFB i g))
  have hl (g) : gibbsReplicaMean μ (H g) n (fun x => f.d1 (b g (x j))*(∑ i, g i*w i x)) =
      ∑ i, g i*gibbsReplicaMean μ (H g) n (F i g) := by
    rw [show (fun x => f.d1 (b g (x j))*(∑ i, g i*w i x)) = (fun x => ∑ i, g i*F i g x) by
      funext x; simp only [Finset.mul_sum,F]; apply Finset.sum_congr rfl; intros; ring]
    rw [replicaMean_sum μ Finset.univ hH.of_uncurry_left (fun i _ => (hFm i).of_uncurry_left.const_mul (g i))
      (by positivity) (hHA g) (D := fun i => |g i| *(‖f.d1‖*D)) (fun i _ x => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFB i g x) (abs_nonneg _))]
    simp_rw [replicaMean_const_mul]
  have hr (g) : (∑ i, (gibbsReplicaMean μ (H g) n (U i g)-n*gibbsReplicaMean μ (H g) (n+1) (V i g))) =
      gibbsReplicaMean μ (H g) n (fun x =>
        (∑ l, f.d1 (b g (x l))*f.d1 (b g (x j))*(∑ i, w i x*v i (x l)))+
        f.d2 (b g (x j))*(∑ i, w i x*v i (x j))) -
      n*gibbsReplicaMean μ (H g) (n+1) (fun x =>
        f.d1 (b g (x 0))*f.d1 (b g (x j.succ))*(∑ i, w i (fun l => x l.succ)*v i (x 0))) := by
    rw [Finset.sum_sub_distrib,←Finset.mul_sum,
      ←replicaMean_sum μ Finset.univ hH.of_uncurry_left (fun i _ => (hUm i).of_uncurry_left)
        (by positivity) (hHA g) (fun i _ => hUB i g),
      ←replicaMean_sum μ Finset.univ hH.of_uncurry_left (fun i _ => (hVm i).of_uncurry_left)
        (by positivity) (hHA g) (fun i _ => hVB i g)]
    congr 1
    · congr 1; funext x
      simp only [U,add_mul,Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1 <;> (apply Finset.sum_congr rfl; intro i _)
      · apply Finset.sum_congr rfl; intros; ring
      · ring
    · congr 1; congr 1; funext x
      simp only [V,Finset.mul_sum]
      apply Finset.sum_congr rfl; intros; ring
  calc
    _ = ∫ g, ∑ i, g i*gibbsReplicaMean μ (H g) n (F i g) ∂γ := integral_congr_ae (ae_of_all _ hl)
    _ = _ := by
      rw [integral_finsetSum _ fun i _ => hiF i]
      simp_rw [show ∀ i, (∫ g, g i*gibbsReplicaMean μ (H g) n (F i g) ∂γ) =
          ∫ g, gibbsReplicaMean μ (H g) n (U i g)-n*gibbsReplicaMean μ (H g) (n+1) (V i g) ∂γ
        from fun i => nonlinear_pattern_replica_coordinate_ibp μ i j f hv hh (hw i) hA hC hD hhA hvC (hwD i)]
      rw [←integral_finsetSum Finset.univ (f := fun i g =>
        gibbsReplicaMean μ (H g) n (U i g)-n*gibbsReplicaMean μ (H g) (n+1) (V i g))
        (fun i _ => (hiU i).sub ((hiV i).const_mul n))]
      exact integral_congr_ae (ae_of_all _ hr)
end SphericalPerceptronFreeEnergy
end

end OAI
