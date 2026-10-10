import Mathlib
import OAI.Probability.Perceptron.Interpolation.TiltReplicaCoordinate

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

def gibbsReplicaMean (H : S → ℝ) (n : ℕ) (G : (Fin n → S) → ℝ) : ℝ :=
  tiltMean (Measure.pi fun _ : Fin n => μ) (replicaPotential H n) G 1

def fieldCovariance (m : ℕ) (v : Fin m → S → ℝ) (x y : S) : ℝ :=
  ∑ i, v i x * v i y

lemma replicaMean_measurable {Ω : Type*} [MeasurableSpace Ω] {H : Ω → S → ℝ}
    {n : ℕ} {G : (Fin n → S) → ℝ} (hH : Measurable (Function.uncurry H))
    (hG : Measurable G) : Measurable (fun ω => gibbsReplicaMean μ (H ω) n G) := by
  apply measurable_tiltMean _ _ hG
  change Measurable (fun p : Ω×(Fin n → S) => ∑ i, H p.1 (p.2 i))
  exact Finset.measurable_sum _ fun i _ => hH.comp
    (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

lemma replicaMean_bound {H : S → ℝ} {n : ℕ} {G : (Fin n → S) → ℝ}
    (hH : Measurable H) (hG : Measurable G) {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hHA : ∀ x, |H x| ≤ A) (hGD : ∀ x, |G x| ≤ D) : |gibbsReplicaMean μ H n G| ≤ D :=
  tilt_mean_bound _ (replicaPotential_measurable hH n) hG
    (mul_nonneg (Nat.cast_nonneg n) hA) hD (replicaPotential_bound hHA n) hGD 1

lemma replicaMean_sum {ι : Type*} (t : Finset ι) {H : S → ℝ} {n : ℕ}
    {G : ι → (Fin n → S) → ℝ} (hH : Measurable H)
    (hG : ∀ i ∈ t, Measurable (G i)) {A : ℝ} {D : ι → ℝ}
    (hA : 0 ≤ A) (hHA : ∀ x, |H x| ≤ A)
    (hGD : ∀ i ∈ t, ∀ x, |G i x| ≤ D i) :
    gibbsReplicaMean μ H n (fun x => ∑ i ∈ t, G i x) = ∑ i ∈ t, gibbsReplicaMean μ H n (G i) :=
  tilt_mean_sum _ t (replicaPotential_measurable hH n) hG
    (mul_nonneg (Nat.cast_nonneg n) hA) (replicaPotential_bound hHA n) hGD 1

omit [IsProbabilityMeasure μ] in
lemma replicaMean_const_mul {H : S → ℝ} {n : ℕ} {G : (Fin n → S) → ℝ} (c : ℝ) :
    gibbsReplicaMean μ H n (fun x => c*G x) = c*gibbsReplicaMean μ H n G :=
  tilt_mean_mulObservable _ c 1

lemma gaussian_replica_field_ibp (m n : ℕ) (j : Fin n)
    {v : Fin (m+1) → S → ℝ} {h : S → ℝ} {G : (Fin n → S) → ℝ}
    (hv : ∀ i, Measurable (v i)) (hh : Measurable h) (hG : Measurable G)
    {C A D : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hvC : ∀ i x, |v i x| ≤ C) (hhA : ∀ x, |h x| ≤ A) (hGD : ∀ x, |G x| ≤ D)
    (s : ℝ) :
    let H := fun (g : Fin (m+1) → ℝ) (x : S) => h x+s*gaussianField (m+1) v g x
    (∫ g, gibbsReplicaMean μ (H g) n (fun x => gaussianField (m+1) v g (x j)*G x)
      ∂Measure.pi (fun _ => gaussianReal 0 1)) =
    s * ∫ g,
      gibbsReplicaMean μ (H g) n (fun x => G x * ∑ l, fieldCovariance (m+1) v (x j) (x l)) -
      n * gibbsReplicaMean μ (H g) (n+1)
        (fun x => G (fun l => x l.succ)*fieldCovariance (m+1) v (x j.succ) (x 0))
      ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  dsimp only
  let γ := Measure.pi (fun _ : Fin (m+1) => gaussianReal 0 1)
  let H := fun (g : Fin (m+1) → ℝ) (x : S) => h x+s*gaussianField (m+1) v g x
  have hH : Measurable (Function.uncurry H) := hh.comp measurable_snd |>.add
    ((gaussianField_measurable hv).const_mul s)
  let B := fun (g : Fin (m+1) → ℝ) => A + |s| * ((∑ i, |g i|) * C)
  have hB (g) : 0 ≤ B g := by dsimp [B]; positivity
  have hb (g) (x : S) : |H g x| ≤ B g := by
    exact (abs_add_le _ _).trans (add_le_add (hhA x) (by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (gaussianField_bound hvC g x) (abs_nonneg s)))
  have hhg (g) : Measurable (H g) := hH.comp (measurable_const.prodMk measurable_id)
  let F := fun i (x : Fin n → S) => v i (x j)*G x
  let U := fun i (x : Fin n → S) => replicaPotential (v i) n x * F i x
  let V := fun i (x : Fin (n+1) → S) => v i (x 0) * (v i (x j.succ)*G (fun l => x l.succ))
  have hFm (i) : Measurable (F i) := ((hv i).comp (measurable_pi_apply j)).mul hG
  have hUm (i) : Measurable (U i) := (replicaPotential_measurable (hv i) n).mul (hFm i)
  have hVm (i) : Measurable (V i) := by dsimp [V]; fun_prop
  have hFB (i) (x) : |F i x| ≤ C*D := by
    exact (abs_mul _ _).trans_le (mul_le_mul (hvC i _) (hGD _) (abs_nonneg _) hC)
  have hUB (i) (x) : |U i x| ≤ (n:ℝ)*C^2*D := by
    dsimp only [U]
    rw [abs_mul]
    have hh := mul_le_mul (replicaPotential_bound (hvC i) n x) (hFB i x)
      (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg n) hC)
    calc
      _ ≤ ((n:ℝ)*C)*(C*D) := hh
      _ = _ := by ring
  have hVB (i) (x) : |V i x| ≤ C^2*D := by
    dsimp only [V]
    rw [abs_mul,abs_mul]
    have hh := mul_le_mul (hvC i (x 0))
      (mul_le_mul (hvC i (x j.succ)) (hGD (fun l => x l.succ)) (abs_nonneg _) hC) (by positivity) hC
    calc
      _ ≤ C*(C*D) := hh
      _ = _ := by ring
  have hUi (i) : Integrable (fun g => gibbsReplicaMean μ (H g) n (U i)) γ := by
    apply Integrable.of_bound (replicaMean_measurable μ hH (hUm i)).aestronglyMeasurable
      ((n:ℝ)*C^2*D)
    exact ae_of_all _ fun g => by
      simpa only [Real.norm_eq_abs] using replicaMean_bound μ (hhg g) (hUm i) (hB g)
        (by positivity) (hb g) (hUB i)
  have hVi (i) : Integrable (fun g => gibbsReplicaMean μ (H g) (n+1) (V i)) γ := by
    apply Integrable.of_bound (replicaMean_measurable μ hH (hVm i)).aestronglyMeasurable (C^2*D)
    exact ae_of_all _ fun g => by
      simpa only [Real.norm_eq_abs] using replicaMean_bound μ (hhg g) (hVm i) (hB g)
        (by positivity) (hb g) (hVB i)
  have hFi (i) : Integrable (fun g => g i * gibbsReplicaMean μ (H g) n (F i)) γ := by
    have hg : Integrable (fun g : Fin (m+1) → ℝ => g i) γ := by
      exact ((measurePreserving_eval (fun _ : Fin (m+1) => gaussianReal 0 1) i).integrable_comp
        measurable_id.aestronglyMeasurable).mpr
        ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num))
    exact hg.mul_bdd (replicaMean_measurable μ hH (hFm i)).aestronglyMeasurable
      (ae_of_all _ fun g => by
        simpa only [Real.norm_eq_abs] using replicaMean_bound μ (hhg g) (hFm i) (hB g)
          (mul_nonneg hC hD) (hb g) (hFB i))
  have hleft (g) : gibbsReplicaMean μ (H g) n
      (fun x => gaussianField (m+1) v g (x j)*G x) =
        ∑ i, g i * gibbsReplicaMean μ (H g) n (F i) := by
    rw [show (fun x => gaussianField (m+1) v g (x j)*G x) =
      fun x => ∑ i, g i * F i x by funext x; simp only [gaussianField,Finset.sum_mul,F]; congr 1; funext i; ring]
    rw [replicaMean_sum μ Finset.univ (hhg g) (fun i _ => (hFm i).const_mul (g i))
      (hB g) (hb g) (D := fun i => |g i| * (C*D)) (fun i _ x => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFB i x) (abs_nonneg _))]
    simp_rw [replicaMean_const_mul]
  have hright (g) :
      (∑ i, (gibbsReplicaMean μ (H g) n (U i)-(n:ℝ)*gibbsReplicaMean μ (H g) (n+1) (V i))) =
      gibbsReplicaMean μ (H g) n (fun x => G x * ∑ l, fieldCovariance (m+1) v (x j) (x l)) -
      n * gibbsReplicaMean μ (H g) (n+1)
        (fun x => G (fun l => x l.succ)*fieldCovariance (m+1) v (x j.succ) (x 0)) := by
    rw [Finset.sum_sub_distrib,← Finset.mul_sum,
      ← replicaMean_sum μ Finset.univ (hhg g) (fun i _ => hUm i) (hB g) (hb g) (fun i _ => hUB i),
      ← replicaMean_sum μ Finset.univ (hhg g) (fun i _ => hVm i) (hB g) (hb g) (fun i _ => hVB i)]
    congr 1
    · congr 1; funext x
      dsimp [U,F,replicaPotential,fieldCovariance]
      simp only [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro i _
      ring
    · congr 1; congr 1; funext x
      simp only [V,fieldCovariance,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
  change (∫ g, gibbsReplicaMean μ (H g) n (fun x => gaussianField (m+1) v g (x j)*G x) ∂γ) = _
  simp_rw [hleft]
  rw [integral_finsetSum _ (fun i _ => hFi i)]
  simp_rw [show ∀ i, (∫ g, g i*gibbsReplicaMean μ (H g) n (F i) ∂γ) =
    s * ∫ g, gibbsReplicaMean μ (H g) n (U i)-(n:ℝ)*gibbsReplicaMean μ (H g) (n+1) (V i) ∂γ
    from fun i => gaussian_replica_coordinate_ibp μ m n i j hv hh hG hC hA hD hvC hhA hGD s]
  rw [← Finset.mul_sum]
  congr 1
  have hi : ∀ i ∈ (Finset.univ : Finset (Fin (m+1))), Integrable
      (fun g => gibbsReplicaMean μ (H g) n (U i)-(n:ℝ)*gibbsReplicaMean μ (H g) (n+1) (V i)) γ :=
    fun i _ => (hUi i).sub ((hVi i).const_mul n)
  rw [← integral_finsetSum Finset.univ hi]
  exact integral_congr_ae (ae_of_all _ hright)

end SphericalPerceptronFreeEnergy

end

end OAI
