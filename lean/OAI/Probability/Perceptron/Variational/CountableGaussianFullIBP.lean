import Mathlib
import OAI.Probability.Perceptron.Interpolation.AnnealedReplicaConvergence
import OAI.Probability.Perceptron.Variational.GaussianGibbsEnergy

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma countableGaussian_replica_full_ibp (n : ℕ) (j : Fin n)
    {W : S → ℝ} {v w : ℕ → S → ℝ} {L : S → ℕ} {G : (Fin n → S) → ℝ}
    (hW : Measurable W) (hv : ∀ i, Measurable (v i)) (hw : ∀ i, Measurable (w i))
    (hL : Measurable L) (hG : Measurable G) {A D E B : ℝ}
    (hA : ∀ x, |W x| ≤ A) (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D)
    (hE : ∀ x, (∑ i : Fin (L x), w i.val x^2) ≤ E)
    (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    let H := countableGaussianHamiltonian W v L
    (∫ g, gibbsReplicaMean μ (H g) n (fun x => countableGaussianField w L g (x j)*G x)
      ∂countableGaussianLaw) =
    ∫ g, gibbsReplicaMean μ (H g) n (fun x => G x*∑ l, countableGaussianCovariance v w L (x j) (x l)) -
      n*gibbsReplicaMean μ (H g) (n+1)
        (fun x => G (fun l => x l.succ)*countableGaussianCovariance v w L (x j.succ) (x 0)) ∂countableGaussianLaw := by
  dsimp only
  let H := countableGaussianHamiltonian W v L
  let C := |(D+E)/2|
  have hC : 0 ≤ C := abs_nonneg _
  have hHm : Measurable (Function.uncurry H) := countableGaussianHamiltonian_measurable hW hv hL
  have he : ∀ᵐ g ∂countableGaussianLaw, Integrable (fun x => Real.exp (H g x)) μ := by
    simpa only [one_mul] using (countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD 1).prod_left_ae
  let K := gaussianPrefixCovariance v w L
  let KFull := countableGaussianCovariance v w L
  have hKm (m) : Measurable (Function.uncurry (K m)) := gaussianPrefixCovariance_measurable hv hw hL m
  have hKFullm : Measurable (Function.uncurry KFull) := countableGaussianCovariance_measurable hv hw hL
  have hKb (m x y) : |K m x y| ≤ C := (gaussianPrefixCovariance_bound v w L hD hE m x y).trans (le_abs_self _)
  have hKFullb (x y) : |KFull x y| ≤ C := hKb (L x) x y
  have hKt (x y) : Tendsto (fun m => K m x y) atTop (nhds (KFull x y)) :=
    tendsto_const_nhds.congr' ((gaussianPrefixCovariance_eventually_eq v w L x y).mono fun _ h => h.symm)
  let U (m) (x : Fin n → S) := G x*∑ l, K m (x j) (x l)
  let UFull (x : Fin n → S) := G x*∑ l, KFull (x j) (x l)
  let V (m) (x : Fin (n+1) → S) := G (fun l => x l.succ)*K m (x j.succ) (x 0)
  let VFull (x : Fin (n+1) → S) := G (fun l => x l.succ)*KFull (x j.succ) (x 0)
  have hPair (a b : Fin n) : Measurable (fun x : Fin n → S => (x a,x b)) :=
    (measurable_pi_apply a).prodMk (measurable_pi_apply b)
  have hUm (m) : Measurable (U m) := hG.mul
    (Finset.measurable_sum Finset.univ fun (l : Fin n) _ => (hKm m).comp (hPair j l))
  have hUFullm : Measurable UFull := hG.mul
    (Finset.measurable_sum Finset.univ fun (l : Fin n) _ => hKFullm.comp (hPair j l))
  have hPairS : Measurable (fun x : Fin (n+1) → S => (x j.succ,x 0)) :=
    (measurable_pi_apply j.succ).prodMk (measurable_pi_apply 0)
  have hVm (m) : Measurable (V m) :=
    (hG.comp (Measurable.of_eval fun index : Fin n => measurable_pi_apply index.succ)).mul
      ((hKm m).comp hPairS)
  have hVFullm : Measurable VFull :=
    (hG.comp (Measurable.of_eval fun index : Fin n => measurable_pi_apply index.succ)).mul
      (hKFullm.comp hPairS)
  have hsum (k : S → S → ℝ) (hk : ∀ x y, |k x y| ≤ C) (x : Fin n → S) :
      |G x*∑ l, k (x j) (x l)| ≤ B*((n:ℝ)*C) := by
    rw [abs_mul]
    apply mul_le_mul (hGB x) _ (abs_nonneg _) hB
    calc
      _ ≤ ∑ l : Fin n, |k (x j) (x l)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l : Fin n, C := Finset.sum_le_sum fun l _ => hk _ _
      _ = _ := by simp
  have hUB (m x) : |U m x| ≤ B*((n:ℝ)*C) := hsum (K m) (hKb m) x
  have hUFullB (x) : |UFull x| ≤ B*((n:ℝ)*C) := hsum KFull hKFullb x
  have hVB (m x) : |V m x| ≤ B*C := by
    exact (abs_mul _ _).trans_le (mul_le_mul (hGB _) (hKb m _ _) (abs_nonneg _) hB)
  have hVFullB (x) : |VFull x| ≤ B*C := by
    exact (abs_mul _ _).trans_le (mul_le_mul (hGB _) (hKFullb _ _) (abs_nonneg _) hB)
  have hUt (x) : Tendsto (fun m => U m x) atTop (nhds (UFull x)) :=
    (tendsto_finsetSum _ (fun index _ => hKt (x j) (x index))).const_mul (G x)
  have hVt (x) : Tendsto (fun m => V m x) atTop (nhds (VFull x)) :=
    (hKt (x j.succ) (x 0)).const_mul (G (fun l => x l.succ))
  have hUi (m) := annealedReplica_bounded_integrable μ countableGaussianLaw hHm (hUm m) (by positivity) (hUB m)
  have hVi (m) := annealedReplica_bounded_integrable μ countableGaussianLaw hHm (hVm m) (by positivity) (hVB m)
  have hUFulli := annealedReplica_bounded_integrable μ countableGaussianLaw hHm hUFullm (by positivity) hUFullB
  have hVFulli := annealedReplica_bounded_integrable μ countableGaussianLaw hHm hVFullm (by positivity) hVFullB
  have hUL := annealedReplica_bounded_tendsto μ countableGaussianLaw hHm hUm hUFullm (by positivity) hUB hUt he
  have hVL := annealedReplica_bounded_tendsto μ countableGaussianLaw hHm hVm hVFullm (by positivity) hVB hVt he
  have hR := hUL.sub (hVL.const_mul (n:ℝ))
  have hL' := gaussianEnergy_replica_prefix_tendsto μ hW hv hw hL hA hD hE j hG hB hGB
  have heq (m) : (∫ g, gibbsReplicaMean μ (H g) n
      (fun x => truncatedCountableGaussianField w L m g (x j)*G x) ∂countableGaussianLaw) =
      (∫ g, gibbsReplicaMean μ (H g) n (U m) ∂countableGaussianLaw)-
        (n:ℝ)*(∫ g, gibbsReplicaMean μ (H g) (n+1) (V m) ∂countableGaussianLaw) := by
    rw [gaussianReplica_prefix_ibp μ m n j hW hv hw hL hG hA hD hE hB hGB]
    exact (integral_sub (hUi m) ((hVi m).const_mul n)).trans (by rw [integral_const_mul])
  have hlim := tendsto_nhds_unique hL' (hR.congr (fun m => (heq m).symm))
  exact hlim.trans ((integral_sub hUFulli (hVFulli.const_mul n)).trans (by rw [integral_const_mul])).symm

end SphericalPerceptronFreeEnergy
end

end OAI
