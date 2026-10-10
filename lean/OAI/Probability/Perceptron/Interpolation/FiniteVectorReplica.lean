import Mathlib
import OAI.Probability.Perceptron.Variational.IntegratedConvex

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy

lemma euclideanReplica_measurable_left {I : Type} {S : Type*} [Fintype I] [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (r : ℕ) (j : Fin r)
    {H : S→ℝ} {V W : S→EuclideanSpace ℝ I} {G : (Fin r→S)→ℝ}
    (hH : Measurable H) (hV : Measurable V) (hW : Measurable W) (hG : Measurable G) :
    Measurable (fun g => gibbsReplicaMean μ (fun x => H x+inner ℝ (V x) g) r
      (fun x => inner ℝ (W (x j)) g*G x)) := by
  have hh : Measurable (fun a : EuclideanSpace ℝ I × S => H a.2+inner ℝ (V a.2) a.1) :=
    (hH.comp measurable_snd).add ((hV.comp measurable_snd).inner measurable_fst)
  have hmj : Measurable (fun x : Fin r→S => W (x j)) := hW.comp (measurable_pi_apply j)
  have hl : Measurable (fun a : EuclideanSpace ℝ I × (Fin r→S) => inner ℝ (W (a.2 j)) a.1*G a.2) :=
    ((hmj.comp measurable_snd).inner measurable_fst).mul (hG.comp measurable_snd)
  exact kernel_replicaMean_measurable (Kernel.const (EuclideanSpace ℝ I) μ) hh hl

lemma euclideanReplica_measurable_right {I : Type} {S : Type*} [Fintype I] [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (r : ℕ) (j : Fin r)
    {H : S→ℝ} {V W : S→EuclideanSpace ℝ I} {G : (Fin r→S)→ℝ}
    (hH : Measurable H) (hV : Measurable V) (hW : Measurable W) (hG : Measurable G) :
    Measurable (fun g => gibbsReplicaMean μ (fun x => H x+inner ℝ (V x) g) r
      (fun x => G x*∑ l, inner ℝ (W (x j)) (V (x l))) -
      r*gibbsReplicaMean μ (fun x => H x+inner ℝ (V x) g) (r+1)
        (fun x => G (fun l => x l.succ)*inner ℝ (W (x j.succ)) (V (x 0)))) := by
  have hh : Measurable (fun a : EuclideanSpace ℝ I × S => H a.2+inner ℝ (V a.2) a.1) :=
    (hH.comp measurable_snd).add ((hV.comp measurable_snd).inner measurable_fst)
  have hsum : Measurable (fun x : Fin r→S => G x*∑ l, inner ℝ (W (x j)) (V (x l))) := by
    apply hG.mul
    exact Finset.measurable_sum _ fun l _ => (hW.comp (measurable_pi_apply j)).inner (hV.comp (measurable_pi_apply l))
  have hpair : Measurable (fun x : Fin (r+1)→S => G (fun l => x l.succ)*inner ℝ (W (x j.succ)) (V (x 0))) :=
    (hG.comp (Measurable.of_eval fun replica => measurable_pi_apply replica.succ)).mul
      ((hW.comp (measurable_pi_apply j.succ)).inner (hV.comp (measurable_pi_apply 0)))
  exact (kernel_replicaMean_measurable (Kernel.const (EuclideanSpace ℝ I) μ)
    (H := fun g x => H x+inner ℝ (V x) g)
    (G := fun _ x => G x*∑ l, inner ℝ (W (x j)) (V (x l))) hh
    (hsum.comp measurable_snd)).sub ((kernel_replicaMean_measurable (Kernel.const (EuclideanSpace ℝ I) μ)
      (H := fun g x => H x+inner ℝ (V x) g)
      (G := fun _ x => G (fun l => x l.succ)*inner ℝ (W (x j.succ)) (V (x 0))) hh
      (hpair.comp measurable_snd)).const_mul r)

lemma countableVector_replica_ibp {I : Type} {S : Type*} [Fintype I] [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (r : ℕ) (j : Fin r)
    {H : S→ℝ} {V W : S→EuclideanSpace ℝ I} {G : (Fin r→S)→ℝ}
    (hH : Measurable H) (hV : Measurable V) (hW : Measurable W) (hG : Measurable G)
    {A D E B : ℝ} (hA : ∀ x, |H x|≤A) (hD : ∀ x, ‖V x‖^2≤D)
    (hE : ∀ x, ‖W x‖^2≤E) (hB : 0≤B) (hGB : ∀ x, |G x|≤B) :
    (∫ g, gibbsReplicaMean μ (fun x => H x+inner ℝ (V x) (countableGaussianVector g)) r
      (fun x => inner ℝ (W (x j)) (countableGaussianVector g)*G x) ∂countableGaussianLaw) =
    ∫ g, gibbsReplicaMean μ (fun x => H x+inner ℝ (V x) (countableGaussianVector g)) r
      (fun x => G x*∑ l, inner ℝ (W (x j)) (V (x l))) -
      r*gibbsReplicaMean μ (fun x => H x+inner ℝ (V x) (countableGaussianVector g)) (r+1)
        (fun x => G (fun l => x l.succ)*inner ℝ (W (x j.succ)) (V (x 0)))
      ∂countableGaussianLaw := by
  have he := countableGaussian_replica_full_ibp μ r j hH
    (vectorGaussianRow_measurable hV) (vectorGaussianRow_measurable hW) measurable_const hG hA
    (fun x => (vectorGaussianRow_norm V x).trans_le (hD x))
    (fun x => (vectorGaussianRow_norm W x).trans_le (hE x)) hB hGB
  have hham (g) : countableGaussianHamiltonian H (vectorGaussianRow V)
      (fun _ => vectorGaussianLength I) g=fun x => H x+inner ℝ (V x) (countableGaussianVector g) := by
    funext x
    exact congrArg (fun y => H x+y) (vectorGaussianRow_field V g x)
  simp_rw [hham,vectorGaussianRow_field,vectorGaussianRow_covariance] at he
  exact he

lemma euclideanGaussian_replica_ibp {I : Type} {S : Type*} [Fintype I] [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (r : ℕ) (j : Fin r)
    {H : S→ℝ} {V W : S→EuclideanSpace ℝ I} {G : (Fin r→S)→ℝ}
    (hH : Measurable H) (hV : Measurable V) (hW : Measurable W) (hG : Measurable G)
    {A D E B : ℝ} (hA : ∀ x, |H x|≤A) (hD : ∀ x, ‖V x‖^2≤D)
    (hE : ∀ x, ‖W x‖^2≤E) (hB : 0≤B) (hGB : ∀ x, |G x|≤B) :
    (∫ g, gibbsReplicaMean μ (fun x => H x+inner ℝ (V x) g) r
      (fun x => inner ℝ (W (x j)) g*G x) ∂stdGaussian (EuclideanSpace ℝ I)) =
    ∫ g, gibbsReplicaMean μ (fun x => H x+inner ℝ (V x) g) r
      (fun x => G x*∑ l, inner ℝ (W (x j)) (V (x l))) -
      r*gibbsReplicaMean μ (fun x => H x+inner ℝ (V x) g) (r+1)
        (fun x => G (fun l => x l.succ)*inner ℝ (W (x j.succ)) (V (x 0)))
      ∂stdGaussian (EuclideanSpace ℝ I) := by
  have hleft := euclideanReplica_measurable_left μ r j hH hV hW hG
  have hright := euclideanReplica_measurable_right μ r j hH hV hW hG
  rw [← countableGaussianVector_law (I:=I),
    integral_map countableGaussianVector_measurable.aemeasurable hleft.aestronglyMeasurable,
    integral_map countableGaussianVector_measurable.aemeasurable hright.aestronglyMeasurable]
  exact countableVector_replica_ibp μ r j hH hV hW hG hA hD hE hB hGB

end SphericalPerceptronFreeEnergy
end

end OAI
