import Mathlib
import OAI.Probability.Perceptron.Variational.GaussianCovarianceDerivative

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

variable {I : Type} [Fintype I] [DecidableEq I] {S : Type} [MeasurableSpace S]
variable (n : ℕ)

omit [MeasurableSpace S] in
theorem indexedHamiltonian_integral_covariance_addition
    (W : S×IndexedLeaf n→ℝ) (V : S→EuclideanSpace ℝ I)
    (Ψ : (S×IndexedLeaf n→ℝ)→ℝ)
    (hΨ : Measurable (fun g => Ψ (sharedMarksHamiltonian n W V g)))
    (B C D : Fin (n+1)→I→ℝ) (h : ∀ l i, D l i^2=B l i^2+C l i^2) :
    (∫ g, Ψ (countableGaussianHamiltonian W (indexedGaussianRow n D V)
      (indexedGaussianRowLength (I := I) n) g) ∂countableGaussianLaw) =
    ∫ g, Ψ (countableGaussianHamiltonian W (indexedGaussianRow n (fun l => Sum.elim (B l) (C l))
      (fun s => WithLp.toLp 2 (Sum.elim (fun i => V s i) (fun i => V s i))))
      (indexedGaussianRowLength (I := I ⊕ I) n) g) ∂countableGaussianLaw := by
  let F := fun g : SharedVertex n→EuclideanSpace ℝ I => Ψ (sharedMarksHamiltonian n W V g)
  have hF : Measurable F := hΨ
  let b := fun g v => gaussianRows (doubledGaussianRows (B (indexedSharedVertexDepth n v)) (C (indexedSharedVertexDepth n v)))
    (countableGaussianVectors g v)
  let d := fun g v => gaussianRows (diagonalGaussianRows (D (indexedSharedVertexDepth n v)))
    (countableGaussianVectors g v)
  have hb : Measurable b := by
    apply Measurable.of_eval
    intro v
    exact (gaussianRows (doubledGaussianRows (B (indexedSharedVertexDepth n v)) (C (indexedSharedVertexDepth n v)))).measurable.comp ((measurable_pi_apply v).comp countableGaussianVectors_measurable)
  have hd : Measurable d := by
    apply Measurable.of_eval
    intro v
    exact (gaussianRows (diagonalGaussianRows (D (indexedSharedVertexDepth n v)))).measurable.comp ((measurable_pi_apply v).comp countableGaussianVectors_measurable)
  have he := countableGaussian_covariance_addition_law
    (fun v => B (indexedSharedVertexDepth n v)) (fun v => C (indexedSharedVertexDepth n v))
    (fun v => D (indexedSharedVertexDepth n v)) (fun v => h (indexedSharedVertexDepth n v))
  have hi : (∫ g, F (d g) ∂countableGaussianLaw) = ∫ g, F (b g) ∂countableGaussianLaw := by
    rw [← integral_map hd.aemeasurable hF.aestronglyMeasurable,
      ← integral_map hb.aemeasurable hF.aestronglyMeasurable,he]
  have hf (g) : sharedMarksHamiltonian n W V (d g) =
      countableGaussianHamiltonian W (indexedGaussianRow n D V) (indexedGaussianRowLength (I := I) n) g :=
    funext (sharedMarks_diagonal_eq n W V D g)
  have hg (g) : sharedMarksHamiltonian n W V (b g) =
      countableGaussianHamiltonian W (indexedGaussianRow n (fun l => Sum.elim (B l) (C l))
      (fun s => WithLp.toLp 2 (Sum.elim (fun i => V s i) (fun i => V s i))))
      (indexedGaussianRowLength (I := I ⊕ I) n) g :=
    funext (sharedMarks_doubled_eq n W V B C g)
  change _ = _ at hi
  simp only [F,hf,hg] at hi
  exact hi

lemma indexedReplicaMean_covariance_addition (μ : Measure (S×IndexedLeaf n)) [IsProbabilityMeasure μ]
    {W : S×IndexedLeaf n→ℝ} {V : S→EuclideanSpace ℝ I}
    (hW : Measurable W) (hV : Measurable V) (r : ℕ)
    {G : (Fin r→S×IndexedLeaf n)→ℝ} (hG : Measurable G)
    (B C D : Fin (n+1)→I→ℝ) (h : ∀ l i, D l i^2=B l i^2+C l i^2) :
    (∫ g, gibbsReplicaMean μ (countableGaussianHamiltonian W (indexedGaussianRow n D V)
      (indexedGaussianRowLength (I := I) n) g) r G ∂countableGaussianLaw) =
    ∫ g, gibbsReplicaMean μ (countableGaussianHamiltonian W (indexedGaussianRow n (fun l => Sum.elim (B l) (C l))
      (fun s => WithLp.toLp 2 (Sum.elim (fun i => V s i) (fun i => V s i))))
      (indexedGaussianRowLength (I := I ⊕ I) n) g) r G ∂countableGaussianLaw := by
  exact indexedHamiltonian_integral_covariance_addition n W V (fun H => gibbsReplicaMean μ H r G)
    (kernel_replicaMean_measurable (Kernel.const _ μ) (sharedMarksHamiltonian_measurable n hW hV)
      (hG.comp measurable_snd)) B C D h

lemma indexedTiltMean_covariance_addition (μ : Measure (S×IndexedLeaf n)) [IsProbabilityMeasure μ]
    {W : S×IndexedLeaf n→ℝ} {V : S→EuclideanSpace ℝ I}
    (hW : Measurable W) (hV : Measurable V) {G : S×IndexedLeaf n→ℝ} (hG : Measurable G)
    (B C D : Fin (n+1)→I→ℝ) (h : ∀ l i, D l i^2=B l i^2+C l i^2) :
    (∫ g, tiltMean μ (countableGaussianHamiltonian W (indexedGaussianRow n D V)
      (indexedGaussianRowLength (I := I) n) g) G 1 ∂countableGaussianLaw) =
    ∫ g, tiltMean μ (countableGaussianHamiltonian W (indexedGaussianRow n (fun l => Sum.elim (B l) (C l))
      (fun s => WithLp.toLp 2 (Sum.elim (fun i => V s i) (fun i => V s i))))
      (indexedGaussianRowLength (I := I ⊕ I) n) g) G 1 ∂countableGaussianLaw := by
  exact indexedHamiltonian_integral_covariance_addition n W V (fun H => tiltMean μ H G 1)
    (kernel_tiltMean_measurable (Kernel.const _ μ) (sharedMarksHamiltonian_measurable n hW hV)
      (hG.comp measurable_snd)) B C D h


omit [DecidableEq I] [MeasurableSpace S] in
lemma indexedGaussianRow_right_covariance (C : Fin (n+1)→I→ℝ) (V : S→EuclideanSpace ℝ I)
    (x y : S×IndexedLeaf n) :
    countableGaussianCovariance
      (indexedGaussianRow n (rightCoefficients n C) (duplicateFeature V))
      (indexedGaussianRow n (rightCoefficients n C) (duplicateFeature V))
      (indexedGaussianRowLength (I := I ⊕ I) n) x y =
    countableGaussianCovariance (indexedGaussianRow n C V) (indexedGaussianRow n C V)
      (indexedGaussianRowLength (I := I) n) x y := by
  rw [indexedGaussianRow_covariance,indexedGaussianRow_covariance,Fintype.sum_sum_type]
  simp [rightCoefficients,duplicateFeature]

def indexedResponse (μ : Measure (S×IndexedLeaf n))
    (K : (S×IndexedLeaf n)→(S×IndexedLeaf n)→ℝ) (H : S×IndexedLeaf n→ℝ) : ℝ :=
  tiltMean μ H (fun x => K x x) 1 - gibbsReplicaMean μ H 2 (fun x => K (x 1) (x 0))

omit [DecidableEq I] in
lemma indexedResponse_measurable (μ : Measure (S×IndexedLeaf n)) [IsProbabilityMeasure μ]
    {W : S×IndexedLeaf n→ℝ} {V : S→EuclideanSpace ℝ I}
    (hW : Measurable W) (hV : Measurable V)
    {K : (S×IndexedLeaf n)→(S×IndexedLeaf n)→ℝ} (hK : Measurable (Function.uncurry K)) :
    Measurable (fun g => indexedResponse n μ K (sharedMarksHamiltonian n W V g)) := by
  have hKd : Measurable (fun x : S×IndexedLeaf n => K x x) :=
    hK.comp (measurable_id.prodMk measurable_id)
  have hpair : Measurable (fun x : Fin 2→S×IndexedLeaf n => (x 1,x 0)) :=
    (measurable_pi_apply 1).prodMk (measurable_pi_apply 0)
  have hKp : Measurable (fun x : Fin 2→S×IndexedLeaf n => K (x 1) (x 0)) := hK.comp hpair
  exact (kernel_tiltMean_measurable (Kernel.const _ μ)
    (H := sharedMarksHamiltonian n W V) (Y := fun _ x => K x x)
    (sharedMarksHamiltonian_measurable n hW hV) (hKd.comp measurable_snd)).sub
    (kernel_replicaMean_measurable (Kernel.const _ μ)
    (H := sharedMarksHamiltonian n W V) (G := fun _ x => K (x 1) (x 0))
    (sharedMarksHamiltonian_measurable n hW hV) (hKp.comp measurable_snd))

lemma indexedResponse_transport (μ : Measure (S×IndexedLeaf n)) [IsProbabilityMeasure μ]
    {W : S×IndexedLeaf n→ℝ} {V : S→EuclideanSpace ℝ I}
    (hW : Measurable W) (hV : Measurable V)
    {K : (S×IndexedLeaf n)→(S×IndexedLeaf n)→ℝ} (hK : Measurable (Function.uncurry K))
    (B : Fin (n+1)→I→ℝ) :
    (∫ g, indexedResponse n μ K (countableGaussianHamiltonian W
      (indexedGaussianRow n (leftCoefficients n B) (duplicateFeature V))
      (indexedGaussianRowLength (I := I ⊕ I) n) g) ∂countableGaussianLaw) =
      ∫ g, indexedResponse n μ K (countableGaussianHamiltonian W
      (indexedGaussianRow n B V) (indexedGaussianRowLength (I := I) n) g) ∂countableGaussianLaw := by
  exact (indexedHamiltonian_integral_covariance_addition n W V (indexedResponse n μ K)
    (indexedResponse_measurable n μ hW hV hK) B (fun _ _ => 0) B (fun l i => by simp)).symm

theorem indexedGaussianMean_right_response (μ : Measure (S×IndexedLeaf n)) [IsProbabilityMeasure μ]
    {W : S×IndexedLeaf n→ℝ} {V : S→EuclideanSpace ℝ I}
    (hW : Measurable W) (hV : Measurable V) {A D : ℝ} (hD0 : 0 ≤ D)
    (hA : ∀ x, |W x| ≤ A) (hD : ∀ x, (∑ i, V x i^2) ≤ D)
    (B C : Fin (n+1)→I→ℝ) (Q : ℝ→Fin (n+1)→I→ℝ)
    (hQ : ∀ t, 0 ≤ t → ∀ l i, Q t l i^2=B l i^2+t*C l i^2) :
    let v := indexedGaussianRow n B V
    let w := indexedGaussianRow n C V
    let L := indexedGaussianRowLength (I := I) (S := S) n
    HasDerivWithinAt (fun t => indexedGaussianMean n μ W V (Q t))
      ((∫ g, indexedResponse n μ (countableGaussianCovariance w w L)
        (countableGaussianHamiltonian W v L g) ∂countableGaussianLaw)/2) (Ici 0) 0 := by
  let w := indexedGaussianRow n C V
  let L := indexedGaussianRowLength (I := I) (S := S) n
  have hK : Measurable (Function.uncurry (countableGaussianCovariance w w L)) :=
    countableGaussianCovariance_measurable (indexedGaussianRow_measurable n C hV)
      (indexedGaussianRow_measurable n C hV) (indexedGaussianRowLength_measurable n)
  have hd := indexedGaussianMean_right_derivative n μ hW hV hD0 hA hD B C Q hQ
  dsimp only at hd ⊢
  simp only [indexedGaussianRow_right_covariance] at hd
  change HasDerivWithinAt _ ((∫ g, indexedResponse n μ (countableGaussianCovariance w w L)
    (countableGaussianHamiltonian W (indexedGaussianRow n (leftCoefficients n B) (duplicateFeature V))
    (indexedGaussianRowLength (I := I ⊕ I) n) g) ∂countableGaussianLaw)/2) _ _ at hd
  rw [indexedResponse_transport n μ hW hV hK B] at hd
  exact hd

end SphericalPerceptronFreeEnergy
end

end OAI
