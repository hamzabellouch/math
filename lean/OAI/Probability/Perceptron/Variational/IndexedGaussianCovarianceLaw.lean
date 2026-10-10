import Mathlib
import OAI.Probability.Perceptron.Variational.GaussianComparison

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
section
variable {I : Type} [Fintype I] [DecidableEq I]

def doubledGaussianRows (B C : I → ℝ) (i : I) : EuclideanSpace ℝ (I ⊕ I) :=
  B i • EuclideanSpace.basisFun (I ⊕ I) ℝ (Sum.inl i) +
    C i • EuclideanSpace.basisFun (I ⊕ I) ℝ (Sum.inr i)

def diagonalGaussianRows (D : I → ℝ) (i : I) : EuclideanSpace ℝ I :=
  D i • EuclideanSpace.basisFun I ℝ i

lemma doubledGaussianRows_gram (B C D : I → ℝ) (h : ∀ i, D i^2=B i^2+C i^2) :
    Matrix.gram ℝ (doubledGaussianRows B C) = Matrix.gram ℝ (diagonalGaussianRows D) := by
  ext i j
  change inner ℝ (doubledGaussianRows B C i) (doubledGaussianRows B C j) =
    inner ℝ (diagonalGaussianRows D i) (diagonalGaussianRows D j)
  simp only [doubledGaussianRows,diagonalGaussianRows,inner_add_left,inner_add_right,
    real_inner_smul_left,real_inner_smul_right,EuclideanSpace.basisFun_inner]
  by_cases hij : i=j
  · subst j; simp [← sq,h]
  · simp [hij]

lemma doubledGaussianRows_law (B C D : I → ℝ) (h : ∀ i, D i^2=B i^2+C i^2) :
    (stdGaussian (EuclideanSpace ℝ (I ⊕ I))).map (gaussianRows (doubledGaussianRows B C)) =
      (stdGaussian (EuclideanSpace ℝ I)).map (gaussianRows (diagonalGaussianRows D)) := by
  rw [gaussianRows_map_stdGaussian,gaussianRows_map_stdGaussian,doubledGaussianRows_gram B C D h]

omit [DecidableEq I] in
lemma doubledGaussianRows_apply (B C : I → ℝ) (g : EuclideanSpace ℝ (I ⊕ I)) (i : I) :
    gaussianRows (doubledGaussianRows B C) g i = B i*g (Sum.inl i)+C i*g (Sum.inr i) := by
  simp only [gaussianRows_apply,doubledGaussianRows,inner_add_left,real_inner_smul_left,
    EuclideanSpace.basisFun_inner]

omit [DecidableEq I] in
lemma diagonalGaussianRows_apply (D : I → ℝ) (g : EuclideanSpace ℝ I) (i : I) :
    gaussianRows (diagonalGaussianRows D) g i = D i*g i := by
  simp only [gaussianRows_apply,diagonalGaussianRows,real_inner_smul_left,EuclideanSpace.basisFun_inner]

end
variable {V I : Type} [Countable V] [Fintype I] [DecidableEq I]

theorem countableGaussian_covariance_addition_law (B C D : V → I → ℝ)
    (h : ∀ v i, D v i^2=B v i^2+C v i^2) :
    countableGaussianLaw.map (fun g v => gaussianRows (doubledGaussianRows (B v) (C v))
      (countableGaussianVectors (I := I ⊕ I) g v)) =
    countableGaussianLaw.map (fun g v => gaussianRows (diagonalGaussianRows (D v))
      (countableGaussianVectors (I := I) g v)) := by
  have hm : Measurable (fun f : V → EuclideanSpace ℝ (I ⊕ I) => fun v =>
      gaussianRows (doubledGaussianRows (B v) (C v)) (f v)) := by fun_prop
  have hn : Measurable (fun f : V → EuclideanSpace ℝ I => fun v =>
      gaussianRows (diagonalGaussianRows (D v)) (f v)) := by fun_prop
  rw [show (fun g v => gaussianRows (doubledGaussianRows (B v) (C v)) (countableGaussianVectors g v)) =
      (fun f v => gaussianRows (doubledGaussianRows (B v) (C v)) (f v)) ∘ countableGaussianVectors from rfl,
    ← Measure.map_map hm countableGaussianVectors_measurable,countableGaussianVectors_law,
    Measure.infinitePi_map_pi _ (fun v => (gaussianRows (doubledGaussianRows (B v) (C v))).measurable)]
  rw [show (fun g v => gaussianRows (diagonalGaussianRows (D v)) (countableGaussianVectors g v)) =
      (fun f v => gaussianRows (diagonalGaussianRows (D v)) (f v)) ∘ countableGaussianVectors from rfl,
    ← Measure.map_map hn countableGaussianVectors_measurable,countableGaussianVectors_law,
    Measure.infinitePi_map_pi _ (fun v => (gaussianRows (diagonalGaussianRows (D v))).measurable)]
  congr 1
  funext v
  exact doubledGaussianRows_law (B v) (C v) (D v) (h v)

variable {S : Type} [MeasurableSpace S]
variable (n : ℕ)

def sharedMarksHamiltonian (W : S×IndexedLeaf n→ℝ) (V : S→EuclideanSpace ℝ I)
    (g : SharedVertex n→EuclideanSpace ℝ I) (x : S×IndexedLeaf n) : ℝ :=
  W x + ∑ l : Fin (n+1), ∑ i : I, g (indexedLeafSharedVertex n x.2 l) i * V x.1 i

omit [DecidableEq I] in
lemma sharedMarksHamiltonian_measurable {W : S×IndexedLeaf n→ℝ} {V : S→EuclideanSpace ℝ I}
    (hW : Measurable W) (hV : Measurable V) :
    Measurable (Function.uncurry (sharedMarksHamiltonian n W V)) := by
  unfold Function.uncurry sharedMarksHamiltonian
  apply (hW.comp measurable_snd).add
  apply Finset.measurable_sum
  intro l hl
  apply Finset.measurable_sum
  intro i hi
  have he : Measurable (fun q : (SharedVertex n→EuclideanSpace ℝ I)×IndexedLeaf n =>
      q.1 (indexedLeafSharedVertex n q.2 l) i) := by
    apply measurable_from_prod_countable_left
    intro leaf
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).measurable.comp (measurable_pi_apply (indexedLeafSharedVertex n leaf l))
  exact (he.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).mul
    ((EuclideanSpace.proj i).measurable.comp (hV.comp (measurable_fst.comp measurable_snd)))

omit [MeasurableSpace S] [DecidableEq I] in
lemma sharedMarks_diagonal_eq (W : S×IndexedLeaf n→ℝ) (V : S→EuclideanSpace ℝ I)
    (B : Fin (n+1)→I→ℝ) (g : ℕ→ℝ) (x : S×IndexedLeaf n) :
    sharedMarksHamiltonian n W V (fun v => gaussianRows (diagonalGaussianRows (B (indexedSharedVertexDepth n v)))
      (countableGaussianVectors g v)) x =
    countableGaussianHamiltonian W (indexedGaussianRow n B V) (indexedGaussianRowLength (I := I) n) g x := by
  rw [countableGaussianHamiltonian,indexedGaussianRow_field]
  unfold sharedMarksHamiltonian
  simp only [indexedLeafSharedVertex_depth,diagonalGaussianRows_apply,countableGaussianVectors]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro i hi
  ring

omit [MeasurableSpace S] [DecidableEq I] in
lemma sharedMarks_doubled_eq (W : S×IndexedLeaf n→ℝ) (V : S→EuclideanSpace ℝ I)
    (B C : Fin (n+1)→I→ℝ) (g : ℕ→ℝ) (x : S×IndexedLeaf n) :
    sharedMarksHamiltonian n W V (fun v => gaussianRows (doubledGaussianRows
      (B (indexedSharedVertexDepth n v)) (C (indexedSharedVertexDepth n v)))
      (countableGaussianVectors g v)) x =
    countableGaussianHamiltonian W (indexedGaussianRow n (fun l => Sum.elim (B l) (C l))
      (fun s => WithLp.toLp 2 (Sum.elim (fun i => V s i) (fun i => V s i))))
      (indexedGaussianRowLength (I := I ⊕ I) n) g x := by
  rw [countableGaussianHamiltonian,indexedGaussianRow_field]
  unfold sharedMarksHamiltonian
  simp only [indexedLeafSharedVertex_depth,doubledGaussianRows_apply,countableGaussianVectors]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [Fintype.sum_sum_type,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Sum.elim_inl,Sum.elim_inr]
  ring

theorem indexedGaussianMean_covariance_addition (μ : Measure (S×IndexedLeaf n)) [IsFiniteMeasure μ]
    {W : S×IndexedLeaf n→ℝ} {V : S→EuclideanSpace ℝ I}
    (hW : Measurable W) (hV : Measurable V) (B C D : Fin (n+1)→I→ℝ)
    (h : ∀ l i, D l i^2=B l i^2+C l i^2) :
    indexedGaussianMean n μ W V D = indexedGaussianMean n μ W
      (fun s => WithLp.toLp 2 (Sum.elim (fun i => V s i) (fun i => V s i)))
      (fun l => Sum.elim (B l) (C l)) := by
  let F := fun g : SharedVertex n→EuclideanSpace ℝ I =>
    Real.log (tiltPartition μ (sharedMarksHamiltonian n W V g) 1)
  have hF : Measurable F := by
    exact (kernel_tiltPartition_measurable (Kernel.const _ μ)
      (sharedMarksHamiltonian_measurable n hW hV)).log
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
  unfold indexedGaussianMean
  change _ = _ at hi
  simp only [F,hf,hg] at hi
  exact hi

end SphericalPerceptronFreeEnergy
end

end OAI
