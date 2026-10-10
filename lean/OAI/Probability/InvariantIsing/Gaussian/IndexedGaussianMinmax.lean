import OAI.Probability.InvariantIsing.Gaussian.GaussianMinmaxComparison
import OAI.Probability.InvariantIsing.Core.FiniteMinmaxBasic
import OAI.Probability.InvariantIsing.Gaussian.IndexedGaussianIntegrability

namespace OAI

/-! Gordon comparison with an arbitrary finite Gaussian coordinate set. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {U V ι : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V] [Fintype ι]

lemma indexedGaussianMinmax_integrable (C : U × V → ι → ℝ) :
    Integrable (fun g => finiteMinmax (fun x => ∑ i, C x i*g i))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  have hi (x : U × V) : Integrable (fun g : ι → ℝ => ∑ i, C x i*g i)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    integrable_finsetSum _ (fun i _ =>
      ((gaussianCoordinate_memLp i).integrable (by norm_num)).const_mul _)
  apply (integrable_finsetSum Finset.univ (fun x _ => (hi x).abs)).mono'
    (continuous_finiteMinmax _ (fun x => by fun_prop)).aestronglyMeasurable
  apply ae_of_all
  intro g
  rw [Real.norm_eq_abs]
  exact finiteMinmax_abs_le _ _ (fun x =>
    Finset.single_le_sum (fun y _ => abs_nonneg (∑ i, C y i*g i)) (Finset.mem_univ x))

lemma indexedGaussianMinmax_reindex {n : ℕ} (e : Fin n ≃ ι) (C : U × V → ι → ℝ) :
    (∫ g, finiteMinmax (fun x => ∑ i, C x i*g i)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
    ∫ g, finiteMinmax (fun x => linearGaussian (fun x j => C x (e j)) g x)
      ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  let E := MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e
  have hp : MeasurePreserving E
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    measurePreserving_piCongrLeft (fun _ : ι => gaussianReal 0 1) e
  rw [← hp.hasLaw.integral_comp (continuous_finiteMinmax _ (fun x => by fun_prop)).aestronglyMeasurable]
  apply integral_congr_ae
  apply ae_of_all
  intro g
  dsimp only [Function.comp_def]
  congr 1
  funext x
  have heq (i : ι) : E g i = g (e.symm i) := by
    simpa only [Equiv.apply_symm_apply] using
      (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ι => ℝ) e g (e.symm i))
  simp only [heq]
  have hs := e.sum_comp (fun i => C x i*g (e.symm i))
  simpa only [linearGaussian,Equiv.symm_apply_apply] using hs.symm

theorem indexed_gaussian_minmax_comparison [Nonempty ι] (C A : U × V → ι → ℝ)
    (hCA : ∀ x y, (∑ i, C x i*A y i) = 0)
    (hrow : ∀ x u, (∑ i, A x i*A (u,x.2) i) = ∑ i, C x i*C (u,x.2) i)
    (hoff : ∀ x y, (∑ i, A x i*A y i) ≤ ∑ i, C x i*C y i) :
    (∫ g, finiteMinmax (fun x => ∑ i, A x i*g i)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) ≤
    ∫ g, finiteMinmax (fun x => ∑ i, C x i*g i)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  let d := Fintype.card ι-1
  have hc : Fintype.card ι = d+1 := by
    have := Fintype.card_pos (α := ι)
    dsimp [d]
    omega
  let e : Fin (d+1) ≃ ι := (finCongr hc.symm).trans (Fintype.equivFin ι).symm
  rw [indexedGaussianMinmax_reindex e A,indexedGaussianMinmax_reindex e C]
  apply finite_gaussian_minmax_comparison
  · intro x y
    change (∑ j, C x (e j)*A y (e j)) = 0
    rw [e.sum_comp (fun i => C x i*A y i)]
    exact hCA x y
  · intro x u
    change (∑ j, A x (e j)*A (u,x.2) (e j)) = ∑ j, C x (e j)*C (u,x.2) (e j)
    rw [e.sum_comp (fun i => A x i*A (u,x.2) i),e.sum_comp (fun i => C x i*C (u,x.2) i)]
    exact hrow x u
  · intro x y
    change (∑ j, A x (e j)*A y (e j)) ≤ ∑ j, C x (e j)*C y (e j)
    rw [e.sum_comp (fun i => A x i*A y i),e.sum_comp (fun i => C x i*C y i)]
    exact hoff x y

end InvariantIsing

end

end OAI
