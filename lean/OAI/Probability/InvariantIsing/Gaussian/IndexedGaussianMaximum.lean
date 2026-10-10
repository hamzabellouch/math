import OAI.Probability.InvariantIsing.Gaussian.GaussianMaximumComparison

namespace OAI

/-! The finite maximum comparison with an arbitrary nonempty Gaussian coordinate set. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {X ι : Type*} [Fintype X] [Nonempty X] [Fintype ι]

def indexedGaussianMaximum (C : X → ι → ℝ) (g : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun x => ∑ i, C x i*g i)

lemma measurable_indexedGaussianMaximum (C : X → ι → ℝ) : Measurable (indexedGaussianMaximum C) := by
  have hm := Finset.measurable_sup' (s := (Finset.univ : Finset X)) Finset.univ_nonempty
    (fun x _ => show Measurable (fun g : ι → ℝ => ∑ i, C x i*g i) from by fun_prop)
  convert hm using 1
  funext g
  rw [Finset.sup'_apply]
  rfl

lemma indexedGaussianMaximum_reindex {n : ℕ} (e : Fin n ≃ ι) (C : X → ι → ℝ) :
    (∫ g, indexedGaussianMaximum C g ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
    ∫ g, finiteGaussianMaximum (fun x j => C x (e j)) g
      ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  let E := MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e
  have hp : MeasurePreserving E
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    measurePreserving_piCongrLeft (fun _ : ι => gaussianReal 0 1) e
  rw [← hp.hasLaw.integral_comp (measurable_indexedGaussianMaximum C).aestronglyMeasurable]
  apply integral_congr_ae
  apply ae_of_all
  intro g
  unfold indexedGaussianMaximum finiteGaussianMaximum
  dsimp only [Function.comp_def]
  congr 1
  funext x
  have heq (i : ι) : E g i = g (e.symm i) := by
    simpa only [Equiv.apply_symm_apply] using
      (MeasurableEquiv.piCongrLeft_apply_apply
        (β := fun _ : ι => ℝ) e g (e.symm i))
  simp only [heq]
  have hs := e.sum_comp (fun i => C x i*g (e.symm i))
  simpa only [linearGaussian,Equiv.symm_apply_apply] using hs.symm

theorem indexed_gaussian_maximum_comparison [Nonempty ι] (C A : X → ι → ℝ)
    (hCA : ∀ x y, (∑ i, C x i*A y i) = 0)
    (hdiag : ∀ x, (∑ i, A x i*A x i) = ∑ i, C x i*C x i)
    (hoff : ∀ x y, (∑ i, A x i*A y i) ≤ ∑ i, C x i*C y i) :
    (∫ g, indexedGaussianMaximum C g ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) ≤
    ∫ g, indexedGaussianMaximum A g ∂Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  let d := Fintype.card ι-1
  have hc : Fintype.card ι = d+1 := by
    have := Fintype.card_pos (α := ι)
    dsimp [d]
    omega
  let e : Fin (d+1) ≃ ι := (finCongr hc.symm).trans (Fintype.equivFin ι).symm
  rw [indexedGaussianMaximum_reindex e C,indexedGaussianMaximum_reindex e A]
  apply finite_gaussian_maximum_comparison
  · intro x y
    change (∑ j, C x (e j)*A y (e j)) = 0
    rw [e.sum_comp (fun i => C x i*A y i)]
    exact hCA x y
  · intro x
    change (∑ j, A x (e j)*A x (e j)) = ∑ j, C x (e j)*C x (e j)
    rw [e.sum_comp (fun i => A x i*A x i),e.sum_comp (fun i => C x i*C x i)]
    exact hdiag x
  · intro x y
    change (∑ j, A x (e j)*A y (e j)) ≤ ∑ j, C x (e j)*C y (e j)
    rw [e.sum_comp (fun i => A x i*A y i),e.sum_comp (fun i => C x i*C y i)]
    exact hoff x y

end InvariantIsing

end

end OAI
