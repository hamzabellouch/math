import OAI.Probability.InvariantIsing.Gaussian.IndexedGaussianMaximum
import OAI.Probability.InvariantIsing.Gaussian.GaussianCoordinateNorm

namespace OAI

/-! Integrability and restriction of finite Gaussian maxima. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace InvariantIsing
variable {X ι κ : Type*} [Fintype X] [Nonempty X] [Fintype ι] [Fintype κ]

lemma indexedGaussianMaximum_integrable (C : X → ι → ℝ) :
    Integrable (indexedGaussianMaximum C) (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  have hi (x : X) : Integrable (fun g : ι → ℝ => ∑ i, C x i*g i)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    integrable_finsetSum Finset.univ (fun i _ =>
      ((gaussianCoordinate_memLp i).integrable (by norm_num)).const_mul _)
  apply (integrable_finsetSum Finset.univ (fun x _ => (hi x).abs)).mono'
    (measurable_indexedGaussianMaximum C).aestronglyMeasurable
  apply ae_of_all
  intro g
  obtain ⟨x,hx,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun x => ∑ i, C x i*g i)
  change ‖Finset.univ.sup' Finset.univ_nonempty _‖ ≤ _
  rw [he,Real.norm_eq_abs]
  exact Finset.single_le_sum (fun y _ => abs_nonneg (∑ i, C y i*g i)) hx

lemma iidGaussian_restrict_hasLaw (e : κ → ι) (he : Function.Injective e) :
    HasLaw (fun g : ι → ℝ => fun j => g (e j))
      (Measure.pi (fun _ : κ => gaussianReal 0 1))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  have hi : iIndepFun (fun i (g : ι → ℝ) => g i)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  exact (hi.precomp he).hasLaw_pi (fun j =>
    (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) (e j)).hasLaw)

lemma indexedGaussianMaximum_add_constant (C : X → ι → ℝ) (g : ι → ℝ) (a : ℝ) :
    Finset.univ.sup' Finset.univ_nonempty (fun x => (∑ i, C x i*g i)+a) =
      indexedGaussianMaximum C g+a := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro x _
    exact add_le_add (Finset.le_sup' (fun x => ∑ i, C x i*g i) (Finset.mem_univ x)) (le_refl a)
  · obtain ⟨x,hx,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun x => ∑ i, C x i*g i)
    unfold indexedGaussianMaximum
    rw [he]
    exact Finset.le_sup' (fun x => (∑ i, C x i*g i)+a) hx

end InvariantIsing

end

end OAI
