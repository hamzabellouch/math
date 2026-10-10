import Mathlib
import OAI.Probability.Perceptron.Variational.GaussianCovarianceDerivative
import OAI.Probability.Perceptron.Cavity.BulkConcentration

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma bulkY_joint_measurable (N M : ℕ) (p : Fin N) :
    Measurable (fun a : BulkDisorder N M × NormalizedSpin N => bulkY N p a.1.2 a.2) :=
  (bulkY_measurable N p).comp (measurable_fst.snd.prodMk measurable_snd)

def bulkCouplingSlope (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1))
    (u : ℝ) (a : BulkDisorder (n+1) M) : ℝ :=
  bulkCoefficient (n+1) p*tiltMean (unitSphereLaw (n+1))
    (bulkHamiltonian (n+1) M f (Function.update v (p.val+1) u) a.1 a.2)
    (bulkY (n+1) p a.2) 1

lemma bulkCouplingSlope_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ) :
    Measurable (bulkCouplingSlope n M f v p u) := by
  apply Measurable.const_mul
  exact kernel_tiltMean_measurable (bulkSpinKernel n M)
    (H := fun a x => bulkHamiltonian (n+1) M f (Function.update v (p.val+1) u) a.1 a.2 x)
    (Y := fun a x => bulkY (n+1) p a.2 x)
    (bulkHamiltonian_continuous _ _ _ _).measurable (bulkY_joint_measurable _ _ _)

lemma bulkCoupling_regular (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1))
    (a : BulkDisorder (n+1) M) :
    ContDiff ℝ 2 (fun u => bulkLogPartition n M f (Function.update v (p.val+1) u) a.1 a.2) ∧
    ConvexOn ℝ univ (fun u => bulkLogPartition n M f (Function.update v (p.val+1) u) a.1 a.2) ∧
    ∀ u, HasDerivAt (fun u => bulkLogPartition n M f (Function.update v (p.val+1) u) a.1 a.2)
      (bulkCouplingSlope n M f v p u a) u := by
  let H := bulkHamiltonian (n+1) M f (Function.update v (p.val+1) 0) a.1 a.2
  let Y := fun x => bulkCoefficient (n+1) p*bulkY (n+1) p a.2 x
  have hH : Measurable H := bulkHamiltonian_section_measurable _ _ _ _ a
  have hY : Measurable Y := (bulkY_measurable _ _).of_uncurry_left.const_mul _
  have he (u : ℝ) : Integrable (fun x => Real.exp (H x+u*Y x)) (unitSphereLaw (n+1)) := by
    have hi := bulkHamiltonian_exp_integrable n M f (Function.update v (p.val+1) u) a
    convert hi using 1
    funext x
    congr 1
    exact (bulkHamiltonian_update _ _ _ _ _ _ _ _).symm
  have hf : (fun u => bulkLogPartition n M f (Function.update v (p.val+1) u) a.1 a.2)=
      (fun u => Real.log (tiltPartition (unitSphereLaw (n+1)) (fun x => H x+u*Y x) 1)) := by
    funext u
    rw [bulkLogPartition_eq]
    congr 2
    funext x
    exact bulkHamiltonian_update _ _ _ _ _ _ _ _
  rw [hf]
  refine ⟨coupling_log_contDiff _ hH hY he,coupling_log_convex _ hH hY he,?_⟩
  intro u
  convert coupling_log_hasDerivAt (unitSphereLaw (n+1)) hH hY he u using 1
  dsimp only [bulkCouplingSlope,Y]
  rw [tiltMean_const_mul_general]
  congr 2
  funext x
  exact bulkHamiltonian_update _ _ _ _ _ _ _ _

lemma bulkExpectedLog_hasDerivAt (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ) :
    Integrable (bulkCouplingSlope n M f v p u) (bulkDisorderLaw (n+1) M) ∧
    HasDerivAt (fun t => bulkExpectedLog n M f (Function.update v (p.val+1) t))
      (∫ a, bulkCouplingSlope n M f v p u a ∂bulkDisorderLaw (n+1) M) u := by
  apply annealed_convex_hasDerivAt (bulkDisorderLaw (n+1) M)
    (fun t => (bulkLogPartition_measurable n M f _).aestronglyMeasurable)
    (fun t => (bulkCouplingSlope_measurable n M f v p t).aestronglyMeasurable)
    (fun t => (bulkLogPartition_memLp n M f _).integrable (by norm_num))
  exact ae_of_all _ fun a => (bulkCoupling_regular n M f v p a).2

lemma bulkExpectedLog_convex (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) :
    ConvexOn ℝ univ (fun t => bulkExpectedLog n M f (Function.update v (p.val+1) t)) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  let F := fun t (d : BulkDisorder (n+1) M) => bulkLogPartition n M f (Function.update v (p.val+1) t) d.1 d.2
  have hi (t : ℝ) : Integrable (F t) (bulkDisorderLaw (n+1) M) :=
    (bulkLogPartition_memLp n M f _).integrable (by norm_num)
  have hi1 : Integrable (fun d => a*F x d) (bulkDisorderLaw (n+1) M) := (hi x).const_mul a
  have hi2 : Integrable (fun d => b*F y d) (bulkDisorderLaw (n+1) M) := (hi y).const_mul b
  change (∫ d, F (a*x+b*y) d ∂bulkDisorderLaw (n+1) M) ≤
    a*(∫ d, F x d ∂bulkDisorderLaw (n+1) M)+b*(∫ d, F y d ∂bulkDisorderLaw (n+1) M)
  calc
    _ ≤ ∫ d, a*F x d+b*F y d ∂bulkDisorderLaw (n+1) M := by
      apply integral_mono (hi _) (hi1.add hi2)
      intro d
      exact (bulkCoupling_regular n M f v p d).2.1.2 (mem_univ x) (mem_univ y) ha hb hab
    _ = _ := by rw [integral_add hi1 hi2,integral_const_mul,integral_const_mul]

end SphericalPerceptronFreeEnergy
end

end OAI
