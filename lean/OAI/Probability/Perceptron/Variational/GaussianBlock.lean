import Mathlib
import OAI.Probability.Perceptron.Sphere.GaussianPolar

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal NNReal
namespace SphericalPerceptronFreeEnergy

def gaussianBlockSplit (N L : ℕ) (x : Spin (N+L)) : Spin N × Spin L :=
  (WithLp.toLp 2 (fun i => x (Fin.castAdd L i)),WithLp.toLp 2 (fun j => x (Fin.natAdd N j)))

lemma gaussianBlockSplit_measurable (N L : ℕ) : Measurable (gaussianBlockSplit N L) := by
  unfold gaussianBlockSplit
  fun_prop

lemma gaussianBlockSplit_preserving (N L : ℕ) :
    MeasurePreserving (gaussianBlockSplit N L) (stdGaussian (Spin (N+L)))
      ((stdGaussian (Spin N)).prod (stdGaussian (Spin L))) := by
  have hp := (measurePreserving_sumPiEquivProdPi (fun _ : Fin N ⊕ Fin L => gaussianReal 0 1)).comp
    (measurePreserving_piCongrLeft (fun _ : Fin N ⊕ Fin L => gaussianReal 0 1) finSumFinEquiv.symm)
  have hN : MeasurePreserving (WithLp.toLp 2 : (Fin N→ℝ)→Spin N)
      (Measure.pi fun _ => gaussianReal 0 1) (stdGaussian (Spin N)) :=
    ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩
  have hL : MeasurePreserving (WithLp.toLp 2 : (Fin L→ℝ)→Spin L)
      (Measure.pi fun _ => gaussianReal 0 1) (stdGaussian (Spin L)) :=
    ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩
  refine ⟨gaussianBlockSplit_measurable N L,?_⟩
  rw [←map_pi_eq_stdGaussian,Measure.map_map (gaussianBlockSplit_measurable N L)
    (PiLp.continuous_toLp 2 _).measurable]
  convert ((hN.prod hL).comp hp).map_eq using 1
  congr 1
  funext x
  apply Prod.ext <;> ext i <;>
    simp [gaussianBlockSplit,MeasurableEquiv.piCongrLeft,MeasurableEquiv.sumPiEquivProdPi,
      Equiv.piCongrLeft,Equiv.piCongrLeft',eq_rec_constant]

lemma gaussianBlockSplit_norm_sq (N L : ℕ) (x : Spin (N+L)) :
    ‖x‖^2=‖(gaussianBlockSplit N L x).1‖^2+‖(gaussianBlockSplit N L x).2‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq,gaussianBlockSplit,Real.norm_eq_abs,sq_abs]
  exact Fin.sum_univ_add _

lemma stdGaussian_direction_law (n : ℕ) :
    (stdGaussian (Spin (n+1))).map (fun x => ‖x‖⁻¹ •x)=
      (unitSphereLaw (n+1)).map Subtype.val := by
  have : IsProbabilityMeasure ((gaussianRadiusLaw n).map Subtype.val) := inferInstance
  have h := congrArg (fun μ : Measure (ℝ×Spin (n+1)) => μ.map Prod.snd) (normalizedGaussian_polar_law n)
  rwa [Measure.map_map measurable_snd (by fun_prop),Measure.map_snd_prod,measure_univ,one_smul] at h

end SphericalPerceptronFreeEnergy
end

end OAI
