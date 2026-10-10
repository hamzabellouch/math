import Mathlib
import OAI.Probability.Perceptron.Variational.FieldDerivative

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def sourceFieldPolynomial {k : ℕ} (a : Fin (k+1)→ℝ) : Polynomial ℝ :=
  Lagrange.interpolate Finset.univ (fun l : Fin (k+1) => (l.val:ℝ)/(k+1:ℕ)) a

lemma sourceFieldPolynomial_eval {k : ℕ} (a : Fin (k+1)→ℝ) (l : Fin (k+1)) :
    (sourceFieldPolynomial a).eval ((l.val:ℝ)/(k+1:ℕ))=a l := by
  unfold sourceFieldPolynomial
  apply Lagrange.eval_interpolate_at_node (s := Finset.univ)
    (v := fun l : Fin (k+1) => (l.val:ℝ)/(k+1:ℕ)) (i := l) a
  · intro i hi j hj he
    apply Fin.ext
    have hv : (i.val:ℝ)=(j.val:ℝ) := (div_left_inj' (by positivity : ((k+1:ℕ):ℝ)≠0)).mp he
    exact_mod_cast hv
  · exact Finset.mem_univ l

lemma sourceFieldPolynomial_continuous {k : ℕ} (a : Fin (k+1)→ℝ) :
    Continuous (fun t : unitInterval => (sourceFieldPolynomial a).eval t.val) :=
  (sourceFieldPolynomial a).continuous.comp continuous_subtype_val

def sourceFieldArrayTest {k : ℕ} (a : Fin (k+1)→ℝ) : CompactArray CompactJointOverlap→ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun Q => (sourceFieldPolynomial a).eval (Q 1 0).2.val*(Q 1 0).1.val,
    by fun_prop⟩

lemma sourceGibbsArray_field_integral (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (hh0 : ∀ l, 0≤h l) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℝ≥0) (a : Fin (k+1)→ℝ) :
    (∫ Q, sourceFieldArrayTest a Q ∂sourceGibbsArrayLaw n k f p d h u z t)=
      ∫ b, gibbsReplicaMean (sourceSpinLeafKernel n k b.1)
        (sourceCouplingHamiltonian n k f p d h u b) 2 (sourceFieldObservable a)
          ∂((sourceBaseDataLaw n k z t).prod countableGaussianLaw) := by
  let F : CompactBlock CompactJointOverlap 2→ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun Q => (sourceFieldPolynomial a).eval (Q 1 0).2.val*(Q 1 0).1.val,by fun_prop⟩
  have he := sourceGibbsArray_block_integral n k f p d h hh0 hh u z t 2 F.measurable
    (fun Q => F.norm_coe_le_norm Q)
  change (∫ Q, sourceFieldArrayTest a Q ∂sourceGibbsArrayLaw n k f p d h u z t)=_ at he
  rw [he]
  apply integral_congr_ae
  exact ae_of_all _ fun b => by
    change gibbsReplicaMean (sourceSpinLeafKernel n k b.1) _ 2 _ = _
    congr 1
    funext x
    dsimp [F,sourceJointOverlap,sourceFieldObservable]
    rw [sourceFieldPolynomial_eval]

end SphericalPerceptronFreeEnergy
end

end OAI
