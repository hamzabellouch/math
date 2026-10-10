import OAI.Probability.InvariantIsing.Fields.PriorTensorReference
import OAI.Probability.InvariantIsing.Pressure.PressureDifferenceConcentration

namespace OAI

/-! The diagonal observable's actual CGF inherits concentration from
both neighboring finite-prior log partition functions. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

def priorDiagonalCGF {N m k n : ℕ} (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (v : Fin m → ℝ) (t : ℝ) (a : Fin m) (s : ℝ)
    (p : SpecialOrthogonal N × (ℕ → ℝ)) : ℝ :=
  cgf (fun x : Spin N × LabeledLeaf n => projectedOverlap (specialRotation p.1) (I a) x.1 x.1)
    (priorNamespacedReference ν (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t)
      c I degree amplitude (fun i => tensorPathProfile I degree n r h i) p) s

theorem priorDiagonalCGF_statistics {N m k n : ℕ} (hN : 0<N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0≤h 0) (v : Fin m → ℝ) (t : ℝ) (a : Fin m) (w B : ℝ)
    (hF : ∀ q : ℝ, q=w ∨ q=0 →
      MemLp (priorNamespacedLog ν (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
        c I degree amplitude (fun i => tensorPathProfile I degree n r h i)) 2 (μ.prod gaussianCoordinates))
    (hv : ∀ q : ℝ, q=w ∨ q=0 →
      variance (priorNamespacedLog ν (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
        c I degree amplitude (fun i => tensorPathProfile I degree n r h i)) (μ.prod gaussianCoordinates) ≤ B) :
    let P := μ.prod gaussianCoordinates
    let M := fun q => ∫ p, priorNamespacedLog ν
      (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
      c I degree amplitude (fun i => tensorPathProfile I degree n r h i) p ∂P
    let Z := priorDiagonalCGF ν eig c I degree amplitude r h v t a (N*perturbationScale N*w)
    MemLp Z 2 P ∧ (∫ p, Z p ∂P)=M w-M 0 ∧
      (∫ p, |Z p-∫ p', Z p' ∂P| ∂P)≤2*Real.sqrt B := by
  intro P M Z
  let F := fun q => priorNamespacedLog ν (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
    c I degree amplitude (fun i => tensorPathProfile I degree n r h i)
  have he : Z =ᵐ[P] fun p => (1 : ℝ)*(F w p-F 0 p) := by
    filter_upwards [prior_diagonal_cgf_eq_log_difference hN μ ν eig c I degree amplitude
      r h hh h0 v t a w] with p hp
    simpa only [one_mul,Z,F,priorDiagonalCGF] using hp
  have hc := centered_scaled_difference_L1_bound P (hF w (Or.inl rfl))
    (hF 0 (Or.inr rfl)) (hv w (Or.inl rfl)) (hv 0 (Or.inr rfl)) he
  refine ⟨hc.1,?_,?_⟩
  · rw [integral_congr_ae he]
    simp only [one_mul]
    exact integral_sub ((hF w (Or.inl rfl)).integrable (by norm_num))
      ((hF 0 (Or.inr rfl)).integrable (by norm_num))
  · simpa only [abs_one,mul_one,one_mul] using hc.2

end InvariantIsing

end

end OAI
