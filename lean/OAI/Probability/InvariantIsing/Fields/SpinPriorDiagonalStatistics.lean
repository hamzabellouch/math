import OAI.Probability.InvariantIsing.Fields.SpinPriorFrozenGibbs
import OAI.Probability.InvariantIsing.Pressure.PressureDifferenceConcentration

namespace OAI

/-! Diagonal CGF and pressure concentration for the actual constrained
cascade model. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

def spinPriorDiagonalCGF {N m k : ℕ} (π : Measure (Spin N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (r : Fin k → ℕ) (h : ℕ → ℝ) (v : Fin m → ℝ) (t : ℝ) (a : Fin m)
    (s : ℝ) (p : TensorFlatDisorder N n) : ℝ :=
  cgf (fun x : Spin N × LabeledLeaf n => projectedOverlap (specialRotation p.1.1) (I a) x.1 x.1)
    (spinPriorNamespacedReference (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t)
      c I degree amplitude r h p) s

/-- At its true coefficient `N e_N w`, a frozen diagonal tilt is exactly
the actual perturbed partition difference. -/
theorem spinPriorDiagonalCGF_eq_log_difference {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (v : Fin m → ℝ) (t : ℝ) (a : Fin m) (w : ℝ) :
    spinPriorDiagonalCGF π eig c I degree amplitude n r h v t a (N * perturbationScale N * w) =ᵐ[
      (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates]
      (fun p => spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a w) t)
        c I degree amplitude r h p -
        spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t)
          c I degree amplitude r h p) := by
  have he := spinPriorNamespaced_exp_integrable_ae μ π
    (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t) c I degree amplitude n b r h hh h0
  filter_upwards [he] with p hp
  let H := tensorNamespacedHamiltonian
    (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t) c I degree amplitude n r h p
  let Y := fun x : Spin N × LabeledLeaf n => projectedOverlap (specialRotation p.1.1) (I a) x.1 x.1
  have hbnd : ∀ x, |(N * perturbationScale N * w) * Y x| ≤ |N * perturbationScale N * w| := by
    intro x
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (projectedOverlap_abs_le_one _ _ _ _) (abs_nonneg _)).trans_eq (mul_one _)
  have ht : Integrable (fun x => Real.exp (H x + (N * perturbationScale N * w) * Y x))
      (labeledSpinReference n π p.1.2) := by
    simpa only [add_comm] using integrable_exp_bounded_add (H := H)
      (B := fun x => (N * perturbationScale N * w) * Y x) hp (measurable_of_countable _)
      (fun x => (le_abs_self _).trans (hbnd x))
  have heq : (fun x => H x + (N * perturbationScale N * w) * Y x) =
      tensorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I (Function.update v a w) t)
        c I degree amplitude n r h p := by
    funext x
    dsimp only [H, Y, tensorNamespacedHamiltonian]
    rw [rotatedEnergy_diagonal_coordinate hN eig (specialRotation p.1.1) I v t a w x.1]
    ring
  change cgf Y (gibbsProbability _ H) _ = _
  rw [cgf_fold _ H Y _ hp ht, heq]
  rfl

theorem spinPriorDiagonalCGF_statistics {N m k n : ℕ} (hN : 0<N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (b : ℕ → ℝ)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0≤h 0) (v : Fin m → ℝ) (t : ℝ) (a : Fin m) (w B : ℝ)
    (hF : ∀ q : ℝ, q=w ∨ q=0 →
      MemLp (spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
        c I degree amplitude r h) 2 (((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)))
    (hv : ∀ q : ℝ, q=w ∨ q=0 →
      variance (spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
        c I degree amplitude r h) (((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)) ≤ B) :
    let P := ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)
    let M := fun q => ∫ p, spinPriorNamespacedLog (n := n) π
      (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
      c I degree amplitude r h p ∂P
    let Z := spinPriorDiagonalCGF π eig c I degree amplitude n r h v t a (N*perturbationScale N*w)
    MemLp Z 2 P ∧ (∫ p, Z p ∂P)=M w-M 0 ∧
      (∫ p, |Z p-∫ p', Z p' ∂P| ∂P)≤2*Real.sqrt B := by
  intro P M Z
  let F := fun q => spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
    c I degree amplitude r h
  have he : Z =ᵐ[P] fun p => (1 : ℝ)*(F w p-F 0 p) := by
    filter_upwards [spinPriorDiagonalCGF_eq_log_difference hN μ π eig c I degree amplitude
      n b r h hh h0 v t a w] with p hp
    simpa only [one_mul,Z,F,spinPriorDiagonalCGF] using hp
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
