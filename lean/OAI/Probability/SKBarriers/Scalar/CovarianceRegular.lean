import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyProbability

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
open Matrix
section CovarianceRegular
variable {S I : Type} [Fintype S]

theorem finiteCovariance_abs_le_two (p : S → ℝ) (v : S → I → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hs : ∑ s, p s = 1) (hv : ∀ s i, |v s i| ≤ 1) (i j : I) :
    |finiteCovariance p v i j| ≤ 2 := by
  have hfirst : |∑ s, p s*v s i*v s j| ≤ 1 := by
    calc
      _ ≤ ∑ s, |p s*v s i*v s j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s, p s := by
        apply Finset.sum_le_sum
        intro s _
        rw [abs_mul,abs_mul,abs_of_nonneg (hp s)]
        calc
          _ ≤ (p s*1)*1 := mul_le_mul (mul_le_mul_of_nonneg_left (hv s i) (hp s)) (hv s j)
            (abs_nonneg _) (by simpa using hp s)
          _ = p s := by ring
      _ = 1 := hs
  have hm := mul_le_mul (finiteMean_abs_le_one p v hp hs hv i)
    (finiteMean_abs_le_one p v hp hs hv j) (abs_nonneg (finiteMean p v j)) (by norm_num : (0 : ℝ) ≤ 1)
  rw [finiteCovariance_apply]
  calc
    _ ≤ |∑ s, p s*v s i*v s j|+|finiteMean p v i*finiteMean p v j| := abs_sub _ _
    _ ≤ 2 := by rw [abs_mul]; linarith

variable [Fintype I]

theorem matrix_trace_square_norm_bound (C : Matrix I I ℝ) (hC : ∀ i j, |C i j| ≤ 2) :
    ‖(C*C).trace‖ ≤ 4*(Fintype.card I : ℝ)^2 := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  calc
    _ ≤ ∑ i, ∑ j, ‖C i j*C j i‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ _ : I, ∑ _ : I, (4 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
      nlinarith [hC i j,hC j i,abs_nonneg (C i j),abs_nonneg (C j i)]
    _ = _ := by simp; ring

variable {Ω : Type} [TopologicalSpace Ω]

omit [Fintype I] in
theorem finiteMean_continuous (P : Ω → S → ℝ) (hP : ∀ s, Continuous (fun z => P z s)) (v : S → I → ℝ) (i : I) :
    Continuous (fun z => finiteMean (P z) v i) := by
  simp only [finiteMean_apply]
  exact continuous_finsetSum _ (fun s _ => (hP s).mul continuous_const)

omit [Fintype I] in
theorem finiteCovariance_continuous (P : Ω → S → ℝ) (hP : ∀ s, Continuous (fun z => P z s)) (v : S → I → ℝ) (i j : I) :
    Continuous (fun z => finiteCovariance (P z) v i j) := by
  simp only [finiteCovariance_apply]
  exact (continuous_finsetSum _ (fun s _ => ((hP s).mul continuous_const).mul continuous_const)).sub
    ((finiteMean_continuous P hP v i).mul (finiteMean_continuous P hP v j))

theorem traceSquare_continuous (C : Ω → Matrix I I ℝ) (hC : ∀ i j, Continuous (fun z => C z i j)) :
    Continuous (fun z => (C z*C z).trace) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  exact continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => (hC i j).mul (hC j i)))
end CovarianceRegular

attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section HierarchyTraceRegular
variable {S : Type} [Fintype S] [Nonempty S]

def hierarchyTraceSquare {N : ℕ} (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (v : S → Fin N → ℝ) (j : Fin (n+1)) (z : ParameterSpace n) : ℝ :=
  let C := finiteCovariance (hierarchySpinWeight n m U j z) v
  (C*C).trace

theorem hierarchyTraceSquare_regular {N : ℕ} (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (v : S → Fin N → ℝ) (hv : ∀ s i, |v s i| ≤ 1) (j : Fin (n+1)) :
    Continuous (hierarchyTraceSquare n m U v j) ∧
      ∀ z, ‖hierarchyTraceSquare n m U v j z‖ ≤ 4*(N : ℝ)^2 := by
  constructor
  · exact traceSquare_continuous _ (finiteCovariance_continuous _ (fun s => (hierarchySpinWeight_regular n m U j s).1) v)
  · intro z
    simpa only [hierarchyTraceSquare, Fintype.card_fin] using matrix_trace_square_norm_bound _
      (finiteCovariance_abs_le_two _ v (hierarchySpinWeight_nonneg n m U j z) (hierarchySpinWeight_sum n m U j z) hv)

theorem hierarchyTraceSquare_integrable {N : ℕ} (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (v : S → Fin N → ℝ) (hv : ∀ s i, |v s i| ≤ 1) (j : Fin (n+1)) (x : ℝ) :
    Integrable (hierarchyTraceSquare n m U v j) (hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) x) :=
  hierarchyPathLaw_integrable n m _ _ (affineLogPartition_boundedDerivs (fun _ => 0) U)
    (hierarchyTraceSquare_regular n m U v hv j).1 (hierarchyTraceSquare_regular n m U v hv j).2 x
end HierarchyTraceRegular

theorem hierarchyPathLaw_moment_integral (n : ℕ) (m : Fin n → ℝ) (f g : ParameterSpace n → ℝ)
    (hf : BoundedDerivs f) (hg : Continuous g) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ z, ‖g z‖ ≤ C)
    (j : Fin (n+1)) (x : ℝ) :
    (∫ z, hierarchyMomentLevel n m f g j z ∂hierarchyPathLaw n m f x) =
      ∫ z, g z ∂hierarchyPathLaw n m f x := by
  have hr := hierarchyMomentLevel_bounded_continuous n m f g hf hg hC hb j
  rw [← hierarchyAverage_eq_integral n m f hf _ hr.1 hC hr.2 x,
    ← hierarchyAverage_eq_integral n m f hf g hg hC hb x,hierarchyAverage_momentLevel]
  exact hf
end SK.Analytic

end
end

end

end OAI
