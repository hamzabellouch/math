import OAI.Analysis.LiebThirring.OneState

namespace OAI


noncomputable section
namespace SharpLiebThirring.OperatorProof
open MeasureTheory Set
open scoped Topology ENNReal

/-- The unbounded self-adjoint operator associated with exactly the H¹ form. -/
def schrodingerOperator {γ : ℝ} (hγ : 1/2 < γ) {W : ℝ → ℝ} (hW : Admissible γ W) :
    L2C →ₗ.[ℂ] L2C := operator (potentialData hγ hW)

lemma schrodingerOperator_selfAdjoint {γ : ℝ} (hγ : 1/2 < γ) {W : ℝ → ℝ}
    (hW : Admissible γ W) : IsSelfAdjoint (schrodingerOperator hγ hW) :=
  operator_selfAdjoint (potentialData hγ hW)

lemma schrodingerOperator_associated {γ : ℝ} (hγ : 1/2 < γ) {W : ℝ → ℝ}
    (hW : Admissible γ W) : IsAssociated W (schrodingerOperator hγ hW) :=
  operator_associated (potentialData hγ hW)

lemma eigenvalueSum_eq_negativeMoment {γ : ℝ} (hγ₀ : 1/2 < γ) (hγ₁ : γ < 3/2)
    {W : ℝ → ℝ} (hW : Admissible γ W) {A : L2C →ₗ.[ℂ] L2C}
    (hA : IsSelfAdjoint A) (ha : IsAssociated W A) :
    eigenvalueSum γ A hA = negativeMoment γ W := by
  have hbound : eigenvalueSum γ A hA ≤
      ENNReal.ofReal (sharpConstant γ)*potentialMass γ W := by
    calc
      _ ≤ eigenvalueMoment γ A := eigenvalueSum_le_moment γ A hA
      _ = negativeMoment γ W := (negativeMoment_eq_eigenvalueMoment ha γ).symm
      _ ≤ _ := negativeMoment_bound hγ₀ hγ₁ hW
  have hfin : eigenvalueSum γ A hA ≠ ∞ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hW.mass_ne_top hγ₀)) hbound
  exact (eigenvalueMoment_eq_sum hA hfin).symm.trans
    (negativeMoment_eq_eigenvalueMoment ha γ).symm

/-- The trace: sum of every negative eigenvalue of the form
operator, counted once for each member of a full eigenspace basis. -/
def spectralMoment {γ : ℝ} (hγ : 1/2 < γ) {W : ℝ → ℝ} (hW : Admissible γ W) : ℝ≥0∞ :=
  eigenvalueSum γ (schrodingerOperator hγ hW) (schrodingerOperator_selfAdjoint hγ hW)

lemma spectralMoment_eq {γ : ℝ} (hγ₀ : 1/2 < γ) (hγ₁ : γ < 3/2)
    {W : ℝ → ℝ} (hW : Admissible γ W) : spectralMoment hγ₀ hW = negativeMoment γ W :=
  eigenvalueSum_eq_negativeMoment hγ₀ hγ₁ hW (schrodingerOperator_selfAdjoint hγ₀ hW)
    (schrodingerOperator_associated hγ₀ hW)

def spectralOptimalConstant {γ : ℝ} (hγ : 1/2 < γ) : ℝ≥0∞ :=
  ⨆ (W : ℝ → ℝ) (hW : Admissible γ W) (_ : 0 < potentialMass γ W),
    spectralMoment hγ hW / potentialMass γ W

def spectralOneStateConstant {γ : ℝ} (hγ : 1/2 < γ) : ℝ≥0∞ :=
  ⨆ (W : ℝ → ℝ) (hW : Admissible γ W) (_ : 0 < potentialMass γ W),
    oneEigenvalueMoment γ (schrodingerOperator hγ hW) / potentialMass γ W

lemma spectralOptimalConstant_eq {γ : ℝ} (hγ₀ : 1/2 < γ) (hγ₁ : γ < 3/2) :
    spectralOptimalConstant hγ₀ = optimalConstant γ := by
  unfold spectralOptimalConstant optimalConstant
  congr 1
  funext W
  congr 1
  funext hW
  simp only [spectralMoment_eq hγ₀ hγ₁ hW]

lemma spectralOneStateConstant_eq {γ : ℝ} (hγ : 1/2 < γ) :
    spectralOneStateConstant hγ = oneStateConstant γ := by
  unfold spectralOneStateConstant oneStateConstant
  congr 1
  funext W
  congr 1
  funext hW
  simp only [← oneStateMoment_eq_oneEigenvalueMoment (schrodingerOperator_associated hγ hW)]

/-- The sharp bound for the infinite eigenvalue sum of any self-adjoint
operator associated with the form, together with finite multiplicities. -/
theorem sharp_bound_for_associated_operator {γ : ℝ} (hγ₀ : 1/2 < γ) (hγ₁ : γ < 3/2)
    {W : ℝ → ℝ} (hW : Admissible γ W) {A : L2C →ₗ.[ℂ] L2C}
    (hA : IsSelfAdjoint A) (ha : IsAssociated W A) :
    eigenvalueSum γ A hA ≤ ENNReal.ofReal (sharpConstant γ)*potentialMass γ W ∧
      ∀ e : NegativeEnergy, FiniteDimensional ℂ (eigenSpace A e.1) := by
  have hb : eigenvalueSum γ A hA ≤ ENNReal.ofReal (sharpConstant γ)*potentialMass γ W := by
    rw [eigenvalueSum_eq_negativeMoment hγ₀ hγ₁ hW hA ha]
    exact negativeMoment_bound hγ₀ hγ₁ hW
  exact ⟨hb,fun e ↦ eigenSpace_finiteDimensional hA
    (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hW.mass_ne_top hγ₀)) hb) e⟩

/-- All main conclusions in the actual-operator formulation. Its operator is
constructed unconditionally; no existence, trace equivalence, spectral estimate,
or finiteness assumption is used as an input. -/
theorem sharp_lieb_thirring_spectral {γ : ℝ} (hγ₀ : 1/2 < γ) (hγ₁ : γ < 3/2) :
    (∀ (W : ℝ → ℝ) (hW : Admissible γ W),
      spectralMoment hγ₀ hW ≤ ENNReal.ofReal (sharpConstant γ)*potentialMass γ W) ∧
    spectralOptimalConstant hγ₀ = ENNReal.ofReal (sharpConstant γ) ∧
    spectralOneStateConstant hγ₀ = ENNReal.ofReal (sharpConstant γ) ∧
    ∃ hW : Admissible γ (equalityPotential γ),
      0 < potentialMass γ (equalityPotential γ) ∧
      spectralMoment hγ₀ hW = ENNReal.ofReal (sharpConstant γ)*potentialMass γ (equalityPotential γ) := by
  obtain ⟨hb,ho,hs,hW,hp,he⟩ := sharp_lieb_thirring γ hγ₀ hγ₁
  refine ⟨fun W hW ↦ ?_,?_,?_,hW,hp,?_⟩
  · rw [spectralMoment_eq hγ₀ hγ₁ hW]
    exact hb W hW
  · rw [spectralOptimalConstant_eq hγ₀ hγ₁]; exact ho
  · rw [spectralOneStateConstant_eq hγ₀]; exact hs
  · rw [spectralMoment_eq hγ₀ hγ₁ hW]; exact he

end SharpLiebThirring.OperatorProof

end

end OAI
