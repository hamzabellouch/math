import Mathlib
import OAI.Analysis.LaughlinFock.PositiveIntegrals

namespace OAI

/-! Averaged Operators. -/
noncomputable section
namespace LaughlinFock
open scoped Matrix Matrix.Norms.Elementwise ComplexOrder BigOperators
open MeasureTheory
local instance averagedOperatorsContinuousENorm {ι κ : Type*} [Fintype ι] [Fintype κ] :
    ContinuousENorm (Matrix ι κ ℂ) :=
  inferInstanceAs (ContinuousENorm (ι → κ → ℂ))

 
theorem matrixIntegral_mul_left_right {G ι κ α β : Type*}
    [MeasurableSpace G] [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    (μ : Measure G) {M : G → Matrix ι κ ℂ} (hM : Integrable M μ)
    (A : Matrix α ι ℂ) (B : Matrix κ β ℂ) :
    A * (∫ g, M g ∂μ) * B = ∫ g, A * M g * B ∂μ := by
  let L : Matrix ι κ ℂ →ₗ[ℂ] Matrix α β ℂ :=
    { toFun := fun X => A * X * B
      map_add' _ _ := by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' _ _ := by simp [Matrix.mul_smul, Matrix.smul_mul] }
  exact (L.toContinuousLinearMap.integral_comp_comm hM).symm

 
theorem matrixIntegral_trace {G ι : Type*} [MeasurableSpace G] [Fintype ι]
    (μ : Measure G) {M : G → Matrix ι ι ℂ} (hM : Integrable M μ) :
    (∫ g, M g ∂μ).trace = ∫ g, (M g).trace ∂μ :=
  ((Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap.integral_comp_comm hM).symm

 

def matrixConjugationAverage {G ι : Type*} [MeasurableSpace G] [Fintype ι]
    (μ : Measure G) (U : G → Matrix ι ι ℂ) (M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∫ g, U g * M * (U g)ᴴ ∂μ

theorem matrixConjugationAverage_posSemidef {G ι : Type*}
    [MeasurableSpace G] [Fintype ι] (μ : Measure G) (U : G → Matrix ι ι ℂ)
    (M : Matrix ι ι ℂ) (hM : M.PosSemidef)
    (hI : Integrable (fun g => U g * M * (U g)ᴴ) μ) :
    (matrixConjugationAverage μ U M).PosSemidef :=
  conjugationIntegral_posSemidef μ U M hM hI

 
theorem matrixConjugationAverage_invariant {G ι : Type*}
    [Group G] [MeasurableSpace G] [MeasurableMul G] [Fintype ι] [DecidableEq ι]
    (μ : Measure G) [μ.IsMulLeftInvariant] (U : G →* Matrix ι ι ℂ)
    (M : Matrix ι ι ℂ) (hI : Integrable (fun g => U g * M * (U g)ᴴ) μ) (h : G) :
    U h * matrixConjugationAverage μ U M * (U h)ᴴ =
      matrixConjugationAverage μ U M := by
  unfold matrixConjugationAverage
  rw [matrixIntegral_mul_left_right μ hI]
  calc
    _ = ∫ g, U (h*g) * M * (U (h*g))ᴴ ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun g => by
        simp only [map_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := integral_mul_left_eq_self (μ := μ) (fun g => U g * M * (U g)ᴴ) h

 

theorem matrixConjugationAverage_commutes {G ι : Type*}
    [Group G] [MeasurableSpace G] [MeasurableMul G] [Fintype ι] [DecidableEq ι]
    (μ : Measure G) [μ.IsMulLeftInvariant] (U : G →* Matrix ι ι ℂ)
    (hU : ∀ g, (U g)ᴴ * U g = 1) (M : Matrix ι ι ℂ)
    (hI : Integrable (fun g => U g * M * (U g)ᴴ) μ) (h : G) :
    matrixConjugationAverage μ U M * U h = U h * matrixConjugationAverage μ U M := by
  have hv := congrArg (fun A => A * U h) (matrixConjugationAverage_invariant μ U M hI h)
  simpa only [Matrix.mul_assoc, hU, Matrix.mul_one] using hv.symm

 
theorem matrixConjugationAverage_trace {G ι : Type*}
    [MeasurableSpace G] [Fintype ι] [DecidableEq ι]
    (μ : Measure G) [IsProbabilityMeasure μ] (U : G → Matrix ι ι ℂ)
    (hU : ∀ g, (U g)ᴴ * U g = 1) (M : Matrix ι ι ℂ)
    (hI : Integrable (fun g => U g * M * (U g)ᴴ) μ) :
    (matrixConjugationAverage μ U M).trace = M.trace := by
  rw [matrixConjugationAverage, matrixIntegral_trace μ hI]
  have ht (g : G) : (U g * M * (U g)ᴴ).trace = M.trace := by
    rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  simp only [ht, integral_const, probReal_univ, one_smul]

 
def matrixRepresentation {G ι : Type*} [Monoid G] [Fintype ι] [DecidableEq ι]
    (U : G →* Matrix ι ι ℂ) : Representation ℂ G (ι → ℂ) :=
  (Matrix.toLinAlgEquiv' : Matrix ι ι ℂ ≃ₐ[ℂ] Module.End ℂ (ι → ℂ)).toMonoidHom.comp U

 
theorem matrix_scalar_of_commutes {G ι : Type*} [Monoid G] [Fintype ι] [DecidableEq ι]
    (U : G →* Matrix ι ι ℂ) [Representation.IsIrreducible (matrixRepresentation U)]
    (A : Matrix ι ι ℂ) (hA : ∀ g, A * U g = U g * A) : ∃ z : ℂ, A = z • 1 := by
  let ρ := matrixRepresentation U
  let f : Representation.IntertwiningMap ρ ρ :=
    { toLinearMap := Matrix.toLin' A
      isIntertwining' g := by
        change Matrix.toLin' A ∘ₗ Matrix.toLin' (U g) = Matrix.toLin' (U g) ∘ₗ Matrix.toLin' A
        simp only [← Matrix.toLin'_mul, hA] }
  obtain ⟨z, hz⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective f
  refine ⟨z, ?_⟩
  apply Matrix.toLin'.injective
  have hz' := congrArg Representation.IntertwiningMap.toLinearMap hz
  rw [Representation.IntertwiningMap.algebraMap_apply,
    Representation.IntertwiningMap.toLinearMap_smul] at hz'
  change z • LinearMap.id = Matrix.toLin' A at hz'
  simpa only [map_smul, Matrix.toLin'_one] using hz'.symm

 

theorem schur_matrix_average {G ι : Type*}
    [Group G] [MeasurableSpace G] [MeasurableMul G] [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (μ : Measure G) [μ.IsMulLeftInvariant] [IsProbabilityMeasure μ]
    (U : G →* Matrix ι ι ℂ) [Representation.IsIrreducible (matrixRepresentation U)]
    (hU : ∀ g, (U g)ᴴ * U g = 1) (M : Matrix ι ι ℂ)
    (hI : Integrable (fun g => U g * M * (U g)ᴴ) μ) :
    matrixConjugationAverage μ U M = (M.trace / (Fintype.card ι : ℂ)) • 1 := by
  obtain ⟨z, hz⟩ := matrix_scalar_of_commutes U _
    (matrixConjugationAverage_commutes μ U hU M hI)
  have ht := matrixConjugationAverage_trace μ (U : G → Matrix ι ι ℂ) hU M hI
  rw [hz, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul] at ht
  have hn : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : z = M.trace / (Fintype.card ι : ℂ) := (eq_div_iff hn).mpr ht
  rw [hz, he]

end LaughlinFock
end

end OAI
