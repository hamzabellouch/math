import Mathlib
import OAI.Analysis.LaughlinFock.AveragedOperators

namespace OAI

/-! Tensor Integrals. -/
noncomputable section
namespace LaughlinFock
open scoped Matrix Matrix.Norms.Elementwise ComplexOrder BigOperators Kronecker
open MeasureTheory
local instance tensorIntegralsContinuousENorm {ι κ : Type*} [Fintype ι] [Fintype κ] :
    ContinuousENorm (Matrix ι κ ℂ) :=
  inferInstanceAs (ContinuousENorm (ι → κ → ℂ))

 

def copyBlock {ι κ : Type*} (M : Matrix (ι × κ) (ι × κ) ℂ) (r s : κ) :
    Matrix ι ι ℂ := M.submatrix (fun i => (i,r)) (fun j => (j,s))

 

def copyPartialTrace {ι κ : Type*} [Fintype ι]
    (M : Matrix (ι × κ) (ι × κ) ℂ) : Matrix κ κ ℂ :=
  fun r s => (copyBlock M r s).trace

def copyBlockLinear {ι κ : Type*} (r s : κ) :
    Matrix (ι × κ) (ι × κ) ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun M := copyBlock M r s
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 
theorem copyBlock_integral {G ι κ : Type*} [MeasurableSpace G]
    [Fintype ι] [Fintype κ] (μ : Measure G)
    {M : G → Matrix (ι × κ) (ι × κ) ℂ} (hM : Integrable M μ) (r s : κ) :
    copyBlock (∫ g, M g ∂μ) r s = ∫ g, copyBlock (M g) r s ∂μ :=
  ((copyBlockLinear r s).toContinuousLinearMap.integral_comp_comm hM).symm

 

theorem copyBlock_conjugation {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (A : Matrix ι ι ℂ) (M : Matrix (ι × κ) (ι × κ) ℂ) (r s : κ) :
    copyBlock ((A ⊗ₖ (1 : Matrix κ κ ℂ)) * M * (A ⊗ₖ (1 : Matrix κ κ ℂ))ᴴ) r s =
      A * copyBlock M r s * Aᴴ := by
  classical
  ext i j
  simp [copyBlock, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, apply_ite, Finset.sum_mul]

 

theorem schur_multiplicity_average {G ι κ : Type*}
    [Group G] [MeasurableSpace G] [MeasurableMul G]
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype κ] [DecidableEq κ]
    (μ : Measure G) [μ.IsMulLeftInvariant] [IsProbabilityMeasure μ]
    (U : G →* Matrix ι ι ℂ) [Representation.IsIrreducible (matrixRepresentation U)]
    (hU : ∀ g, (U g)ᴴ * U g = 1) (M : Matrix (ι × κ) (ι × κ) ℂ)
    (hI : Integrable (fun g => (U g ⊗ₖ (1 : Matrix κ κ ℂ)) * M *
      (U g ⊗ₖ (1 : Matrix κ κ ℂ))ᴴ) μ) :
    matrixConjugationAverage μ (fun g => U g ⊗ₖ (1 : Matrix κ κ ℂ)) M =
      ((Fintype.card ι : ℂ)⁻¹) • ((1 : Matrix ι ι ℂ) ⊗ₖ copyPartialTrace M) := by
  have hblock (r s : κ) :
      copyBlock (matrixConjugationAverage μ (fun g => U g ⊗ₖ (1 : Matrix κ κ ℂ)) M) r s =
        ((copyBlock M r s).trace / (Fintype.card ι : ℂ)) • 1 := by
    have hi := (copyBlockLinear (ι := ι) r s).toContinuousLinearMap.integrable_comp hI
    have hib : Integrable (fun g => U g * copyBlock M r s * (U g)ᴴ) μ := by
      change Integrable (fun g => copyBlock ((U g ⊗ₖ (1 : Matrix κ κ ℂ)) * M *
        (U g ⊗ₖ (1 : Matrix κ κ ℂ))ᴴ) r s) μ at hi
      simpa only [copyBlock_conjugation] using hi
    unfold matrixConjugationAverage
    rw [copyBlock_integral μ hI]
    simp_rw [copyBlock_conjugation]
    exact schur_matrix_average μ U hU (copyBlock M r s) hib
  ext ⟨i,r⟩ ⟨j,s⟩
  have he := congrArg (fun X : Matrix ι ι ℂ => X i j) (hblock r s)
  change _ = _ at he
  rw [show matrixConjugationAverage μ (fun g => U g ⊗ₖ 1) M (i,r) (j,s) =
    (copyBlock M r s).trace / (Fintype.card ι : ℂ) * (1 : Matrix ι ι ℂ) i j from he]
  simp only [Matrix.smul_apply, Matrix.kronecker_apply, smul_eq_mul, copyPartialTrace, div_eq_mul_inv]
  ring

 

theorem matrix_intertwiner_eq_zero_of_card_ne {G ι κ : Type*} [Monoid G]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : G →* Matrix ι ι ℂ) (V : G →* Matrix κ κ ℂ)
    [Representation.IsIrreducible (matrixRepresentation U)]
    [Representation.IsIrreducible (matrixRepresentation V)]
    (hcard : Fintype.card ι ≠ Fintype.card κ) (A : Matrix ι κ ℂ)
    (hA : ∀ g, A * V g = U g * A) : A = 0 := by
  let f : Representation.IntertwiningMap (matrixRepresentation V) (matrixRepresentation U) :=
    { toLinearMap := Matrix.toLin' A
      isIntertwining' g := by
        change Matrix.toLin' A ∘ₗ Matrix.toLin' (V g) = Matrix.toLin' (U g) ∘ₗ Matrix.toLin' A
        simp only [← Matrix.toLin'_mul, hA] }
  rcases Representation.IsIrreducible.bijective_or_eq_zero f with hf | hf
  · have he := (LinearEquiv.ofBijective f.toLinearMap hf).finrank_eq
    have hc : Fintype.card κ = Fintype.card ι := by simpa using he
    exact False.elim (hcard hc.symm)
  · apply Matrix.toLin'.injective
    have he := congrArg Representation.IntertwiningMap.toLinearMap hf
    change Matrix.toLin' A = 0 at he
    simpa only [map_zero] using he

 

theorem schur_cross_average {G ι κ : Type*}
    [Group G] [MeasurableSpace G] [MeasurableMul G]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (μ : Measure G) [μ.IsMulLeftInvariant]
    (U : G →* Matrix ι ι ℂ) (V : G →* Matrix κ κ ℂ)
    [Representation.IsIrreducible (matrixRepresentation U)]
    [Representation.IsIrreducible (matrixRepresentation V)]
    (hcard : Fintype.card ι ≠ Fintype.card κ)
    (hV : ∀ g, (V g)ᴴ * V g = 1) (M : Matrix ι κ ℂ)
    (hI : Integrable (fun g => U g * M * (V g)ᴴ) μ) :
    (∫ g, U g * M * (V g)ᴴ ∂μ) = 0 := by
  apply matrix_intertwiner_eq_zero_of_card_ne U V hcard
  intro h
  have hinv : U h * (∫ g, U g * M * (V g)ᴴ ∂μ) * (V h)ᴴ =
      ∫ g, U g * M * (V g)ᴴ ∂μ := by
    rw [matrixIntegral_mul_left_right μ hI]
    calc
      _ = ∫ g, U (h*g) * M * (V (h*g))ᴴ ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun g => by
          simp only [map_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := integral_mul_left_eq_self (μ := μ) (fun g => U g * M * (V g)ᴴ) h
  have he := congrArg (fun A => A * V h) hinv
  simpa only [Matrix.mul_assoc, hV, Matrix.mul_one] using he.symm

end LaughlinFock
end

end OAI
