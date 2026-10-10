import OAI.Analysis.KadisonKastler.MeasurableHilbertCoordinates

namespace OAI

/-! # Measurable trivializations of projection ranges on dimension strata -/

namespace KadisonKastler

open MeasureTheory InnerProductSpace
open scoped lp

noncomputable section

/-- A fixed countable index type for each dimension stratum. -/
def projectionDimensionIndex : ℕ → Type
  | 0 => ℕ
  | n + 1 => Fin n

instance projectionDimensionIndex_countable (n : ℕ) : Countable (projectionDimensionIndex n) := by
  cases n <;> dsimp [projectionDimensionIndex] <;> infer_instance

def projectionDimensionIndexNat : {n : ℕ} → projectionDimensionIndex n → ℕ
  | 0, i => i
  | n + 1, i => (show Fin n from i).val

variable {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : X → H →L[ℂ] H) (hP : ∀ x, IsIdempotentElem (P x))
  (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)

def projectionRankStratum (n : ℕ) : Set X :=
  frameDimensionStratum (fun x i => measurableProjectionFrame P b x i ≠ 0) n

/-- A basis with a fixed index set on the whole dimension stratum. -/
def projectionStratumBasis (n : ℕ) (x : projectionRankStratum P b n) :
    HilbertBasis (projectionDimensionIndex n) ℂ (P x.val).range := by
  cases n with
  | zero => exact infiniteProjectionBasis P hP b hb x.val x.property
  | succ n => exact finiteProjectionBasis P hP b hb n x.val x.property

@[simp] theorem projectionStratumBasis_coe (n : ℕ) (x : projectionRankStratum P b n)
    (i : projectionDimensionIndex n) :
    (projectionStratumBasis P hP b hb n x i : H) =
      enumeratedProjectionFrame P b x.val (projectionDimensionIndexNat i) := by
  cases n with
  | zero => exact infiniteProjectionBasis_coe P hP b hb x.val x.property i
  | succ n => exact finiteProjectionBasis_coe P hP b hb n x.val x.property i

/-- The coordinate unitary uses the same target Hilbert space throughout a stratum. -/
def projectionStratumCoordinates (n : ℕ) (x : projectionRankStratum P b n) :
    (P x.val).range ≃ₗᵢ[ℂ] ℓ²(projectionDimensionIndex n, ℂ) :=
  (projectionStratumBasis P hP b hb n x).repr

variable [MeasurableSpace X] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

omit [CompleteSpace H] in
theorem measurableSet_projectionRankStratum (hPm : ∀ v, Measurable fun x => P x v) (n : ℕ) :
    MeasurableSet (projectionRankStratum P b n) :=
  measurableSet_frameDimensionStratum _ (fun i =>
    (measurableSet_eq_fun (measurableProjectionFrame_measurable P b hPm i)
      (measurable_const : Measurable fun _ : X => (0 : H))).compl) n

theorem projectionStratumBasis_measurable (hPm : ∀ v, Measurable fun x => P x v)
    (n : ℕ) (i : projectionDimensionIndex n) :
    Measurable fun x : projectionRankStratum P b n =>
      (projectionStratumBasis P hP b hb n x i : H) := by
  simp_rw [projectionStratumBasis_coe]
  exact (enumeratedProjectionFrame_measurable P b hPm (projectionDimensionIndexNat i)).comp
    measurable_subtype_coe

theorem projectionStratumCoordinates_measurable
    (hPm : ∀ v, Measurable fun x => P x v) (n : ℕ)
    [MeasurableSpace ℓ²(projectionDimensionIndex n, ℂ)]
    [BorelSpace ℓ²(projectionDimensionIndex n, ℂ)]
    (v : ∀ x : projectionRankStratum P b n, (P x.val).range)
    (hv : Measurable fun x => (v x : H)) :
    Measurable fun x => projectionStratumCoordinates P hP b hb n x (v x) :=
  measurable_rangeHilbertCoordinates (fun x : projectionRankStratum P b n => P x.val)
    (projectionStratumBasis P hP b hb n) (projectionStratumBasis_measurable P hP b hb hPm n) v hv

theorem projectionStratumCoordinates_symm_measurable
    (hPm : ∀ v, Measurable fun x => P x v) (n : ℕ)
    (v : projectionRankStratum P b n → ℓ²(projectionDimensionIndex n, ℂ))
    (hv : ∀ i, Measurable fun x => v x i) :
    Measurable fun x => ((projectionStratumCoordinates P hP b hb n x).symm (v x) : H) :=
  measurable_rangeHilbertSynthesis (fun x : projectionRankStratum P b n => P x.val)
    (projectionStratumBasis P hP b hb n) (projectionStratumBasis_measurable P hP b hb hPm n) v hv

end

end KadisonKastler

end OAI
