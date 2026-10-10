import OAI.Analysis.FiniteFactor.CrossedProduct.StageOperator
import OAI.Analysis.FiniteFactor.CrossedProduct.Rotation
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Algebra.Star.Subalgebra

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Pointwise
noncomputable section

/-- A bounded Borel function on the source cube. Values outside the cube
are irrelevant because the representation evaluates rotation representatives. -/
structure SourceBaseFunction where
  toFun : (SourceCoordinate → ℝ) → ℂ
  measurable : Measurable toFun
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_le : ∀ x, (∀ i, x i ∈ Set.Ico 0 1) → ‖toFun x‖ ≤ bound

def sourcePiSymbol (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction)
    (z : (SourceCoordinate → ℝ) × ℤ) : ℂ := g.toFun (coordinateRotate θ z.2 z.1)

theorem sourcePiSymbol_measurable (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) :
    Measurable (sourcePiSymbol θ g) := by
  apply g.measurable.comp
  apply Measurable.of_eval
  intro i
  unfold coordinateRotate
  fun_prop

theorem sourcePiSymbol_bound (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) (z) :
    ‖sourcePiSymbol θ g z‖ ≤ g.bound :=
  g.norm_le _ (fun _ => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩)

theorem sourcePiSymbol_memLp (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) :
    MemLp (sourcePiSymbol θ g) ∞ (sourceMeasure SourceCoordinate) :=
  memLp_top_of_bound (sourcePiSymbol_measurable θ g).aestronglyMeasurable g.bound
    (Eventually.of_forall (sourcePiSymbol_bound θ g))

def sourcePi (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) :
    SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL (sourceMeasure SourceCoordinate) ∞ 2 2
    ((sourcePiSymbol_memLp θ g).toLp (sourcePiSymbol θ g))

theorem sourcePi_apply_ae (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction)
    (f : SourceHilbert SourceCoordinate) :
    sourcePi θ g f =ᵐ[sourceMeasure SourceCoordinate] fun z => sourcePiSymbol θ g z * f z := by
  have hh := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder
    ((sourcePiSymbol_memLp θ g).toLp (sourcePiSymbol θ g)) f (r := 2)
  filter_upwards [hh, (sourcePiSymbol_memLp θ g).coeFn_toLp] with z hz hg
  simpa [sourcePi, hg] using hz

theorem sourcePi_norm_le (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) :
    ‖sourcePi θ g‖ ≤ g.bound := by
  apply ContinuousLinearMap.opNorm_le_bound _ g.bound_nonneg
  intro f
  have hh : ‖sourcePi θ g f‖ ≤ ‖g.bound • f‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [sourcePi_apply_ae θ g f, Lp.coeFn_smul g.bound f] with z hz hs
    rw [hz, hs, Pi.smul_apply, norm_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg g.bound_nonneg]
    exact mul_le_mul_of_nonneg_right (sourcePiSymbol_bound θ g z) (norm_nonneg _)
  simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg g.bound_nonneg] using hh

/-- Double commutant of a concrete family, including its adjoints. -/
def sourceGeneratedVonNeumann {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : Set (H →L[ℂ] H)) : VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S)
  centralizer_centralizer' := by
    have he : (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S)).carrier =
        Set.centralizer (Set.centralizer (S ∪ star S)) :=
      StarSubalgebra.coe_centralizer_centralizer ℂ S
    rw [he]
    simp

theorem mem_sourceGeneratedVonNeumann {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : Set (H →L[ℂ] H)) {T : H →L[ℂ] H} (hT : T ∈ S) :
    T ∈ sourceGeneratedVonNeumann S := by
  have he : (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S)).carrier =
      Set.centralizer (Set.centralizer (S ∪ star S)) :=
    StarSubalgebra.coe_centralizer_centralizer ℂ S
  change T ∈ (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S)).carrier
  rw [he]
  exact Set.subset_centralizer_centralizer (Or.inl hT)

/-- The actual generated algebra of the source regular representation.
Factor, trace, finiteness and predual properties are separate obligations. -/
def sourceAlgebra (θ : SourceCoordinate → ℝ) : VonNeumannAlgebra (SourceHilbert SourceCoordinate) :=
  sourceGeneratedVonNeumann ({sourceShift SourceCoordinate} ∪ Set.range (sourcePi θ))

theorem sourcePi_mem (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) :
    sourcePi θ g ∈ sourceAlgebra θ :=
  mem_sourceGeneratedVonNeumann _ (Or.inr ⟨g,rfl⟩)

theorem sourceShift_mem (θ : SourceCoordinate → ℝ) :
    sourceShift SourceCoordinate ∈ sourceAlgebra θ :=
  mem_sourceGeneratedVonNeumann _ (Or.inl rfl)

def sourceWeightBase (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) : SourceBaseFunction where
  toFun := fun x => (sourceCocycle θ sourceLogWeight 1 x : ℂ)
  measurable := Complex.measurable_ofReal.comp (sourceCocycle_measurable θ sourceLogWeight 1)
  bound := 1
  bound_nonneg := zero_le_one
  norm_le := by
    intro x hx
    rw [Complex.norm_real, Real.norm_of_nonneg (sourceCocycle_pos _ _ _ _).le]
    exact sourceWeight_le_one θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg hx

theorem sourceMultiplication_eq_pi (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    sourceMultiplication θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg =
      sourcePi θ (sourceWeightBase θ hθ) := rfl

/-- Actual membership of the already verified staged operator in its generated
von Neumann algebra, without an assumed operator-membership hypothesis. -/
theorem staged_sourceOperator_mem (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg ∈ sourceAlgebra θ := by
  change sourceShift SourceCoordinate * sourceMultiplication θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg ∈ _
  rw [sourceMultiplication_eq_pi θ hθ]
  exact mul_mem (sourceShift_mem θ) (sourcePi_mem θ (sourceWeightBase θ hθ))

end
end FiniteFactor

end OAI
