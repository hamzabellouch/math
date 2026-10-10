import OAI.Computability.PerfectCompleteness.Foundations.ManyGoodRowsLemmas
import OAI.Computability.PerfectCompleteness.Foundations.RecursiveSpaceEquivLemmas
import OAI.Computability.PerfectCompleteness.Sampling.CutSamplerReplayTransportLemmas

namespace OAI

section

namespace PerfectCompleteness.GoodRowSampling

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters (F2)
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open PerfectCompleteness.ManyGoodRows

attribute [local instance] linearMapFintype

variable {E F Y : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype E] [Fintype F] [Fintype Y]

abbrev RowFiber {r : Nat} (A : RowMap F r) (U : E →ₗ[F2] (Fin r → F2)) :=
  {X : E →ₗ[F2] F // A.comp X = U}

def rowFiberEquiv {r : Nat} (A : RowMap F r) (U : E →ₗ[F2] (Fin r → F2))
    (T : E →ₗ[F2] F) (hT : A.comp T = U) :
    MatrixSlice.Slice (⊥ : Submodule F2 E) (LinearMap.ker A) T ≃ RowFiber A U where
  toFun X := ⟨X.val, (RowAdvice.slice_row_eq ⊥ A T X).trans hT⟩
  invFun X := ⟨X.val, by
    apply LinearMap.ext
    intro x
    have hx : (x : E) = 0 := (Submodule.mem_bot F2).mp x.property
    simp [hx], (RowAdvice.comp_eq_iff_ker_quotient A X.val T).mp (X.property.trans hT.symm)⟩
  left_inv X := by apply Subtype.ext; rfl
  right_inv X := by apply Subtype.ext; rfl

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype E] [Fintype F] in
@[simp] theorem rowFiberEquiv_val {r : Nat} (A : RowMap F r)
    (U : E →ₗ[F2] (Fin r → F2)) (T : E →ₗ[F2] F) (hT : A.comp T = U)
    (X : MatrixSlice.Slice (⊥ : Submodule F2 E) (LinearMap.ker A) T) :
    (rowFiberEquiv A U T hT X).val = X.val := rfl

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype Y] in
theorem witness_rowFiber_nonempty {f : (E →ₗ[F2] F) → Option Y}
    {r : Nat} {ρ : ℝ} {A : RowMap F r} {U : E →ₗ[F2] (Fin r → F2)}
    (w : Witness f r ρ A U) : Nonempty (RowFiber A U) :=
  ⟨⟨w.base, w.row_value⟩⟩

omit [Fintype Y] in
theorem witness_column_probability {f : (E →ₗ[F2] F) → Option Y}
    {r : Nat} {ρ : ℝ} {A : RowMap F r} {U : E →ₗ[F2] (Fin r → F2)}
    (w : Witness f r ρ A U) :
    letI : Nonempty (RowFiber A U) := witness_rowFiber_nonempty w
    1 / (2 : ℝ) ^ (r * Module.finrank F2 F) ≤
      (FiniteDistribution.uniform (RowFiber A U)).probability
        (fun X => decide (X.val.domRestrict w.columnSpace = w.base.domRestrict w.columnSpace)) := by
  let : Nonempty (RowFiber A U) := witness_rowFiber_nonempty w
  have h := SliceMass.probability_columnConstraint_ge_of_finrank_le
    w.columnSpace (LinearMap.ker A) w.base r w.column_count
  have he := UniformConditioning.uniform_probability_equiv
    (rowFiberEquiv A U w.base w.row_value)
    (fun X : RowFiber A U =>
      decide (X.val.domRestrict w.columnSpace = w.base.domRestrict w.columnSpace))
  apply h.trans_eq
  refine Eq.trans ?_ he
  congr 1
  funext X
  exact decide_eq_decide.mpr Iff.rfl

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype Y] in
theorem witness_row_probability_pos {f : (E →ₗ[F2] F) → Option Y}
    {r : Nat} {ρ : ℝ} {A : RowMap F r} {U : E →ₗ[F2] (Fin r → F2)}
    (w : Witness f r ρ A U) :
    0 < (FiniteDistribution.uniform (E →ₗ[F2] F)).probability
      (fun X => decide (A.comp X = U)) := by
  let : Nonempty (RowFiber A U) := witness_rowFiber_nonempty w
  apply lt_of_lt_of_eq
    (UniformConditioning.uniform_probability_pos (fun X : E →ₗ[F2] F => A.comp X = U))
  congr 1
  funext X
  exact decide_eq_decide.mpr Iff.rfl

omit [Fintype Y] in
theorem witness_conditional_probability {f : (E →ₗ[F2] F) → Option Y}
    {r : Nat} {ρ : ℝ} {A : RowMap F r} {U : E →ₗ[F2] (Fin r → F2)}
    (w : Witness f r ρ A U) :
    1 / (2 : ℝ) ^ (r * Module.finrank F2 F) ≤
      ((FiniteDistribution.uniform (E →ₗ[F2] F)).condition
        (fun X => decide (A.comp X = U)) (witness_row_probability_pos w)).probability
        (fun X => decide (X.domRestrict w.columnSpace = w.base.domRestrict w.columnSpace)) := by
  let : Nonempty (RowFiber A U) := witness_rowFiber_nonempty w
  have hevent : (fun X : E →ₗ[F2] F => decide (A.comp X = U)) =
      (fun X : E →ₗ[F2] F => @decide (A.comp X = U) (Classical.propDecidable _)) := by
    funext X
    exact decide_eq_decide.mpr Iff.rfl
  simp only [hevent, UniformConditioning.probability_condition_uniform]
  convert witness_column_probability w using 1
  congr!

end
end PerfectCompleteness.GoodRowSampling

end

end OAI
