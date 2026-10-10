import OAI.Analysis.TracialSplitting.Main

namespace OAI

/-! The construction certificates are proved here, outside the self-contained challenge.
`main_iff_original` checks that packaging them preserves the original assertion. -/

universe uNuclear

namespace CurrentMain

open Pureness Filter

def OriginalGammaStatement : Prop := ∀
    {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [Nontrivial A] [TopologicalSpace.SeparableSpace A]
    (_hsimple : TopologicallySimple A) (_hinf : ¬FiniteDimensional ℂ A)
    (_hA : IsNuclear.{0, uNuclear} A) (_hfinite : StablyFinite A)
    [Nonempty (TracialState A)] (U : Ultrafilter ℕ)
    (_hfree : (U : Filter ℕ) ≤ atTop)
    (_hRR : RealRankZero (FamilyUltrapower (completionTrace (fun τ : TracialState A => τ)) U)),
    UniformPropertyGammaAt A U
end CurrentMain

namespace ComparatorModel.CurrentMain

noncomputable section

open Filter

local instance canonicalNorm : Pureness.ClosedStarIdeal.NormConstruction where
  mul_le := by intros; apply _root_.OAI.Pureness.ClosedStarIdeal.quotient_norm_mul_le
  star_eq := by intros; apply _root_.OAI.Pureness.ClosedStarIdeal.quotient_norm_star
  square_le := by intros; apply _root_.OAI.Pureness.ClosedStarIdeal.quotient_norm_square_le

local instance canonicalNull : NullConstruction where
  zero := by intros; apply _root_.OAI.CurrentMain.isFamilyNull_zero
  add := by intros; apply _root_.OAI.CurrentMain.isFamilyNull_add <;> assumption
  neg := by intros; apply _root_.OAI.CurrentMain.isFamilyNull_neg; assumption
  star := by intros; apply _root_.OAI.CurrentMain.isFamilyNull_star; assumption
  mul_left := by intros; apply _root_.OAI.CurrentMain.isFamilyNull_mul_left <;> assumption
  mul_right := by intros; apply _root_.OAI.CurrentMain.isFamilyNull_mul_right <;> assumption
  closed := by intros; apply _root_.OAI.CurrentMain.familyNull_isClosed

local instance canonicalCauchy : CauchyConstruction where
  const := by intros; apply _root_.OAI.CurrentMain.isFamilyCauchy_const
  add := by intros; apply _root_.OAI.CurrentMain.isFamilyCauchy_add <;> assumption
  star := by intros; apply _root_.OAI.CurrentMain.isFamilyCauchy_star; assumption
  mul := by intros; apply _root_.OAI.CurrentMain.isFamilyCauchy_mul <;> assumption
  closed := by intros; apply _root_.OAI.CurrentMain.familyCauchyAlgebra_isClosed

local instance canonicalLimit : LimitConstruction where
  tendsto := by intros; apply _root_.OAI.CurrentMain.ultraTraceValue_tendsto

local instance canonicalTrace : TraceConstruction where
  null := by
    intro D I X _ _ _ _ τ _ U s u hu
    apply _root_.OAI.CurrentMain.ultraTrace_null τ U s u
    exact (_root_.OAI.CurrentMain.familyNull_mem τ (U : Filter X) u).mpr hu

/-- The asserted conclusion, including all hypotheses, is definitionally unchanged. -/
theorem statement_iff_original : Statement.{uNuclear} ↔
    _root_.OAI.CurrentMain.OriginalGammaStatement.{uNuclear} := Iff.rfl

/-- The existential construction requirements do not change the original assertion. -/
theorem main_iff_original : MainClaim.{uNuclear} ↔
    _root_.OAI.CurrentMain.OriginalGammaStatement.{uNuclear} := by
  constructor
  · rintro ⟨_, _, _, _, _, h⟩
    exact statement_iff_original.mp h
  · intro h
    exact ⟨canonicalNorm, canonicalNull, canonicalCauchy, canonicalLimit, canonicalTrace,
      statement_iff_original.mpr h⟩

theorem main : MainClaim.{uNuclear} :=
  main_iff_original.mpr @_root_.OAI.CurrentMain.real_rank_zero_uniform_gamma

end

end ComparatorModel.CurrentMain

end OAI
