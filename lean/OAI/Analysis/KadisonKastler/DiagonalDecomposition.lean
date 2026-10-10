import OAI.Analysis.KadisonKastler.DiagonalLocalVectors
import OAI.Analysis.KadisonKastler.VectorCoreField

namespace OAI

/-! # The real-line diagonal-commutant decomposition

The local representatives determine a bounded operator on the rational
core at almost every point. The pointwise difference bound then proves
that the resulting field represents the original operator on every
L2 vector, without choosing an uncountable common conull set.
-/

namespace KadisonKastler

open MeasureTheory Filter TopologicalSpace

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [SeparableSpace H]

theorem exists_diagonalField_of_commute_indicators
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ (s : Set ℝ) (hs : MeasurableSet s),
      Commute T (regularIndicatorProjection s hs)) :
    ∃ F : ℝ → H →L[ℂ] H,
      (∀ ξ, AEStronglyMeasurable (fun t => F t ξ) volume) ∧
      (∀ t, ‖F t‖ ≤ ‖T‖) ∧ RepresentsOperatorField volume F T := by
  let C : RationalComplexCore H := Classical.choice (exists_rationalComplexCore H)
  let : Countable C.space := C.countable
  let g : C.space → ℝ → H := fun ξ => diagonalRawVector T (ξ : H)
  have hg : ∀ᵐ t : ℝ, CoherentVectorCore C ‖T‖ (fun ξ => g ξ t) := by
    apply coherentVectorCore_ae
    · intro ξ η
      exact diagonalRawVector_add_ae T ξ η
    · intro r ξ
      simpa only [g, Submodule.coe_smul, ← Rat.cast_smul_eq_qsmul ℂ] using
        diagonalRawVector_smul_ae T (r : ℂ) ξ
    · intro ξ
      exact diagonalRawVector_smul_ae T Complex.I ξ
    · exact fun ξ => diagonalRawVector_norm_ae T hT ξ
  obtain ⟨F, hFm, hFn, hFcore⟩ := exists_field_of_vectorCore C ‖T‖ g
    (norm_nonneg _) (fun ξ => diagonalRawVector_measurable T ξ) hg
  refine ⟨F, hFm, hFn, ?_⟩
  intro f
  have hbound (ξ : C.space) : ∀ᵐ t : ℝ,
      ‖T f t - F t (ξ : H)‖ ≤ ‖T‖ * ‖f t - (ξ : H)‖ := by
    have hall : ∀ᵐ t : ℝ, ∀ n : ℕ,
        ‖T f t - T (diagonalTestVector n (ξ : H)) t‖ ≤
          ‖T‖ * ‖f t - diagonalTestVector n (ξ : H) t‖ :=
      ae_all_iff.mpr fun n => ae_norm_apply_sub_le_of_commute_indicators T hT f _
    have hvec : ∀ᵐ t : ℝ, ∀ n : ℕ,
        diagonalTestVector n (ξ : H) t =
          (Set.Icc (-(n : ℝ)) (n : ℝ)).indicator (fun _ => (ξ : H)) t :=
      ae_all_iff.mpr fun n => diagonalTestVector_ae n (ξ : H)
    filter_upwards [hall, hvec, hFcore ξ] with t ht hξ hFt
    rw [hFt]
    have hmem : t ∈ Set.Icc (-(Nat.ceil |t| : ℝ)) (Nat.ceil |t| : ℝ) :=
      Set.mem_Icc.mpr (abs_le.mp (Nat.le_ceil |t|))
    simpa only [g, diagonalRawVector, hξ, Set.indicator_of_mem hmem] using
      ht (Nat.ceil |t|)
  filter_upwards [ae_all_iff.mpr hbound] with t ht
  have hclosed : IsClosed {ξ : H | ‖T f t - F t ξ‖ ≤ ‖T‖ * ‖f t - ξ‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hpoint : ‖T f t - F t (f t)‖ ≤ ‖T‖ * ‖f t - f t‖ :=
    isClosed_property C.dense.denseRange_val hclosed ht (f t)
  simp only [sub_self, norm_zero, mul_zero] at hpoint
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hpoint (norm_nonneg _)))

/-- Blackadar III.1.6.2--3, for the exact constant Hilbert field over
Lebesgue measure required by the regular-core argument. -/
theorem publishedRealDiagonalDecomposition : PublishedRealDiagonalDecomposition.{u} := by
  intro H _ _ _ _ T hT
  obtain ⟨F, hm, hn, hF⟩ := exists_diagonalField_of_commute_indicators T
    (commute_indicators_of_commute_scalarMultipliers T hT)
  exact ⟨F, hm, Eventually.of_forall hn, hF⟩

end

end KadisonKastler

end OAI
