import OAI.Analysis.MarkovType.OrderedNorm
import OAI.Analysis.MarkovType.FinitelyRepresentable

namespace OAI

namespace MarkovSuperreflexivity

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem CoordinatesRepresentable.transfer {N : OrderedNorm}
    (hNY : CoordinatesRepresentable Y N) (hYX : FinitelyRepresentable Y X) :
    CoordinatesRepresentable X N := by
  intro m ε hε
  let δ : ℝ := min (ε / 3) 1
  have hδ : 0 < δ := lt_min (by linarith) zero_lt_one
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : δ ≤ ε / 3 := min_le_left _ _
  have hfactor : (1 + δ) * (1 + δ) ≤ 1 + ε := by
    have hsquare : δ * δ ≤ δ := by nlinarith
    nlinarith
  obtain ⟨T, hT⟩ := hNY m δ hδ
  let E : Submodule ℝ Y := LinearMap.range T
  let : FiniteDimensional ℝ E := LinearMap.finiteDimensional_range T
  obtain ⟨S, hS⟩ := hYX E δ hδ
  refine ⟨S.comp T.rangeRestrict, ?_⟩
  intro a
  have hnorm : ‖T.rangeRestrict a‖ = ‖T a‖ := rfl
  constructor
  · exact (hT a).1.trans (by simpa only [LinearMap.comp_apply, hnorm] using (hS (T.rangeRestrict a)).1)
  · calc
      ‖(S.comp T.rangeRestrict) a‖ ≤ (1 + δ) * ‖T.rangeRestrict a‖ :=
        (hS (T.rangeRestrict a)).2
      _ = (1 + δ) * ‖T a‖ := by rw [hnorm]
      _ ≤ (1 + δ) * ((1 + δ) * N (C00.ofArray a)) :=
        mul_le_mul_of_nonneg_left (hT a).2 (by linarith)
      _ = ((1 + δ) * (1 + δ)) * N (C00.ofArray a) :=
        (mul_assoc _ _ _).symm
      _ ≤ (1 + ε) * N (C00.ofArray a) :=
        mul_le_mul_of_nonneg_right hfactor (N.nonneg _)

end MarkovSuperreflexivity

end OAI
