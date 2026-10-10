import Mathlib

namespace OAI

/-! # A positive sublevel set stays a definite distance below its endpoint -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {Ω : Type*} [MeasurableSpace Ω]

theorem exists_smaller_sublevel_nonzero (μ : Measure Ω) (f : Ω → ℝ) {q : ℝ}
    (hpos : μ {z | f z<q}≠0) :
    ∃ S : ℝ, S<q ∧ μ {z | f z<S}≠0 := by
  by_contra h
  have hz (S : ℝ) (hS : S<q) : μ {z | f z<S}=0 :=
    Classical.byContradiction fun hn => h ⟨S,hS,hn⟩
  have he : {z | f z<q}=⋃ n : ℕ, {z | f z<q-1/((n:ℝ)+1)} := by
    ext z
    constructor
    · intro hq
      obtain ⟨n,hn⟩ := exists_nat_one_div_lt (show (0:ℝ)<q-f z from sub_pos.mpr hq)
      exact mem_iUnion.mpr ⟨n,by dsimp only [mem_ofPred_eq]; linarith⟩
    · intro hq
      obtain ⟨n,hn⟩ := mem_iUnion.mp hq
      have hp : 0<1/((n:ℝ)+1) := by positivity
      dsimp only [mem_ofPred_eq] at hn ⊢
      linarith
  apply hpos
  rw [he,measure_iUnion_null_iff]
  intro n
  apply hz
  have hp : 0<1/((n:ℝ)+1) := by positivity
  linarith

theorem smaller_sublevel_above_ae_lower_bound (μ : Measure Ω) {f : Ω → ℝ} {T S : ℝ}
    (hT : ∀ᵐ z ∂μ, T≤f z) (hS : μ {z | f z<S}≠0) : T<S := by
  by_contra h
  have he : ∀ᵐ z ∂μ, ¬f z<S := hT.mono fun z hz => not_lt.mpr ((le_of_not_gt h).trans hz)
  exact hS (by simpa only [not_not] using ae_iff.mp he)

end RegularPointCoordinates

end

end OAI
