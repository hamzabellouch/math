import OAI.Analysis.KadisonKastler.TracialSequenceIdeal

namespace OAI

/-! # The faithful trace on the tracial sequence quotient -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {B : ℕ → Type*} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]
  (τ : ∀ j, FaithfulTracialState (B j)) (ω : Ultrafilter ℕ)

abbrev TracialSequenceQuotient := (traceNullClosedIdeal τ ω).Quotient

local instance tracialSequenceProductOrder : PartialOrder (VaryingBoundedSequence B) :=
  CStarAlgebra.spectralOrder _
local instance tracialSequenceProductStarOrder : StarOrderedRing (VaryingBoundedSequence B) :=
  CStarAlgebra.spectralOrderedRing _

instance tracialSequenceQuotientCStarAlgebra : CStarAlgebra (TracialSequenceQuotient τ ω) :=
  inferInstanceAs (CStarAlgebra (traceNullClosedIdeal τ ω).Quotient)

def tracialSequenceQuotientMap :
    VaryingBoundedSequence B →⋆ₐ[ℂ] TracialSequenceQuotient τ ω :=
  (traceNullClosedIdeal τ ω).quotientStarHom

theorem tracialSequenceQuotientMap_surjective :
    Function.Surjective (tracialSequenceQuotientMap τ ω) :=
  (traceNullClosedIdeal τ ω).quotientMap_surjective

theorem tracialSequenceQuotientMap_eq_zero_iff (x : VaryingBoundedSequence B) :
    tracialSequenceQuotientMap τ ω x = 0 ↔ TraceNullSequence τ ω x := by
  change (traceNullClosedIdeal τ ω).quotientMap x =
    (traceNullClosedIdeal τ ω).quotientMap 0 ↔ _
  constructor
  · intro h
    have hh := Quotient.exact h
    change TraceNullSequence τ ω (x - 0) at hh
    simpa only [sub_zero] using hh
  · intro h
    apply Quotient.sound
    change TraceNullSequence τ ω (x - 0)
    simpa only [sub_zero] using h

def tracialQuotientLinear : TracialSequenceQuotient τ ω →ₗ[ℂ] ℂ where
  toFun := Quotient.lift (tracialSequenceValue τ ω) (by
    intro x y h
    change TraceNullSequence τ ω (x - y) at h
    have he := tracialSequenceValue_eq_zero_of_null τ ω h
    change tracialSequenceLinear τ ω (x - y) = 0 at he
    rw [map_sub] at he
    exact sub_eq_zero.mp he)
  map_add' x y := by
    obtain ⟨a, rfl⟩ := tracialSequenceQuotientMap_surjective τ ω x
    obtain ⟨b, rfl⟩ := tracialSequenceQuotientMap_surjective τ ω y
    change tracialSequenceValue τ ω (a + b) = _
    exact (tracialSequenceLinear τ ω).map_add a b
  map_smul' c x := by
    obtain ⟨a, rfl⟩ := tracialSequenceQuotientMap_surjective τ ω x
    change tracialSequenceValue τ ω (c • a) = _
    exact (tracialSequenceLinear τ ω).map_smul c a

@[simp] theorem tracialQuotientLinear_map (x : VaryingBoundedSequence B) :
    tracialQuotientLinear τ ω (tracialSequenceQuotientMap τ ω x) =
      tracialSequenceValue τ ω x := rfl

/-- The quotient trace is faithful because exactly the two-null ideal was removed. -/
def tracialQuotientTrace : FaithfulTracialState (TracialSequenceQuotient τ ω) where
  toLinearMap := tracialQuotientLinear τ ω
  map_one := tracialSequenceValue_one τ ω
  positive x := by
    obtain ⟨a, rfl⟩ := tracialSequenceQuotientMap_surjective τ ω x
    rw [← map_star, ← map_mul, tracialQuotientLinear_map]
    exact tracialSequenceValue_positive τ ω a
  positive_im x := by
    obtain ⟨a, rfl⟩ := tracialSequenceQuotientMap_surjective τ ω x
    rw [← map_star, ← map_mul, tracialQuotientLinear_map]
    exact tracialSequenceValue_positive_im τ ω a
  faithful x hx := by
    obtain ⟨a, rfl⟩ := tracialSequenceQuotientMap_surjective τ ω x
    rw [← map_star, ← map_mul, tracialQuotientLinear_map] at hx
    exact (tracialSequenceQuotientMap_eq_zero_iff τ ω a).mpr
      ((tracialSequenceValue_square_eq_zero_iff τ ω a).mp hx)
  tracial x y := by
    obtain ⟨a, rfl⟩ := tracialSequenceQuotientMap_surjective τ ω x
    obtain ⟨b, rfl⟩ := tracialSequenceQuotientMap_surjective τ ω y
    rw [← map_mul, ← map_mul, tracialQuotientLinear_map, tracialQuotientLinear_map]
    exact tracialSequenceValue_tracial τ ω a b

instance tracialSequenceQuotientNontrivial : Nontrivial (TracialSequenceQuotient τ ω) := by
  have hn : (1 : TracialSequenceQuotient τ ω) ≠ 0 := by
    intro h
    have he := (tracialQuotientTrace τ ω).map_one
    rw [h, map_zero] at he
    exact zero_ne_one he
  exact ⟨⟨1, 0, hn⟩⟩

/-- The constructed quotient has the required coordinate trace formula. -/
theorem tracialQuotientTrace_limit (x : VaryingBoundedSequence B) :
    Tendsto (fun j => (τ j).toLinearMap (x j)) (ω : Filter ℕ)
      (𝓝 ((tracialQuotientTrace τ ω).toLinearMap (tracialSequenceQuotientMap τ ω x))) :=
  tendsto_tracialSequenceValue τ ω x

/-- Coordinate two-norms converge to the quotient two-norm. -/
theorem tracialQuotientTwoNorm_limit (x : VaryingBoundedSequence B) :
    Tendsto (fun j => traceTwoNorm (τ j) (x j)) (ω : Filter ℕ)
      (𝓝 (traceTwoNorm (tracialQuotientTrace τ ω) (tracialSequenceQuotientMap τ ω x))) := by
  have ht := (Real.continuous_sqrt.tendsto _).comp
    ((Complex.continuous_re.tendsto _).comp (tracialQuotientTrace_limit τ ω (star x * x)))
  simpa only [Function.comp_def, traceTwoNorm, lp.infty_coeFn_mul, lp.coeFn_star,
    Pi.mul_apply, Pi.star_apply, map_mul, map_star] using ht

end

end KadisonKastler

end OAI
