import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientValue

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

theorem scaled_cauchyValue_add (c : ℂ)
    (hlinear : ∀ x y : D, c * T.complexValue (x+y) = c*T.complexValue x+c*T.complexValue y)
    (u v : T.cauchySequenceAlgebra hadd) :
    c * T.cauchyValue hadd hsqrt (u+v) = c*T.cauchyValue hadd hsqrt u+c*T.cauchyValue hadd hsqrt v := by
  have hl := (T.cauchyValue_tendsto hadd hsqrt (u+v)).const_mul c
  have hr := ((T.cauchyValue_tendsto hadd hsqrt u).const_mul c).add
    ((T.cauchyValue_tendsto hadd hsqrt v).const_mul c)
  have he (n : ℕ) : c*T.complexValue ((u+v).1 n) =
      c*T.complexValue (u.1 n)+c*T.complexValue (v.1 n) := hlinear _ _
  simp only [he] at hl
  exact tendsto_nhds_unique hl hr

theorem scaled_quotientValue_add (c : ℂ)
    (hlinear : ∀ x y : D, c*T.complexValue (x+y) = c*T.complexValue x+c*T.complexValue y)
    (x y : T.CauchyQuotient hadd) :
    c*T.quotientValue hadd hsqrt (x+y) = c*T.quotientValue hadd hsqrt x+c*T.quotientValue hadd hsqrt y := by
  obtain ⟨u, rfl⟩ := T.cauchyQuotientMap_surjective hadd x
  obtain ⟨v, rfl⟩ := T.cauchyQuotientMap_surjective hadd y
  rw [← map_add, T.quotientValue_map, T.quotientValue_map, T.quotientValue_map]
  exact T.scaled_cauchyValue_add hadd hsqrt c hlinear u v

theorem scaled_quotientValue_add_iff (c : ℂ) :
    (∀ x y : T.CauchyQuotient hadd,
      c*T.quotientValue hadd hsqrt (x+y) = c*T.quotientValue hadd hsqrt x+c*T.quotientValue hadd hsqrt y) ↔
    (∀ x y : D, c*T.complexValue (x+y) = c*T.complexValue x+c*T.complexValue y) := by
  constructor
  · intro h x y
    have he := h (T.quotientEmbedding hadd x) (T.quotientEmbedding hadd y)
    rwa [← map_add, T.quotientValue_embedding, T.quotientValue_embedding, T.quotientValue_embedding] at he
  · exact T.scaled_quotientValue_add hadd hsqrt c
end CuntzPureness.PositiveQuasitrace

end

end OAI
