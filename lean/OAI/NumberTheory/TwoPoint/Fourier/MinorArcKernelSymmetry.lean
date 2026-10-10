import OAI.NumberTheory.TwoPoint.Fourier.MinorArcGeometric

namespace OAI

/-! Positivity and reflection symmetry of the resonant-safe geometric kernel. -/

namespace TwoPointCorrelations

open Complex
open scoped ComplexConjugate

lemma minor_arc_geometric_nonneg {L : ℝ} (hL : 0 ≤ L) (α : ℝ) :
    0 ≤ minorArcGeometricBound L α := by
  unfold minorArcGeometricBound
  split_ifs
  · exact hL
  · exact le_min hL (by positivity)

lemma minor_arc_character_neg (α : ℝ) (n : ℕ) :
    additiveCharacter (-α) n = conj (additiveCharacter α n) := by
  simp only [additiveCharacter, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

lemma minor_arc_geometric_neg (L α : ℝ) :
    minorArcGeometricBound L (-α) = minorArcGeometricBound L α := by
  have hc : conj (additiveCharacter α 1) = 1 ↔ additiveCharacter α 1 = 1 := by
    constructor
    · intro h
      have he := congrArg conj h
      simpa only [map_one, conj_conj] using he
    · intro h
      rw [h, map_one]
  unfold minorArcGeometricBound
  rw [minor_arc_character_neg]
  by_cases h : additiveCharacter α 1 = 1
  · rw [ite_eq_left (hc.mpr h), ite_eq_left h]
  · rw [ite_eq_right ((not_congr hc).mpr h), ite_eq_right h]
    have he : conj (additiveCharacter α 1) - 1 = conj (additiveCharacter α 1 - 1) := by
      rw [map_sub, map_one]
    rw [he, norm_conj]

lemma minor_arc_geometric_natAbs (L α : ℝ) (n : ℤ) :
    minorArcGeometricBound L ((n.natAbs : ℝ) * α) =
      minorArcGeometricBound L ((n : ℝ) * α) := by
  have he : (n.natAbs : ℝ) = |(n : ℝ)| := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs n)
    simpa only [Int.cast_natCast, Int.cast_abs] using h
  rw [he]
  by_cases hn : (0 : ℝ) ≤ n
  · rw [abs_of_nonneg hn]
  · rw [abs_of_neg (lt_of_not_ge hn), neg_mul, minor_arc_geometric_neg]

end TwoPointCorrelations

end OAI
