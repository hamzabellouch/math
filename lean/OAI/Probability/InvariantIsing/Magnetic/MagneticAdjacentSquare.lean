import OAI.Probability.InvariantIsing.Magnetic.MagneticPrefixComparison

namespace OAI

/-! The conditional square means preceding a transferred variance
increment decrease at fixed total mean spin. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

theorem magneticClosedSquare_adjacent_transfer (P L : List (ℝ × ℝ≥0))
    (hP : ∀ av ∈ P, 0 < av.1) (hP1 : ∀ av ∈ P, av.1 ≤ 1)
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (x δ y : ℝ≥0)
    (hN : ∀ av ∈ P ++ (a, x + δ) :: (b, y) :: L, 0 < av.1)
    (hO : ∀ av ∈ P ++ (a, x) :: (b, δ + y) :: L, 0 < av.1)
    (i : ℕ) (hi : i ≤ P.length) {ζ v s : ℝ}
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hv : 0 ≤ v) (hs : s ∈ Icc (-1 : ℝ) 1) :
    closedMagneticContinuation (P ++ (a, x + δ) :: (b, y) :: L)
      (magneticScalarSquareFourJet _ hN
        ⟨i, by simp only [List.length_append, List.length_cons]; omega⟩).toMagneticContinuationJet
        ζ (v, s) ≤
    closedMagneticContinuation (P ++ (a, x) :: (b, δ + y) :: L)
      (magneticScalarSquareFourJet _ hO
        ⟨i, by simp only [List.length_append, List.length_cons]; omega⟩).toMagneticContinuationJet
        ζ (v, s) := by
  let N := (a, x + δ) :: (b, y) :: L
  let O := (a, x) :: (b, δ + y) :: L
  have hNT : ∀ av ∈ N, 0 < av.1 := fun av hav => hN av (List.mem_append_right P hav)
  have hOT : ∀ av ∈ O, 0 < av.1 := fun av hav => hO av (List.mem_append_right P hav)
  have hNT1 : ∀ av ∈ N, av.1 ≤ 1 := by
    intro av hav
    rcases List.mem_cons.mp hav with rfl | hav
    · exact hab.trans hb1
    · rcases List.mem_cons.mp hav with rfl | hav
      · exact hb1
      · exact hL1 av hav
  have hOT1 : ∀ av ∈ O, av.1 ≤ 1 := by
    intro av hav
    rcases List.mem_cons.mp hav with rfl | hav
    · exact hab.trans hb1
    · rcases List.mem_cons.mp hav with rfl | hav
      · exact hb1
      · exact hL1 av hav
  have hinit (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
      closedMagneticScalarCurvature N hNT 0 (0, u) ≤
        closedMagneticScalarCurvature O hOT 0 (0, u) :=
    magneticClosedCurvature_adjacent_transfer L hL hL1 ha hab hb1 x δ y
      (le_refl 0) (by norm_num) (le_refl 0) hu
  exact magneticClosedSquare_append_mono P N O hP hP1 hNT hNT1 hOT hOT1 hinit i hi
    hζ hζ1 hv hs

end InvariantIsing

end

end OAI
