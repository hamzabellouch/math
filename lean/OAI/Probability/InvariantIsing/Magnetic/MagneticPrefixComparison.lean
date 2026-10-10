import OAI.Probability.InvariantIsing.Magnetic.MagneticAdjacentCurvature
import OAI.Probability.InvariantIsing.Magnetic.MagneticSquareInitial

namespace OAI

/-! A common finite prefix preserves inverse-curvature order and the
associated conditional-square order up to the end of that prefix. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

private lemma positive_append (P L : List (ℝ × ℝ≥0))
    (hP : ∀ av ∈ P, 0 < av.1) (hL : ∀ av ∈ L, 0 < av.1) :
    ∀ av ∈ P ++ L, 0 < av.1 := by
  intro av hav
  rcases List.mem_append.mp hav with hp | hl
  · exact hP av hp
  · exact hL av hl

private lemma upper_append (P L : List (ℝ × ℝ≥0))
    (hP : ∀ av ∈ P, av.1 ≤ 1) (hL : ∀ av ∈ L, av.1 ≤ 1) :
    ∀ av ∈ P ++ L, av.1 ≤ 1 := by
  intro av hav
  rcases List.mem_append.mp hav with hp | hl
  · exact hP av hp
  · exact hL av hl

theorem magneticClosedCurvature_append_mono (P L M : List (ℝ × ℝ≥0))
    (hP : ∀ av ∈ P, 0 < av.1) (hP1 : ∀ av ∈ P, av.1 ≤ 1)
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    (hM : ∀ av ∈ M, 0 < av.1) (hM1 : ∀ av ∈ M, av.1 ≤ 1)
    (hinit : ∀ u ∈ Icc (-1 : ℝ) 1,
      closedMagneticScalarCurvature L hL 0 (0, u) ≤
        closedMagneticScalarCurvature M hM 0 (0, u))
    {ζ v s : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hv : 0 ≤ v) (hs : s ∈ Icc (-1 : ℝ) 1) :
    closedMagneticScalarCurvature (P ++ L) (positive_append P L hP hL) ζ (v, s) ≤
      closedMagneticScalarCurvature (P ++ M) (positive_append P M hP hM) ζ (v, s) := by
  induction P generalizing ζ v s with
  | nil =>
    apply magneticClosedCurvature_compare_initial L M hL hM hL1 hM1 hζ le_rfl hζ1 ?_ hv hs
    intro u hu
    rw [closedMagneticScalarCurvature_initial L hL ζ 0 u,
      closedMagneticScalarCurvature_initial M hM ζ 0 u]
    exact hinit u hu
  | cons av P ih =>
    apply magneticClosedCurvature_compare_initial (av :: P ++ L) (av :: P ++ M)
      (positive_append _ _ hP hL) (positive_append _ _ hP hM)
      (upper_append _ _ hP1 hL1) (upper_append _ _ hP1 hM1) hζ le_rfl hζ1 ?_ hv hs
    intro u hu
    simp only [List.cons_append]
    rw [closedMagneticScalarCurvature_cons_initial,
      closedMagneticScalarCurvature_cons_initial]
    exact ih (fun bv hb => hP bv (List.mem_cons_of_mem av hb))
      (fun bv hb => hP1 bv (List.mem_cons_of_mem av hb))
      (hP av List.mem_cons_self).le (hP1 av List.mem_cons_self) av.2.property hu

theorem magneticClosedSquare_append_mono (P L M : List (ℝ × ℝ≥0))
    (hP : ∀ av ∈ P, 0 < av.1) (hP1 : ∀ av ∈ P, av.1 ≤ 1)
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    (hM : ∀ av ∈ M, 0 < av.1) (hM1 : ∀ av ∈ M, av.1 ≤ 1)
    (hinit : ∀ u ∈ Icc (-1 : ℝ) 1,
      closedMagneticScalarCurvature L hL 0 (0, u) ≤
        closedMagneticScalarCurvature M hM 0 (0, u))
    (i : ℕ) (hi : i ≤ P.length) {ζ v s : ℝ}
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hv : 0 ≤ v) (hs : s ∈ Icc (-1 : ℝ) 1) :
    closedMagneticContinuation (P ++ L)
      (magneticScalarSquareFourJet (P ++ L) (positive_append P L hP hL)
        ⟨i, by simp only [List.length_append]; omega⟩).toMagneticContinuationJet ζ (v, s) ≤
    closedMagneticContinuation (P ++ M)
      (magneticScalarSquareFourJet (P ++ M) (positive_append P M hP hM)
        ⟨i, by simp only [List.length_append]; omega⟩).toMagneticContinuationJet ζ (v, s) := by
  induction P generalizing i ζ v s with
  | nil =>
    have hi0 : i = 0 := by simpa using hi
    subst i
    apply magneticClosedSquare_compare_initial L M hL hM hL1 hM1 0 0 hζ hζ1 ?_ ?_ hv hs
    · intro u hu
      rw [closedMagneticScalarCurvature_initial L hL ζ 0 u,
        closedMagneticScalarCurvature_initial M hM ζ 0 u]
      exact hinit u hu
    · intro u hu
      rw [closedMagneticSquareContinuation_zero_initial L hL hζ hu,
        closedMagneticSquareContinuation_zero_initial M hM hζ hu]
  | cons av P ih =>
    apply magneticClosedSquare_compare_initial (av :: P ++ L) (av :: P ++ M)
      (positive_append _ _ hP hL) (positive_append _ _ hP hM)
      (upper_append _ _ hP1 hL1) (upper_append _ _ hP1 hM1) _ _ hζ hζ1 ?_ ?_ hv hs
    · intro u hu
      exact magneticClosedCurvature_append_mono (av :: P) L M hP hP1 hL hL1 hM hM1
        hinit hζ hζ1 (le_refl 0) hu
    · intro u hu
      simp only [List.cons_append]
      cases i with
      | zero =>
        exact (closedMagneticSquareContinuation_zero_initial (av :: P ++ L)
          (positive_append _ _ hP hL) hζ hu).le.trans
          (closedMagneticSquareContinuation_zero_initial (av :: P ++ M)
            (positive_append _ _ hP hM) hζ hu).ge
      | succ i =>
        have hiP : i ≤ P.length := by simpa only [List.length_cons] using Nat.le_of_succ_le_succ hi
        have heL : (⟨i + 1, by simp only [List.length_cons, List.length_append]; omega⟩ :
            Fin ((av :: P ++ L).length + 1)) =
            (⟨i, by simp only [List.length_append]; omega⟩ : Fin ((P ++ L).length + 1)).succ := rfl
        have heM : (⟨i + 1, by simp only [List.length_cons, List.length_append]; omega⟩ :
            Fin ((av :: P ++ M).length + 1)) =
            (⟨i, by simp only [List.length_append]; omega⟩ : Fin ((P ++ M).length + 1)).succ := rfl
        rw [heL, heM, closedMagneticSquareContinuation_cons_initial,
          closedMagneticSquareContinuation_cons_initial]
        exact ih (fun bv hb => hP bv (List.mem_cons_of_mem av hb))
          (fun bv hb => hP1 bv (List.mem_cons_of_mem av hb)) i hiP
          (hP av List.mem_cons_self).le (hP1 av List.mem_cons_self) av.2.property hu

end InvariantIsing

end

end OAI
