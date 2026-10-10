import OAI.Probability.InvariantIsing.Magnetic.MagneticAdjacentSquare
import OAI.Probability.InvariantIsing.Magnetic.MagneticTerminalCongruence

namespace OAI

/-! Increasing the final covariance height decreases each preceding
conditional square at fixed total magnetization. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

private lemma square_congr_list {L M : List (ℝ × ℝ≥0)} (he : L = M)
    (hL : ∀ av ∈ L, 0 < av.1) (hM : ∀ av ∈ M, 0 < av.1)
    (i : Fin (L.length + 1)) (j : Fin (M.length + 1)) (hij : i.val = j.val)
    (ζ : ℝ) (p : ℝ × ℝ) :
    closedMagneticContinuation L
      (magneticScalarSquareFourJet L hL i).toMagneticContinuationJet ζ p =
    closedMagneticContinuation M
      (magneticScalarSquareFourJet M hM j).toMagneticContinuationJet ζ p := by
  subst M
  have hj : i = j := Fin.ext hij
  subst j
  rfl

theorem magneticClosedSquare_terminal_variance_mono (P : List (ℝ × ℝ≥0))
    (hP : ∀ av ∈ P, 0 < av.1) (hP1 : ∀ av ∈ P, av.1 ≤ 1)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (x δ : ℝ≥0)
    (hN : ∀ av ∈ P ++ [(a, x + δ)], 0 < av.1)
    (hO : ∀ av ∈ P ++ [(a, x)], 0 < av.1)
    (i : ℕ) (hi : i ≤ P.length) {ζ v s : ℝ}
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hv : 0 ≤ v) (hs : s ∈ Icc (-1 : ℝ) 1) :
    closedMagneticContinuation (P ++ [(a, x + δ)])
      (magneticScalarSquareFourJet _ hN
        ⟨i, by simp only [List.length_append, List.length_singleton]; omega⟩).toMagneticContinuationJet
        ζ (v, s) ≤
    closedMagneticContinuation (P ++ [(a, x)])
      (magneticScalarSquareFourJet _ hO
        ⟨i, by simp only [List.length_append, List.length_singleton]; omega⟩).toMagneticContinuationJet
        ζ (v, s) := by
  have hn : ∀ av ∈ P ++ (a, x + δ) :: (1, (0 : ℝ≥0)) :: [], 0 < av.1 := by
    intro av hav
    rcases List.mem_append.mp hav with hp | ht
    · exact hP av hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact ha
      · norm_num
  have ho : ∀ av ∈ P ++ (a, x) :: (1, δ + 0) :: [], 0 < av.1 := by
    intro av hav
    rcases List.mem_append.mp hav with hp | ht
    · exact hP av hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact ha
      · norm_num
  have h := magneticClosedSquare_adjacent_transfer P [] hP hP1 (by simp) (by simp)
    ha ha1 (le_refl 1) x δ 0 hn ho i hi hζ hζ1 hv hs
  have hn' : ∀ av ∈ (P ++ [(a, x + δ)]) ++ [(1, (0 : ℝ≥0))], 0 < av.1 := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hn
  have ho' : ∀ av ∈ (P ++ [(a, x)]) ++ [(1, δ)], 0 < av.1 := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append, add_zero] using ho
  have hni : i ≤ (P ++ [(a, x + δ)]).length := by
    simp only [List.length_append, List.length_singleton]
    omega
  have hoi : i ≤ (P ++ [(a, x)]).length := by
    simp only [List.length_append, List.length_singleton]
    omega
  have en := closedMagneticSquare_terminal_one (P ++ [(a, x + δ)]) hN 0 hn' i hni ζ (v, s)
  have eo := closedMagneticSquare_terminal_one (P ++ [(a, x)]) hO δ ho' i hoi ζ (v, s)
  have enC := square_congr_list
    (show (P ++ [(a, x + δ)]) ++ [(1, (0 : ℝ≥0))] =
      P ++ (a, x + δ) :: (1, (0 : ℝ≥0)) :: [] by simp only [List.append_assoc,
        List.cons_append, List.nil_append]) hn' hn
    ⟨i, by simp only [List.length_append, List.length_singleton]; omega⟩
    ⟨i, by simp only [List.length_append, List.length_cons, List.length_nil]; omega⟩
    rfl ζ (v, s)
  have eoC := square_congr_list
    (show (P ++ [(a, x)]) ++ [(1, δ)] = P ++ (a, x) :: (1, δ + 0) :: [] by
      simp only [List.append_assoc, List.cons_append, List.nil_append, add_zero]) ho' ho
    ⟨i, by simp only [List.length_append, List.length_singleton]; omega⟩
    ⟨i, by simp only [List.length_append, List.length_cons, List.length_nil]; omega⟩
    rfl ζ (v, s)
  exact (enC.symm.trans en).ge.trans (h.trans (eoC.symm.trans eo).le)

end InvariantIsing

end

end OAI
