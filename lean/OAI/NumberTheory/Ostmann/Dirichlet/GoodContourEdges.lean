import OAI.NumberTheory.Ostmann.Dirichlet.ContourEdgeSelection
import OAI.NumberTheory.Ostmann.Dirichlet.ContourPolynomialBudget
import OAI.NumberTheory.Ostmann.Dirichlet.ContourSeparatedBound

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Dirichlet

theorem exists_good_contour_edges :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi ≠ 1 → ∀ T : ℝ, 2 ≤ T → ∃ left lo hi : ℝ,
        left ∈ Set.Icc (1/4:ℝ) (1/2) ∧ lo ∈ Set.Icc (-T-1) (-T) ∧
        hi ∈ Set.Icc T (T+1) ∧ ∀ s : ℂ,
          1/4 ≤ s.re → s.re ≤ 2 → |s.im| ≤ T+1 →
          (s.re = left ∨ s.im = lo ∨ s.im = hi) →
          chi.LFunction s ≠ 0 ∧
          ‖deriv chi.LFunction s / chi.LFunction s‖ ≤ C*((q:ℝ)*(T+2))^5 := by
  obtain ⟨C0,hC0,hbound⟩ := exists_contour_logDerivative_of_separated
  let D : ℝ := 8000000*absoluteZetaTwo
  have hD : 0 < D := by have := one_le_absoluteZetaTwo; dsimp [D]; positivity
  refine ⟨3*C0*(17+256*D),by positivity,?_⟩
  intro q _ chi hchi T hT
  let S := contourZeros chi hchi T
  obtain ⟨left,lo,hi,hleft,hlo,hhi,havoid⟩ := exists_contour_edges_avoiding_finset S T
  let delta : ℝ := 1/(16*((S.card:ℝ)+1))
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hcard : (S.card:ℝ) ≤ D*q*(T+4)^4 := contourZeros_card_le chi hchi (by linarith)
  have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hpoly := contour_polynomial_budget C0 D q T S.card hC0 hD hq hT (by positivity) hcard
  refine ⟨left,lo,hi,hleft,hlo,hhi,?_⟩
  intro s hre hre2 him hedge
  have h := hbound q chi hchi T delta (by linarith) hdelta s hre hre2 him
    (havoid s hedge)
  refine ⟨h.1,?_⟩
  have hb : ‖deriv chi.LFunction s/chi.LFunction s‖ ≤
      C0*q*(T+7)*(1+16*((S.card:ℝ)+1)) := by
    simpa only [delta,one_div_one_div] using h.2
  exact hb.trans hpoly

theorem exists_good_contour_rectangle :
    ∃ (B : ℕ) (C : ℝ), 0 < C ∧ ∀ (q : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q), chi ≠ 1 → ∀ T : ℝ, 2 ≤ T →
      ∃ left lo hi : ℝ, left ∈ Set.Icc (1/4:ℝ) (1/2) ∧
        lo ∈ Set.Icc (-T-1) (-T) ∧ hi ∈ Set.Icc T (T+1) ∧
        ∀ right : ℝ, right ∈ Set.Icc 1 2 → ∀ s : ℂ,
          ((s.re = left ∧ lo ≤ s.im ∧ s.im ≤ hi) ∨
           (s.im = lo ∧ left ≤ s.re ∧ s.re ≤ right) ∨
           (s.im = hi ∧ left ≤ s.re ∧ s.re ≤ right)) →
          chi.LFunction s ≠ 0 ∧
          ‖deriv chi.LFunction s/chi.LFunction s‖ ≤ C*((q:ℝ)*(T+2))^B := by
  obtain ⟨C,hC,hgood⟩ := exists_good_contour_edges
  refine ⟨5,C,hC,?_⟩
  intro q _ chi hchi T hT
  obtain ⟨left,lo,hi,hleft,hlo,hhi,hbound⟩ := hgood q chi hchi T hT
  refine ⟨left,lo,hi,hleft,hlo,hhi,?_⟩
  intro right hright s hs
  rcases hs with ⟨hre,himlo,himhi⟩ | ⟨him,hrelo,hrehi⟩ | ⟨him,hrelo,hrehi⟩
  · apply hbound s (by rw [hre]; exact hleft.1) (by rw [hre]; linarith [hleft.2])
      (abs_le.mpr ⟨by linarith [hlo.1],by linarith [hhi.2]⟩)
    exact Or.inl hre
  · apply hbound s (hleft.1.trans hrelo) (hrehi.trans hright.2)
      (abs_le.mpr ⟨by rw [him]; linarith [hlo.1],by rw [him]; linarith [hlo.2]⟩)
    exact Or.inr (Or.inl him)
  · apply hbound s (hleft.1.trans hrelo) (hrehi.trans hright.2)
      (abs_le.mpr ⟨by rw [him]; linarith [hhi.1],by rw [him]; exact hhi.2⟩)
    exact Or.inr (Or.inr him)

end Ostmann.Dirichlet

end

end OAI
