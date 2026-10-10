import OAI.NumberTheory.Ostmann.Dirichlet.ContourMultiplicityPolynomial
import OAI.NumberTheory.Ostmann.Dirichlet.GoodContourEdges
import OAI.NumberTheory.Ostmann.Dirichlet.SmoothedExplicitRectangle

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Dirichlet
open Complex

theorem LFunction_ne_zero_rectangleBorder_of_three_edges {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {left right lo hi : ℝ}
    (hLR : left ≤ right) (hlohi : lo ≤ hi) (hright : 1 < right)
    (hthree : ∀ s : ℂ,
      ((s.re = left ∧ lo ≤ s.im ∧ s.im ≤ hi) ∨
       (s.im = lo ∧ left ≤ s.re ∧ s.re ≤ right) ∨
       (s.im = hi ∧ left ≤ s.re ∧ s.re ≤ right)) → chi.LFunction s ≠ 0) :
    ∀ s ∈ Erdos970.RectangleBorder ((left:ℂ)+(lo:ℂ)*Complex.I) ((right:ℂ)+(hi:ℂ)*Complex.I),
      chi.LFunction s ≠ 0 := by
  intro s hs
  have hs' :
      ((((left ≤ s.re ∧ s.re ≤ right) ∧ s.im = lo) ∨
        (s.re = left ∧ lo ≤ s.im ∧ s.im ≤ hi)) ∨
        ((left ≤ s.re ∧ s.re ≤ right) ∧ s.im = hi)) ∨
        (s.re = right ∧ lo ≤ s.im ∧ s.im ≤ hi) := by
    simpa [Erdos970.RectangleBorder,Set.uIcc_of_le hLR,Set.uIcc_of_le hlohi, Complex.reProdIm] using hs
  rcases hs' with ((⟨⟨hlo,hhi⟩,him⟩ | ⟨hre,hlo,hhi⟩) | ⟨⟨hlo,hhi⟩,him⟩) | ⟨hre,_,_⟩
  · exact hthree s (Or.inr (Or.inl ⟨him,hlo,hhi⟩))
  · exact hthree s (Or.inl ⟨hre,hlo,hhi⟩)
  · exact hthree s (Or.inr (Or.inr ⟨him,hlo,hhi⟩))
  · exact LFunction_ne_zero_right chi (by rw [hre]; exact hright)

theorem zerosInRectangle_subset_zerosUpTo {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) {left right lo hi T : ℝ}
    (hleft : 0 < left) (hLR : left ≤ right) (hlohi : lo ≤ hi)
    (hlo : -T-1 ≤ lo) (hhi : hi ≤ T+1) :
    (↑(zerosInRectangle chi hchi ((left:ℂ)+(lo:ℂ)*Complex.I) ((right:ℂ)+(hi:ℂ)*Complex.I)) : Set ℂ)
      ⊆ zerosUpTo chi (T+1) := by
  intro rho hrho
  obtain ⟨hr,hz⟩ := (mem_zerosInRectangle chi hchi _ _ rho).mp hrho
  have hr' : left ≤ rho.re ∧ rho.re ≤ right ∧ lo ≤ rho.im ∧ rho.im ≤ hi := by
    simpa using (mem_Rect (by simpa using hLR) (by simpa using hlohi) rho).mp hr
  have hlt : rho.re < 1 := by
    by_contra! h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi (Or.inl hchi) h hz
  exact ⟨⟨hz,hleft.trans_le hr'.1,hlt⟩,
    abs_le.mpr ⟨by linarith [hr'.2.2.1],by linarith [hr'.2.2.2]⟩⟩

theorem zerosInRectangle_multiplicity_polynomial {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) {left right lo hi T : ℝ}
    (hT : 2 ≤ T) (hleft : 1/4 ≤ left) (hLR : left ≤ right) (hlohi : lo ≤ hi)
    (hlo : -T-1 ≤ lo) (hhi : hi ≤ T+1) :
    (∑ rho ∈ zerosInRectangle chi hchi ((left:ℂ)+(lo:ℂ)*Complex.I) ((right:ℂ)+(hi:ℂ)*Complex.I),
      (zeroMultiplicity chi rho:ℝ)) ≤
      (128000000*absoluteZetaTwo)*((q:ℝ)*(T+2))^5 := by
  apply contour_zero_multiplicity_polynomial chi hchi hT
  intro rho hrho
  have hcrit := zerosInRectangle_subset_zerosUpTo chi hchi (by linarith : 0 < left)
    hLR hlohi hlo hhi hrho
  obtain ⟨hr,hz⟩ := (mem_zerosInRectangle chi hchi _ _ rho).mp hrho
  have hr' : left ≤ rho.re ∧ rho.re ≤ right ∧ lo ≤ rho.im ∧ rho.im ≤ hi := by
    simpa using (mem_Rect (by simpa using hLR) (by simpa using hlohi) rho).mp hr
  exact ⟨hleft.trans hr'.1,hcrit.1.2.2.le,hcrit.2⟩

end Ostmann.Dirichlet

end

end OAI
