import Mathlib.Analysis.Complex.Basic
import OAI.NumberTheory.Ostmann.Dirichlet.FiniteContourAvoidance

namespace OAI

noncomputable section
namespace Ostmann.Dirichlet
open scoped Classical

lemma contour_gap_le {N M a b : ℝ} (hM : 0 ≤ M) (hMN : M ≤ N) (hab : 1/4 ≤ b-a) :
    1/(16*(N+1)) ≤ (b-a)/(4*(M+1)) := by
  calc
    _ = (1/4:ℝ)/(4*(N+1)) := by rw [div_div]; congr 1; ring
    _ ≤ (1/4:ℝ)/(4*(M+1)) := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    _ ≤ _ := div_le_div_of_nonneg_right hab (by positivity)

theorem exists_contour_edges_avoiding_finset (S : Finset ℂ) (T : ℝ) :
    ∃ left lo hi : ℝ, left ∈ Set.Icc (1/4:ℝ) (1/2) ∧
      lo ∈ Set.Icc (-T-1) (-T) ∧ hi ∈ Set.Icc T (T+1) ∧
      ∀ s : ℂ, s.re = left ∨ s.im = lo ∨ s.im = hi →
        ∀ rho ∈ S, 1/(16*((S.card:ℝ)+1)) ≤ ‖s-rho‖ := by
  obtain ⟨left,hleft,hleftAvoid⟩ := exists_mem_Icc_avoiding_finset
    (S.image Complex.re) (1/4) (1/2) (by norm_num)
  obtain ⟨lo,hlo,hloAvoid⟩ := exists_mem_Icc_avoiding_finset
    (S.image Complex.im) (-T-1) (-T) (by linarith)
  obtain ⟨hi,hhi,hhiAvoid⟩ := exists_mem_Icc_avoiding_finset
    (S.image Complex.im) T (T+1) (by linarith)
  have hreCard : ((S.image Complex.re).card:ℝ) ≤ S.card := by exact_mod_cast Finset.card_image_le
  have himCard : ((S.image Complex.im).card:ℝ) ≤ S.card := by exact_mod_cast Finset.card_image_le
  refine ⟨left,lo,hi,hleft,hlo,hhi,?_⟩
  intro s hs rho hr
  rcases hs with hleftEq | hloEq | hhiEq
  · have h := (contour_gap_le (by positivity) hreCard (by norm_num : (1/4:ℝ)≤1/2-1/4)).trans
      (hleftAvoid rho.re (Finset.mem_image.mpr ⟨rho,hr,rfl⟩))
    have hn := Complex.abs_re_le_norm (s-rho)
    simp only [Complex.sub_re,hleftEq] at hn
    exact h.trans hn
  · have h := (contour_gap_le (by positivity) himCard
        (show (1/4:ℝ)≤-T-(-T-1) by linarith)).trans
      (hloAvoid rho.im (Finset.mem_image.mpr ⟨rho,hr,rfl⟩))
    have hn := Complex.abs_im_le_norm (s-rho)
    simp only [Complex.sub_im,hloEq] at hn
    exact h.trans hn
  · have h := (contour_gap_le (by positivity) himCard
        (show (1/4:ℝ)≤(T+1)-T by linarith)).trans
      (hhiAvoid rho.im (Finset.mem_image.mpr ⟨rho,hr,rfl⟩))
    have hn := Complex.abs_im_le_norm (s-rho)
    simp only [Complex.sub_im,hhiEq] at hn
    exact h.trans hn

end Ostmann.Dirichlet

end

end OAI
