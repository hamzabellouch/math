import OAI.NumberTheory.TwoPoint.Halasz.HalaszDyadicDirichlet
import OAI.NumberTheory.TwoPoint.Halasz.HalaszDyadicCutoff
import OAI.NumberTheory.TwoPoint.Halasz.HalaszCutoffRemainder

namespace OAI

/-! Polynomial logarithmic growth of the actual Hurwitz function in a
weak Vinogradov--Korobov strip, uniform in the translation parameter. -/
namespace TwoPointCorrelations

open Complex HurwitzZeta Finset

theorem halasz_hurwitz_growth : ∃ A : ℝ, 1≤ A ∧ ∀ L : ℝ, 100≤ L →
    ∀ a∈Set.Icc (0:ℝ) 1, ∀ s : ℂ, 2/3≤ s.re → s.re≤2 →
    |s.im|=Real.exp L → max (1-s.re) 0≤4*L^(-(2/3:ℝ)) →
      ‖hurwitzZeta (a:UnitAddCircle) s-mrtHurwitzFirstTerm a s‖≤ A*(L+1)^7 := by
  obtain ⟨C,hC,hpoly⟩ := halasz_dyadic_dirichlet
  refine ⟨7*C+15,by linarith,?_⟩
  intro L hL a ha s hσ hσhi ht hδ
  let K := halaszDyadicCutoffDegree L
  let N := 2^K-1
  obtain ⟨hN,hKL,hKhi,hNlo,hNhi⟩ := halasz_dyadic_cutoff_bounds hL
  have hσ0 : 0<s.re := by linarith
  have hs1 : s≠1 := by
    intro hs1
    rw [hs1] at ht
    norm_num at ht
    exact (Real.exp_pos L).ne' ht.symm
  have hcut := halasz_hurwitz_cutoff ha hσ0 hs1 hN
  have hrem := halasz_cutoff_remainder
    (Real.one_le_exp_iff.mpr (by linarith : 0≤ L)) hNlo hNhi hσ hσhi ht
  have hp := hpoly K L (by linarith) hKL a ha s hσ ht hδ
  have hn : ‖hurwitzZeta (a:UnitAddCircle) s-mrtHurwitzFirstTerm a s‖≤
      15+((K:ℝ)+1)*C*(L+1)^6 := by
    calc
      _ = ‖(hurwitzZeta (a:UnitAddCircle) s-mrtHurwitzFirstTerm a s-
          ∑ n∈range N,(((n+1:ℕ):ℝ)+a:ℂ)^(-s))+
          ∑ n∈range N,(((n+1:ℕ):ℝ)+a:ℂ)^(-s)‖ := by congr 1; ring
      _ ≤ ‖hurwitzZeta (a:UnitAddCircle) s-mrtHurwitzFirstTerm a s-
          ∑ n∈range N,(((n+1:ℕ):ℝ)+a:ℂ)^(-s)‖+
          ‖∑ n∈range N,(((n+1:ℕ):ℝ)+a:ℂ)^(-s)‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (hcut.trans hrem) hp
  have hK : (K:ℝ)+1≤7*(L+1) := by linarith
  have hmul := mul_le_mul_of_nonneg_right hK (by positivity : 0≤ C*(L+1)^6)
  have hone : 1≤(L+1)^7 := one_le_pow₀ (by linarith)
  apply hn.trans
  have heq : (L+1)^7=(L+1)^6*(L+1) := by ring
  rw [heq] at hone ⊢
  nlinarith

end TwoPointCorrelations

end OAI
