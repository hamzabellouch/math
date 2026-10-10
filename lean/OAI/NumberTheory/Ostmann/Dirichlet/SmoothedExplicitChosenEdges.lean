import OAI.NumberTheory.Ostmann.Dirichlet.GoodContourRectangleBoundary
import OAI.NumberTheory.Ostmann.Dirichlet.SmoothedExplicitContourBound
import OAI.NumberTheory.Ostmann.Dirichlet.SmoothedExplicitKernelBounds
import OAI.NumberTheory.Ostmann.Dirichlet.SmoothedExplicitTails

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Dirichlet
open Complex Set MeasureTheory
open scoped Topology BigOperators SchwartzMap

theorem smooth_contour_bound_of_edges {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : 𝓢(ℝ, ℂ)) (A : ℕ)
    {X left right lo hi T B C D : ℝ} (hX : 1 ≤ X) (hT : 2 ≤ T)
    (hl : left ∈ Icc (1/4:ℝ) (1/2)) (hr : right ∈ Ioc (1:ℝ) 2)
    (hlo : lo ∈ Icc (-T-1) (-T)) (hhi : hi ∈ Icc T (T+1))
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hedges : ∀ s : ℂ,
      ((s.re=left ∧ lo ≤ s.im ∧ s.im ≤ hi) ∨
       (s.im=lo ∧ left ≤ s.re ∧ s.re ≤ right) ∨
       (s.im=hi ∧ left ≤ s.re ∧ s.re ≤ right)) →
      χ.LFunction s ≠ 0 ∧ ‖logDeriv χ.LFunction s‖ ≤ B)
    (hker : ∀ s : ℂ, s.re ∈ Icc (1/4:ℝ) 2 → ‖mellin (ρ:ℝ→ℂ) s‖ ≤ C/(1+|s.im|)^A)
    (hker0 : ∀ s : ℂ, s.re ∈ Icc (1/4:ℝ) 2 → ‖mellin (ρ:ℝ→ℂ) s‖ ≤ C)
    (hker2 : ∀ σ ∈ Icc (1/4:ℝ) 2, ∀ t : ℝ,
      (1+|t|)^(A+2)*‖mellin (ρ:ℝ→ℂ) ((σ:ℂ)+t*Complex.I)‖ ≤ C)
    (hright : ∀ t : ℝ, ‖logDeriv χ.LFunction ((right:ℂ)+t*Complex.I)‖ ≤ D) :
    ‖∑' n : ℕ, χ n*(ArithmeticFunction.vonMangoldt n:ℂ)*ρ ((n:ℝ)/X)‖ ≤
      (∑ p ∈ zerosInRectangle χ hχ ((left:ℂ)+lo*Complex.I) ((right:ℂ)+hi*Complex.I),
        (zeroMultiplicity χ p:ℝ)*X^p.re*‖mellin (ρ:ℝ→ℂ) p‖) +
      B*C*Real.sqrt X*(2*T+2) + 4*B*C*X^right/T^A +
      2*D*C*X^right/T^A*smoothTailIntegral := by
  have hXp : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hTp : 0 < T := by linarith
  have hlr : left ≤ right := by linarith [hl.2,hr.1]
  have hlohi : lo ≤ hi := by linarith [hlo.2,hhi.1]
  have hleft : 0 < left := by linarith [hl.1]
  have hnon := LFunction_ne_zero_rectangleBorder_of_three_edges χ hlr hlohi hr.1
    (fun s hs => (hedges s hs).1)
  have hn := norm_character_smooth_le_zeroSum_edges χ hχ ρ hXp hleft hr.1 hlr hlohi hnon
  have hve := smooth_vertical_edge_bound χ ρ hXp hB hC hlohi
    (fun t ht => (hedges ((left:ℂ)+t*Complex.I) (Or.inl (by simpa using ht))).2)
    (fun t _ => hker0 ((left:ℂ)+t*Complex.I) (by simpa only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_zero,add_zero]
      using (show left ∈ Icc (1/4:ℝ) 2 from ⟨hl.1,le_trans hl.2 (by norm_num)⟩)))
  have hpow : X^left ≤ Real.sqrt X := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hX hl.2
  have hleftbound : ‖Erdos970.VIntegral (characterSmoothIntegrand ρ χ X) left lo hi‖ ≤
      B*C*Real.sqrt X*(2*T+2) := by
    apply hve.trans
    gcongr
    linarith [hlo.1,hhi.2]
  have hhor (y : ℝ) (hy : y=lo ∨ y=hi) :
      ‖Erdos970.HIntegral (characterSmoothIntegrand ρ χ X) left right y‖ ≤
        2*B*C*X^right/T^A := by
    have habs : T ≤ |y| := by
      rcases hy with hy | hy
      · rw [hy]
        exact (by linarith [hlo.2] : T ≤ -lo).trans (neg_le_abs lo)
      · rw [hy]
        exact hhi.1.trans (le_abs_self hi)
    have he := smooth_horizontal_edge_bound χ ρ hX hB (by positivity : 0 ≤ C/T^A) hlr
      (fun x hx => (hedges ((x:ℂ)+y*Complex.I) (by
        rcases hy with rfl | rfl
        · exact Or.inr (Or.inl (by simpa using hx))
        · exact Or.inr (Or.inr (by simpa using hx)))).2)
      (fun x hx => smooth_kernel_at_height hC hTp hker
        (by simpa only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_zero,add_zero]
          using (show x ∈ Icc (1/4:ℝ) 2 from ⟨hl.1.trans hx.1,hx.2.trans hr.2⟩)) (by simpa using habs))
    calc
      _ ≤ B*(C/T^A)*X^right*(right-left) := he
      _ ≤ B*(C/T^A)*X^right*2 := by gcongr; linarith [hl.1,hr.2]
      _ = _ := by ring
  have hbottom := hhor lo (Or.inl rfl)
  have htop := hhor hi (Or.inr rfl)
  have hlowtail := smooth_right_tail_bound χ ρ A hXp hTp hD hC hright
    (hker2 right ⟨by linarith [hr.1],hr.2⟩) (Iic lo) measurableSet_Iic
    (fun t ht => (by have htt : t ≤ lo := ht; linarith [hlo.2] : T ≤ -t).trans (neg_le_abs t))
  have hightail := smooth_right_tail_bound χ ρ A hXp hTp hD hC hright
    (hker2 right ⟨by linarith [hr.1],hr.2⟩) (Ici hi) measurableSet_Ici
    (fun t ht => (hhi.1.trans ht).trans (le_abs_self t))
  calc
    _ ≤ (∑ p ∈ zerosInRectangle χ hχ ((left:ℂ)+lo*Complex.I) ((right:ℂ)+hi*Complex.I),
        (zeroMultiplicity χ p:ℝ)*X^p.re*‖mellin (ρ:ℝ→ℂ) p‖) +
        B*C*Real.sqrt X*(2*T+2) + (2*B*C*X^right/T^A) + (2*B*C*X^right/T^A) +
        (D*C*X^right/T^A*smoothTailIntegral) + (D*C*X^right/T^A*smoothTailIntegral) :=
      by linarith only [hn,hleftbound,hbottom,htop,hlowtail,hightail]
    _ = _ := by ring

end Ostmann.Dirichlet

end

end OAI
