import OAI.NumberTheory.JointDickman.Analysis.SquarefreeLaplaceExpansion

namespace OAI

/-! # Reciprocal-Gamma coefficients of the local Hankel contribution -/
namespace JointDickman
open MeasureTheory Set Filter Asymptotics Finset
open scoped Topology

theorem hankel_monomial_coefficient {z L : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (j : ℕ) (a : ℂ) :
    (Real.sin (Real.pi*z)/Real.pi) •
      ((L^(z-j-1)*Real.Gamma ((j:ℝ)+1-z)) • (a*(-1:ℂ)^j)) =
        (L^(z-j-1)) • (a/(Real.Gamma (z-j):ℂ)) := by
  have hs := Real.sin_sub_nat_mul_pi (Real.pi*z) j
  rw [show Real.pi*z-(j:ℝ)*Real.pi = Real.pi*(z-j) by ring] at hs
  have hc : Real.sin (Real.pi*z)/Real.pi *
      (Real.Gamma ((j:ℝ)+1-z)*(-1:ℝ)^j) = 1/Real.Gamma (z-j) := by
    rw [← gamma_reflection_coefficient hz hz1 j,hs]
    ring
  have hc' := congrArg (fun x : ℝ => (x:ℂ)) hc
  simp only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow,
    Complex.ofReal_neg,Complex.ofReal_one] at hc'
  simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_div]
  calc
    _ = (L^(z-j-1):ℝ) * a * ((Real.sin (Real.pi*z):ℂ)/(Real.pi:ℂ) *
        ((Real.Gamma ((j:ℝ)+1-z):ℂ)*(-1:ℂ)^j)) := by ring
    _ = _ := by rw [hc']; ring

theorem squarefree_local_hankel_expansion {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    ∃ c : ℕ → ℂ, c 0 = (squarefreeLeadingConstant z:ℂ) ∧
      ∀ H : ℕ, ∃ η : ℝ, 0 < η ∧
        (fun L : ℝ => (Real.sin (Real.pi*z)/Real.pi) •
          (∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) •
            squarefreeSingularFactor z (1-(t:ℂ))) -
          ∑ j ∈ range (H+1), L^(z-j-1) • c j)
          =O[atTop] (fun L => L^(z-H-2)) := by
  obtain ⟨a,ha,h⟩ := squarefreeSingularFactor_laplace_expansion hz hz1
  refine ⟨fun j => a j/(Real.Gamma (z-j):ℂ),?_,fun H => ?_⟩
  · dsimp only
    rw [Nat.cast_zero,sub_zero,ha,Complex.ofReal_mul,mul_div_cancel_right₀]
    exact_mod_cast (Real.Gamma_pos_of_pos hz).ne'
  · obtain ⟨η,hη,he⟩ := h H
    refine ⟨η,hη,?_⟩
    have hh := he.const_smul_left (Real.sin (Real.pi*z)/Real.pi)
    apply hh.congr_left
    intro L
    change (Real.sin (Real.pi*z)/Real.pi) •
      ((∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) •
        squarefreeSingularFactor z (1-(t:ℂ))) -
        ∑ j ∈ range (H+1), (L^(z-j-1)*Real.Gamma ((j:ℝ)+1-z)) • (a j*(-1:ℂ)^j)) = _
    rw [smul_sub,smul_sum]
    congr 1
    exact sum_congr rfl (fun j _ => hankel_monomial_coefficient hz hz1 j (a j))

/-- The real local contour contribution, with the factor `exp L` removed. -/
noncomputable def squarefreeLocalHankel (z η L : ℝ) : ℝ :=
  ((Real.sin (Real.pi*z)/Real.pi) •
    (∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) •
      squarefreeSingularFactor z (1-(t:ℂ)))).re

theorem squarefree_local_hankel_real_expansion {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∀ H : ℕ, ∃ η : ℝ, 0 < η ∧
        (fun L : ℝ => squarefreeLocalHankel z η L -
          ∑ j ∈ range (H+1), c j*L^(z-1-j)) =O[atTop] (fun L => L^(z-2-H)) := by
  obtain ⟨c,hc,h⟩ := squarefree_local_hankel_expansion hz hz1
  refine ⟨fun j => (c j).re,?_,?_,fun H => ?_⟩
  · dsimp only
    rw [hc,Complex.ofReal_re]
  · dsimp only
    rw [hc,Complex.ofReal_re]
    exact squarefreeLeadingConstant_pos hz hz1.le
  · obtain ⟨η,hη,he⟩ := h H
    refine ⟨η,hη,?_⟩
    have hr : (fun L : ℝ => ((Real.sin (Real.pi*z)/Real.pi) •
        (∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) •
          squarefreeSingularFactor z (1-(t:ℂ))) -
        ∑ j ∈ range (H+1), L^(z-j-1) • c j).re) =O[atTop]
          (fun L => L^(z-H-2)) := by
      apply IsBigO.trans _ he
      apply isBigO_of_le atTop
      intro L
      simpa only [Real.norm_eq_abs] using (Complex.abs_re_le_norm
        ((Real.sin (Real.pi*z)/Real.pi) •
          (∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) •
            squarefreeSingularFactor z (1-(t:ℂ))) -
          ∑ j ∈ range (H+1), L^(z-j-1) • c j))
    have hsum (L : ℝ) : (∑ j ∈ range (H+1), L^(z-j-1) • c j).re =
        ∑ j ∈ range (H+1), L^(z-j-1)*(c j).re := by
      change Complex.reCLM (∑ j ∈ range (H+1), L^(z-j-1) • c j) = _
      rw [map_sum]
      simp only [Complex.reCLM_apply,Complex.smul_re,smul_eq_mul]
    have hr' : (fun L : ℝ => squarefreeLocalHankel z η L -
        ∑ j ∈ range (H+1), (c j).re*L^(z-1-j)) =O[atTop] (fun L => L^(z-H-2)) := by
      apply hr.congr_left
      intro L
      rw [Complex.sub_re,hsum]
      change squarefreeLocalHankel z η L - _ = squarefreeLocalHankel z η L - _
      congr 1
      apply sum_congr rfl
      intro j _
      rw [show z-j-1 = z-1-j by ring,mul_comm]
    simpa only [show z-H-2 = z-2-H by ring] using hr'

end JointDickman

end OAI
