import OAI.NumberTheory.JointDickman.Arithmetic.SquarefreeHankelExpansion
import OAI.NumberTheory.JointDickman.Analysis.SquarefreeRieszLaplaceExpansion

namespace OAI

/-! # Hankel coefficients for the squarefree Riesz mean -/
namespace JointDickman
open MeasureTheory Set Filter Asymptotics Finset
open scoped Topology

theorem squarefreeRiesz_local_hankel_expansion_below {z : ℝ}
    (hz : 0 < z) (hz1 : z < 1) (r : ℝ) (hr : 0 < r) :
    ∃ c : ℕ → ℂ, c 0 = ((squarefreeLeadingConstant z / 2:ℝ):ℂ) ∧
      ∀ H : ℕ, ∃ η : ℝ, 0 < η ∧ η ≤ r ∧
        (fun L : ℝ => (Real.sin (Real.pi*z)/Real.pi) •
          (∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) •
            squarefreeRieszSingularFactor z (1-(t:ℂ))) -
          ∑ j ∈ range (H+1), L^(z-j-1) • c j)
          =O[atTop] (fun L => L^(z-H-2)) := by
  obtain ⟨a,ha,h⟩ := squarefreeRieszSingularFactor_laplace_expansion_below hz hz1 r hr
  refine ⟨fun j => a j/(Real.Gamma (z-j):ℂ),?_,fun H => ?_⟩
  · dsimp only
    rw [Nat.cast_zero,sub_zero,ha]
    have hG : (Real.Gamma z:ℂ) ≠ 0 := by exact_mod_cast (Real.Gamma_pos_of_pos hz).ne'
    push_cast
    field_simp
  · obtain ⟨η,hη,hηr,he⟩ := h H
    refine ⟨η,hη,hηr,?_⟩
    have hh := he.const_smul_left (Real.sin (Real.pi*z)/Real.pi)
    apply hh.congr_left
    intro L
    change (Real.sin (Real.pi*z)/Real.pi) •
      ((∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) •
        squarefreeRieszSingularFactor z (1-(t:ℂ))) -
        ∑ j ∈ range (H+1), (L^(z-j-1)*Real.Gamma ((j:ℝ)+1-z)) • (a j*(-1:ℂ)^j)) = _
    rw [smul_sub,smul_sum]
    congr 1
    exact sum_congr rfl (fun j _ => hankel_monomial_coefficient hz hz1 j (a j))

theorem squarefreeRiesz_local_hankel_expansion {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    ∃ c : ℕ → ℂ, c 0 = ((squarefreeLeadingConstant z / 2:ℝ):ℂ) ∧
      ∀ H : ℕ, ∃ η : ℝ, 0 < η ∧
        (fun L : ℝ => (Real.sin (Real.pi*z)/Real.pi) •
          (∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) •
            squarefreeRieszSingularFactor z (1-(t:ℂ))) -
          ∑ j ∈ range (H+1), L^(z-j-1) • c j)
          =O[atTop] (fun L => L^(z-H-2)) := by
  obtain ⟨c,hc,h⟩ := squarefreeRiesz_local_hankel_expansion_below hz hz1 1 zero_lt_one
  refine ⟨c,hc,fun H => ?_⟩
  obtain ⟨η,hη,_,he⟩ := h H
  exact ⟨η,hη,he⟩

/-- The real local contour contribution, with the factor `exp L` removed. -/
noncomputable def squarefreeRieszLocalHankel (z η L : ℝ) : ℝ :=
  ((Real.sin (Real.pi*z)/Real.pi) •
    (∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) •
      squarefreeRieszSingularFactor z (1-(t:ℂ)))).re

theorem squarefreeRiesz_local_hankel_real_expansion_below {z : ℝ}
    (hz : 0 < z) (hz1 : z < 1) (r : ℝ) (hr : 0 < r) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z / 2 ∧ 0 < c 0 ∧
      ∀ H : ℕ, ∃ η : ℝ, 0 < η ∧ η ≤ r ∧
        (fun L : ℝ => squarefreeRieszLocalHankel z η L -
          ∑ j ∈ range (H+1), c j*L^(z-1-j)) =O[atTop] (fun L => L^(z-2-H)) := by
  obtain ⟨c,hc,h⟩ := squarefreeRiesz_local_hankel_expansion_below hz hz1 r hr
  refine ⟨fun j => (c j).re,?_,?_,fun H => ?_⟩
  · dsimp only
    rw [hc,Complex.ofReal_re]
  · dsimp only
    rw [hc,Complex.ofReal_re]
    exact div_pos (squarefreeLeadingConstant_pos hz hz1.le) (by norm_num)
  · obtain ⟨η,hη,hηr,he⟩ := h H
    refine ⟨η,hη,hηr,?_⟩
    have hr : (fun L : ℝ => ((Real.sin (Real.pi*z)/Real.pi) •
        (∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) •
          squarefreeRieszSingularFactor z (1-(t:ℂ))) -
        ∑ j ∈ range (H+1), L^(z-j-1) • c j).re) =O[atTop]
          (fun L => L^(z-H-2)) := by
      apply IsBigO.trans _ he
      apply isBigO_of_le atTop
      intro L
      simpa only [Real.norm_eq_abs] using (Complex.abs_re_le_norm
        ((Real.sin (Real.pi*z)/Real.pi) •
          (∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) •
            squarefreeRieszSingularFactor z (1-(t:ℂ))) -
          ∑ j ∈ range (H+1), L^(z-j-1) • c j))
    have hsum (L : ℝ) : (∑ j ∈ range (H+1), L^(z-j-1) • c j).re =
        ∑ j ∈ range (H+1), L^(z-j-1)*(c j).re := by
      change Complex.reCLM (∑ j ∈ range (H+1), L^(z-j-1) • c j) = _
      rw [map_sum]
      simp only [Complex.reCLM_apply,Complex.smul_re,smul_eq_mul]
    have hr' : (fun L : ℝ => squarefreeRieszLocalHankel z η L -
        ∑ j ∈ range (H+1), (c j).re*L^(z-1-j)) =O[atTop] (fun L => L^(z-H-2)) := by
      apply hr.congr_left
      intro L
      rw [Complex.sub_re,hsum]
      change squarefreeRieszLocalHankel z η L - _ = squarefreeRieszLocalHankel z η L - _
      congr 1
      apply sum_congr rfl
      intro j _
      rw [show z-j-1 = z-1-j by ring,mul_comm]
    simpa only [show z-H-2 = z-2-H by ring] using hr'

theorem squarefreeRiesz_local_hankel_real_expansion {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z / 2 ∧ 0 < c 0 ∧
      ∀ H : ℕ, ∃ η : ℝ, 0 < η ∧
        (fun L : ℝ => squarefreeRieszLocalHankel z η L -
          ∑ j ∈ range (H+1), c j*L^(z-1-j)) =O[atTop] (fun L => L^(z-2-H)) := by
  obtain ⟨c,hc,hpos,h⟩ := squarefreeRiesz_local_hankel_real_expansion_below hz hz1 1 zero_lt_one
  refine ⟨c,hc,hpos,fun H => ?_⟩
  obtain ⟨η,hη,_,he⟩ := h H
  exact ⟨η,hη,he⟩

end JointDickman

end OAI
