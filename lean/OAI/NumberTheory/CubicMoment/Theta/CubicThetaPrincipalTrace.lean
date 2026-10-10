import OAI.NumberTheory.CubicMoment.Theta.CubicThetaBottomRow

namespace OAI

/-! The level-three determinant identity forces the trace to be 2 modulo
9. Together with the elliptic trace bound, this isolates trace 2 without
an assumed torsion-freeness theorem. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrincipal_trace_mod_nine (g : cubicThetaPrincipalGroup) :
    (9:Eisenstein) ∣ g.val 0 0+g.val 1 1-2 := by
  obtain ⟨a,ha⟩ := (cubicThetaPrincipalGroup_diagonal_primary g).1
  obtain ⟨d,hd⟩ := (cubicThetaPrincipalGroup_diagonal_primary g).2
  obtain ⟨b,hb⟩ := (cubicThetaPrincipalGroup_offDiagonal g).1
  obtain ⟨c,hc⟩ := (cubicThetaPrincipalGroup_offDiagonal g).2
  have h00 : g.val 0 0=1+3*a := by linear_combination ha
  have h11 : g.val 1 1=1+3*d := by linear_combination hd
  have he := cubicThetaPrincipalGroup_det g
  rw [h00,h11,hb,hc] at he
  refine ⟨-(a*d-b*c),?_⟩
  rw [h00,h11]
  linear_combination he

lemma cubicThetaPrincipal_trace_eq_two_of_norm_le (g : cubicThetaPrincipalGroup)
    (h : ‖((g.val 0 0+g.val 1 1:Eisenstein):ℂ)‖ ≤ 2) :
    g.val 0 0+g.val 1 1=2 := by
  by_contra hn
  let w := g.val 0 0+g.val 1 1-2
  have hw : w≠0 := sub_ne_zero.mpr hn
  obtain ⟨t,ht⟩ := cubicThetaPrincipal_trace_mod_nine g
  have ht0 : t≠0 := by
    intro he
    apply hw
    change g.val 0 0+g.val 1 1-2=0
    rw [ht,he,mul_zero]
  have hlarge : 81 ≤ norm w := by
    change 81 ≤ norm (g.val 0 0+g.val 1 1-2)
    rw [ht]
    change 81 ≤ Complex.normSq (((9:Eisenstein):ℂ)*(t:ℂ))
    rw [Complex.normSq_mul]
    have hn9 : norm (9:Eisenstein)=81 := by
      change Complex.normSq (9:ℂ)=81
      norm_num [Complex.normSq_apply]
    change 81 ≤ norm (9:Eisenstein)*norm t
    rw [hn9]
    nlinarith [one_le_norm ht0]
  have hsmall : ‖(w:ℂ)‖ ≤ 4 := by
    change ‖((g.val 0 0+g.val 1 1:Eisenstein):ℂ)-(2:ℂ)‖ ≤ 4
    have h' : ‖((g.val 0 0+g.val 1 1:Eisenstein):ℂ)‖+‖(2:ℂ)‖ ≤ 4 := by
      have hn2 : ‖(2:ℂ)‖=(2:ℝ) := by norm_num
      rw [hn2]
      linarith only [h]
    exact (norm_sub_le _ _).trans h'
  rw [norm,Complex.normSq_eq_norm_sq] at hlarge
  nlinarith [_root_.norm_nonneg (w:ℂ)]

end CubicFirstMoment

end

end OAI
