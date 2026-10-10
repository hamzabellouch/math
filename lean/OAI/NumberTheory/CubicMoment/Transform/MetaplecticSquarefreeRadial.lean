import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRadialCentered
import OAI.NumberTheory.CubicMoment.Angular.AngularSquarefreeLattice
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRadialDensity
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRadialEulerTail

namespace OAI

/-! The squarefree radial model after actual square-divisor inversion.
Its finite main term remains explicit for comparison with the inverse
completion residue. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def squarefreeCoprimeRadialMain (r : Eisenstein) (W : ℝ → ℂ) (Y B : ℝ) : ℂ :=
  ∑ c ∈ squarefreeDivisorTruncation (Real.sqrt (B*Y)),
    (idealMoebius c:ℂ)*(if IsCoprime r (c^2) then
      primaryCoprimeRadialMain r W (Y/norm (c^2)) else 0)

lemma squarefreeCoprimeRadialMain_eq {r : Eisenstein} (hr : primary r)
    (hsr : Squarefree r) (W : ℝ → ℂ) (Y B : ℝ) :
    squarefreeCoprimeRadialMain r W Y B =
      ((((2*Real.pi*Y/(9*Real.sqrt 3))*(metaplecticTotient r/norm r):ℝ):ℂ)*
        (∫ x in Set.Ioi (0:ℝ), W x))*
          metaplecticRadialEulerPartial r (Real.sqrt (B*Y)) := by
  have he : squarefreeDivisorTruncation (Real.sqrt (B*Y)) =
      (primaryElementBall (Real.sqrt (B*Y))).filter Squarefree := by
    ext c
    simp only [mem_squarefreeDivisorTruncation,Finset.mem_filter,mem_primaryElementBall]
    tauto
  unfold squarefreeCoprimeRadialMain metaplecticRadialEulerPartial
  rw [he,Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hsf : Squarefree c
  · simp only [hsf,ite_true]
    have hcop : IsCoprime r (c^2) ↔ IsCoprime r c := by
      rw [pow_two,IsCoprime.mul_right_iff,and_self]
    by_cases hrc : IsCoprime r c
    · simp only [hcop,hrc,ite_true,primaryCoprimeRadialMain_eq hr hsr]
      rw [eisenstein_norm_pow,Real.rpow_neg (norm_nonneg c),Real.rpow_ofNat]
      push_cast
      ring
    · simp only [hcop,hrc,ite_false,mul_zero]
  · simp [hsf,idealMoebius]

theorem UniformLogWeights.squarefreeCoprimeRadialLattice_centered
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ i r, primary r → Squarefree r → ∀ Y, 0 < Y →
      ‖squarefreeCoprimeAngularLattice r 0 (W i) Y-
        squarefreeCoprimeRadialMain r (W i) Y (Real.exp h.radius)‖ ≤
        K*norm r^ε*Real.sqrt Y := by
  obtain ⟨C,hC,hbound⟩ := h.primaryCoprimeRadialLattice_centered hε
  let S := Real.exp h.radius
  have hS : 0 < S := Real.exp_pos _
  refine ⟨18*Real.sqrt S*C,by positivity,?_⟩
  intro i r hr hsr Y hY
  have hNr : 0 ≤ norm r^ε := Real.rpow_nonneg (norm_nonneg r) _
  let B := squarefreeDivisorTruncation (Real.sqrt (S*Y))
  have hcard : (B.card:ℝ) ≤ 18*Real.sqrt (S*Y) := by
    have hsub : B ⊆ nonzeroNormBall (Real.sqrt (S*Y)) := by
      intro c hc
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (nonzeroNormBall_card_le (Real.sqrt_nonneg _))
  rw [squarefreeCoprimeAngularLattice_expansion r 0 (W i) (h.compact i) (h.smooth i)
    hY (h.upper_support i),squarefreeCoprimeRadialMain,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ c ∈ B,C*norm r^ε := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro c hc
      have hprim : primary (c^2) := by
        simpa only [pow_two] using primary_mul (mem_squarefreeDivisorTruncation.mp hc).1
          (mem_squarefreeDivisorTruncation.mp hc).1
      by_cases hcop : IsCoprime r (c^2)
      · simp only [hcop,ite_true,show theta 0 (c^2) = 1 by simp [theta],one_mul]
        rw [←mul_sub,norm_mul]
        exact (mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_idealMoebius_le_one _)).trans
          (hbound i r hr hsr _ (div_pos hY (norm_pos_of_ne_zero (primary_ne_zero hprim))))
      · simp only [hcop,ite_false,mul_zero,sub_self,norm_zero]
        exact mul_nonneg hC.le hNr
    _ = (B.card:ℝ)*(C*norm r^ε) := by simp
    _ ≤ (18*Real.sqrt (S*Y))*(C*norm r^ε) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg hC.le hNr)
    _ = _ := by rw [Real.sqrt_mul hS.le]; ring

end CubicFirstMoment

end

end OAI
