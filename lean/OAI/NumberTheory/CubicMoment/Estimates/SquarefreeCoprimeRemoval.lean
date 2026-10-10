import OAI.NumberTheory.CubicMoment.Estimates.SquarefreeModelMass
import OAI.NumberTheory.CubicMoment.Estimates.ModelOverlapCounting

namespace OAI

/-! Removing the true mutual-coprimality restriction costs the density
of multiples of the actual prime factors, not an assumed error term. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefreeCoprimeRadial_eq_sum (r : Eisenstein) (W : ℝ → ℂ)
    {A R : ℝ} (hA : 0 < A) (hcut : ∀ x, R < x → W x = 0) :
    squarefreeCoprimeAngularLattice r 0 W A =
      ∑ a ∈ primaryElementBall (R*A), if IsCoprime r a then
        (idealMoebius a:ℂ)^2*W (norm a/A) else 0 := by
  unfold squarefreeCoprimeAngularLattice
  simp only [theta_zero,mul_one]
  calc
    _ = ∑ a ∈ primaryElementBall (R*A), if primary a ∧ IsCoprime r a then
        (idealMoebius a:ℂ)^2*W (norm a/A) else 0 := by
      apply tsum_eq_sum
      intro a ha
      by_cases hp : primary a
      · have hn : R < norm a/A := by
          apply (lt_div_iff₀ hA).mpr
          exact lt_of_not_ge (fun hn => ha (mem_primaryElementBall.mpr ⟨hp,hn⟩))
        simp only [hcut _ hn,mul_zero,ite_self]
      · simp only [hp,false_and,ite_false]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [(mem_primaryElementBall.mp ha).1,true_and]

lemma squarefreeCoprimeRadial_difference_bound (W : ℝ → ℂ)
    {A R M D : ℝ} (hA : 0 < A) (hR : 0 ≤ R) (hM : 0 ≤ M) (hD : 0 < D)
    (hcut : ∀ x, R < x → W x = 0) (hW : ∀ x, ‖W x‖ ≤ M)
    {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
    (hrough : ∀ p ∈ primaryPrimeFactors r, D ≤ norm p) :
    ‖squarefreeCoprimeAngularLattice r 0 W A-
      squarefreeCoprimeAngularLattice 1 0 W A‖ ≤
      M*(primaryPrimeFactors r).card*(18*(R*A)/D) := by
  let S := primaryElementBall (R*A)
  rw [squarefreeCoprimeRadial_eq_sum r W hA hcut,
    squarefreeCoprimeRadial_eq_sum 1 W hA hcut]
  simp only [isCoprime_one_left,ite_true]
  rw [←Finset.sum_sub_distrib]
  have hp (a : Eisenstein) :
      ‖(if IsCoprime r a then (idealMoebius a:ℂ)^2*W (norm a/A) else 0)-
        (idealMoebius a:ℂ)^2*W (norm a/A)‖ ≤ if ¬IsCoprime r a then M else 0 := by
    by_cases ha : IsCoprime r a
    · simp only [ha,ite_true,not_true_eq_false,ite_false,sub_self,norm_zero,le_refl]
    · simp only [ha,ite_false,not_false_eq_true,ite_true,zero_sub,norm_neg,norm_mul,norm_pow]
      exact (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (_root_.norm_nonneg _) (norm_idealMoebius_le_one a) 2)
        (_root_.norm_nonneg _)).trans (by simpa using hW (norm a/A))
  have hcard := noncoprime_row_card_le S (mul_nonneg hR hA.le) hD
    (fun a ha => ⟨primary_ne_zero (mem_primaryElementBall.mp ha).1,
      (mem_primaryElementBall.mp ha).2⟩) hr hsr hrough
  calc
    _ ≤ ∑ a ∈ S, if ¬IsCoprime r a then M else 0 :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun a _ => hp a))
    _ = ((S.filter (fun a => ¬IsCoprime r a)).card:ℝ)*M := by rw [←Finset.sum_filter]; simp
    _ ≤ ((primaryPrimeFactors r).card*(18*(R*A)/D))*M := mul_le_mul_of_nonneg_right hcard hM
    _ = _ := by ring

theorem UniformLogWeights.squarefreeCoprimeRadial_removal
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i (r : Eisenstein) (A D : ℝ),
      primary r → Squarefree r → 0 < A → 0 < D →
      (∀ p ∈ primaryPrimeFactors r, D ≤ norm p) →
      ‖squarefreeCoprimeAngularLattice r 0 (W i) A-
        squarefreeCoprimeAngularLattice 1 0 (W i) A‖ ≤
        K*A*(primaryPrimeFactors r).card/D := by
  obtain ⟨M,hM,hbound⟩ := h.norm_bound
  let R := Real.exp h.radius
  refine ⟨18*M*R,by dsimp [R]; positivity,?_⟩
  intro i r A D hr hsr hA hD hrough
  apply (squarefreeCoprimeRadial_difference_bound (W i) hA
    (Real.exp_pos _).le hM hD (h.upper_support i) (hbound i) hr hsr hrough).trans_eq
  ring

end CubicFirstMoment

end

end OAI
