import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRadialLattice
import OAI.NumberTheory.CubicMoment.Angular.AngularCoprimeLattice

namespace OAI

/-! Uniform centered radial lattice sums, including the short empty range.
The coprimality correction is a literal finite Möbius expansion. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma UniformLogWeights.radial_integral_bound {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) :
    ∃ M : ℝ, 0 < M ∧ ∀ i, ‖∫ x in Ioi (0:ℝ), W i x‖ ≤ M := by
  obtain ⟨M,hM,hb⟩ := h.mellin_decay 1 0
  refine ⟨M,hM,?_⟩
  intro i
  have hh := hb i 1 (by norm_num) 0
  simpa [mellin] using hh

theorem UniformLogWeights.primaryRadialLattice_centered {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) :
    ∃ K : ℝ, 0 < K ∧ ∀ i Y, 0 < Y →
      ‖primaryAngularLattice 0 (W i) Y-primaryRadialMain (W i) Y‖ ≤ K := by
  obtain ⟨C,hC,hbound⟩ := h.primaryRadialLattice_error
  obtain ⟨M,hM,hMbound⟩ := h.radial_integral_bound
  let S := Real.exp h.radius
  have hS : 1 ≤ S := Real.one_le_exp h.radius_nonneg
  have hSpos : 0 < S := Real.exp_pos _
  let A := 2*Real.pi/(9*Real.sqrt 3)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨C*S+A*M,by positivity,?_⟩
  intro i Y hY
  by_cases he : 1 ≤ S*Y
  · apply (hbound i Y hY).trans
    have hh : C/Y ≤ C*S := (div_le_iff₀ hY).mpr (by nlinarith)
    exact hh.trans (le_add_of_nonneg_right (mul_nonneg hA hM.le))
  · have hz : primaryAngularLattice 0 (W i) Y = 0 := by
      have ht (u : PrimaryArgument) : theta 0 u*W i (norm u/Y) = 0 := by
        have hn := one_le_norm (primary_ne_zero u.property)
        have hw : W i (norm u/Y) = 0 := h.upper_support i _
          ((lt_div_iff₀ hY).mpr ((lt_of_not_ge he).trans_le hn))
        rw [hw,mul_zero]
      simp only [primaryAngularLattice,ht,tsum_zero]
    have hY1 : Y ≤ 1 := by nlinarith
    have hm : ‖primaryRadialMain (W i) Y‖ ≤ A*M := by
      rw [primaryRadialMain,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
      change (2*Real.pi*Y/(9*Real.sqrt 3))*_ ≤ A*M
      calc
        _ = (A*Y)*‖∫ x in Ioi (0:ℝ), W i x‖ := by dsimp [A]; ring
        _ ≤ A*M := by
          apply mul_le_mul
          · exact mul_le_of_le_one_right hA hY1
          · exact hMbound i
          · positivity
          · exact hA
    rw [hz,zero_sub,norm_neg]
    exact hm.trans (le_add_of_nonneg_left (by positivity))

def primaryCoprimeRadialMain (r : Eisenstein) (W : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ s ∈ (primaryPrimeFactors r).powerset,
    (idealMoebius (∏ p ∈ s,p):ℂ)*primaryRadialMain W (Y/norm (∏ p ∈ s,p))

theorem UniformLogWeights.primaryCoprimeRadialLattice_centered
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ i r, primary r → Squarefree r → ∀ Y, 0 < Y →
      ‖primaryCoprimeAngularLattice r 0 (W i) Y-primaryCoprimeRadialMain r (W i) Y‖ ≤
        K*norm r^ε := by
  obtain ⟨C,hC,hbound⟩ := h.primaryRadialLattice_centered
  obtain ⟨D,hD,hdiv⟩ := primeDivisorWeight_small_power ε hε
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro i r hr hsr Y hY
  rw [primaryCoprimeAngularLattice_expansion hr hsr 0 (W i) (h.compact i) (h.smooth i) hY,
    primaryCoprimeRadialMain,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ s ∈ (primaryPrimeFactors r).powerset,C := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro s hs
      have hd : primary (∏ p ∈ s,p) := primary_finset_prod _ _
        (fun p hp => (primaryPrimeFactor_spec hr (Finset.mem_powerset.mp hs hp)).1.1)
      have hθ : theta 0 (∏ p ∈ s,p) = 1 := by simp [theta]
      rw [hθ,mul_one,←mul_sub,norm_mul]
      exact (mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_idealMoebius_le_one _)).trans
        (hbound i _ (div_pos hY (norm_pos_of_ne_zero (primary_ne_zero hd))))
    _ = C*(2:ℝ)^(primaryPrimeFactors r).card := by
      simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      ring
    _ ≤ C*(D*norm r^ε) := mul_le_mul_of_nonneg_left (hdiv r hr hsr) hC.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
