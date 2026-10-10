import OAI.NumberTheory.JointDickman.Counting.FiniteConvolutionShift

namespace OAI

/-! # Smoothing a periodic lag factor along its residue class -/
namespace JointDickman
open Finset Classical

noncomputable def residueSmoothed (g : ℕ → ℂ) (q R n : ℕ) : ℂ :=
  (∑ h ∈ range R, g (n+q*(h+1)))/(R : ℂ)

theorem norm_sub_average_le (A : ℂ) (B : ℕ → ℂ) {R : ℕ} (hR : 0 < R)
    {E : ℝ} (hE : ∀ h < R, ‖A-B h‖ ≤ E) :
    ‖A-(∑ h ∈ range R, B h)/(R : ℂ)‖ ≤ E := by
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  have he : A-(∑ h ∈ range R, B h)/(R : ℂ) =
      (∑ h ∈ range R, (A-B h))/(R : ℂ) := by
    rw [sum_sub_distrib,sum_const,card_range,nsmul_eq_mul]
    field_simp
  rw [he,norm_div,Complex.norm_natCast]
  apply (div_le_iff₀ hRr).mpr
  calc
    _ ≤ ∑ h ∈ range R, ‖A-B h‖ := norm_sum_le _ _
    _ ≤ ∑ _h ∈ range R, E := sum_le_sum (fun h hh => hE h (mem_range.mp hh))
    _ = _ := by simp; ring

theorem periodicConvolution_smoothing (K : ℕ → ℝ) (g : ℕ → ℂ)
    {q R : ℕ} (F : ZMod q → ℝ) (hR : 0 < R) (N v : ℕ)
    {G W : ℝ} (hG : ∀ n, ‖g n‖ ≤ G) (hF : ∀ r, |F r| ≤ W) :
    ‖(∑ j ∈ range (N+1), (K j : ℂ)*(F (j : ZMod q) : ℂ)*g (v+j))-
      ∑ j ∈ range (N+1), (K j : ℂ)*(F (j : ZMod q) : ℂ)*residueSmoothed g q R (v+j)‖ ≤
        W*G*finiteCoefficientVariation K N*(q*R : ℕ) := by
  let g' : ℕ → ℂ := fun n => (F ((n : ZMod q)-(v : ZMod q)) : ℂ)*g n
  have hG0 : 0 ≤ G := (norm_nonneg (g 0)).trans (hG 0)
  have hW0 : 0 ≤ W := (abs_nonneg (F 0)).trans (hF 0)
  have hg' n : ‖g' n‖ ≤ W*G := by
    dsimp only [g']
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul (hF _) (hG n) (norm_nonneg _) hW0
  have hphase (j h : ℕ) :
      F (((v+q*(h+1)+j : ℕ) : ZMod q)-(v : ZMod q)) = F (j : ZMod q) := by
    congr 1
    push_cast
    simp
  have hbase (j : ℕ) : F (((v+j : ℕ) : ZMod q)-(v : ZMod q)) = F (j : ZMod q) := by
    congr 1
    push_cast
    ring
  let A : ℂ := ∑ j ∈ range (N+1), (K j : ℂ)*(F (j : ZMod q) : ℂ)*g (v+j)
  let V : ℕ → ℂ := fun h => ∑ j ∈ range (N+1),
    (K j : ℂ)*(F (j : ZMod q) : ℂ)*g (v+j+q*(h+1))
  have hshift (h : ℕ) (hh : h < R) :
      ‖A-V h‖ ≤ W*G*finiteCoefficientVariation K N*(q*R : ℕ) := by
    have hshiftBound := finiteConvolution_shift_bound K g' N v (q*(h+1)) hg'
    simp only [finiteConvolution,g',hphase,hbase] at hshiftBound
    have hV : (∑ j ∈ range (N+1), (K j : ℂ)*((F (j : ZMod q) : ℂ)*g (v+q*(h+1)+j))) = V h := by
      apply sum_congr rfl
      intro j _
      rw [show v+q*(h+1)+j = v+j+q*(h+1) by omega]
      ring
    simp only [hV] at hshiftBound
    have hA : (∑ j ∈ range (N+1), (K j : ℂ)*((F (j : ZMod q) : ℂ)*g (v+j))) = A := by
      dsimp only [A]
      apply sum_congr rfl
      intro j _
      ring
    rw [hA,norm_sub_rev] at hshiftBound
    apply hshiftBound.trans
    have hvar : 0 ≤ finiteCoefficientVariation K N := by
      unfold finiteCoefficientVariation
      positivity
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.mul_le_mul_left q (show h+1 ≤ R by omega))
      (by positivity)
  have he : (∑ j ∈ range (N+1), (K j : ℂ)*(F (j : ZMod q) : ℂ)*residueSmoothed g q R (v+j)) =
      (∑ h ∈ range R, V h)/(R : ℂ) := by
    unfold residueSmoothed V
    simp only [← mul_div_assoc,mul_sum]
    rw [← sum_div,sum_comm]
  rw [he]
  exact norm_sub_average_le A V hR hshift

end JointDickman

end OAI
