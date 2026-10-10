import OAI.NumberTheory.CubicGram.LatticeCounts

namespace OAI

/-! A genuine thin-annulus lattice count. Disjoint half-unit disks
around Eisenstein integers fit inside the thickened annulus. -/
noncomputable section
open MeasureTheory Set Metric
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma eisenstein_dist_ge_one {a b : Eisenstein} (hab : a ≠ b) :
    1 ≤ dist (a:ℂ) (b:ℂ) := by
  have hn := one_le_norm (sub_ne_zero.mpr hab)
  rw [norm,Subalgebra.coe_sub,Complex.normSq_eq_norm_sq] at hn
  rw [dist_eq_norm]
  nlinarith [_root_.norm_nonneg ((a:ℂ)-(b:ℂ))]

lemma complex_ball_real_volume (z : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (ball z r) = r^2*Real.pi := by
  simp only [measureReal_def,Complex.volume_ball,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr,ENNReal.coe_toReal,NNReal.coe_real_pi]

theorem eisenstein_annulus_card (S : Finset Eisenstein) {A B : ℝ}
    (hA : 1 ≤ A) (hAB : A ≤ B)
    (hS : ∀ a ∈ S, A ≤ norm a ∧ norm a ≤ B) :
    (S.card:ℝ) ≤ 4*(B-A+Real.sqrt B+Real.sqrt A) := by
  have hA0 : 0 ≤ A := by linarith
  have hB0 : 0 ≤ B := hA0.trans hAB
  let r := Real.sqrt A-1/2
  let R := Real.sqrt B+1/2
  have hsqA := Real.sq_sqrt hA0
  have hsqB := Real.sq_sqrt hB0
  have hsA := Real.sqrt_nonneg A
  have hsB := Real.sqrt_nonneg B
  have hr : 0 ≤ r := by dsimp [r]; nlinarith
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hrR : r ≤ R := by
    dsimp [r,R]
    linarith [Real.sqrt_le_sqrt hAB]
  let U : Set ℂ := ⋃ a ∈ S, ball (a:ℂ) (1/2)
  have hdisj : PairwiseDisjoint (S:Set Eisenstein)
      (fun a => ball (a:ℂ) (1/2:ℝ)) := by
    intro a ha b hb hab
    exact ball_disjoint_ball (by convert eisenstein_dist_ge_one hab using 1; norm_num)
  have hsub : U ⊆ ball (0:ℂ) R \ ball 0 r := by
    intro z hz
    obtain ⟨a,ha,hz⟩ := mem_iUnion₂.mp hz
    have haN := hS a ha
    have haL : Real.sqrt A ≤ ‖(a:ℂ)‖ := by
      have hn := haN.1
      rw [norm,Complex.normSq_eq_norm_sq] at hn
      nlinarith [_root_.norm_nonneg (a:ℂ)]
    have haU : ‖(a:ℂ)‖ ≤ Real.sqrt B := by
      have hn := haN.2
      rw [norm,Complex.normSq_eq_norm_sq] at hn
      nlinarith [_root_.norm_nonneg (a:ℂ)]
    have hz' : dist z (a:ℂ) < (1/2:ℝ) := hz
    refine ⟨?_,?_⟩
    · change dist z 0 < R
      have ht := dist_triangle z (a:ℂ) 0
      simp only [dist_zero_right] at ht ⊢
      dsimp [R]
      linarith
    · intro hz0
      have hz0' : dist z 0 < r := hz0
      have ht := dist_triangle (a:ℂ) z 0
      rw [dist_comm (a:ℂ) z] at ht
      simp only [dist_zero_right] at ht hz0'
      dsimp [r] at hz0'
      linarith
  have hvolU : volume.real U = (S.card:ℝ)*((1/2:ℝ)^2*Real.pi) := by
    rw [show U = ⋃ a ∈ S, ball (a:ℂ) (1/2:ℝ) from rfl,
      measureReal_biUnion_finset hdisj (fun _ _ => measurableSet_ball)]
    simp only [complex_ball_real_volume _ (by norm_num : (0:ℝ) ≤ 1/2),
      Finset.sum_const,nsmul_eq_mul]
  have hfin : volume (ball (0:ℂ) R) ≠ ⊤ := by
    rw [Complex.volume_ball]
    finiteness
  have hvol : volume.real U ≤ (R^2-r^2)*Real.pi := by
    apply (measureReal_mono hsub (measure_ne_top_of_subset sdiff_subset hfin)).trans_eq
    rw [measureReal_sdiff (ball_subset_ball hrR) measurableSet_ball hfin,
      complex_ball_real_volume _ hR,complex_ball_real_volume _ hr]
    ring
  rw [hvolU] at hvol
  have hp := Real.pi_pos
  have he : R^2-r^2 = B-A+Real.sqrt B+Real.sqrt A := by
    dsimp [R,r]
    nlinarith
  rw [he] at hvol
  nlinarith

theorem eisenstein_thin_annulus_card (S : Finset Eisenstein) {A J : ℝ}
    (hA : 1 ≤ A) (hJ : 1 ≤ J) (hJA : J ≤ Real.sqrt A)
    (hS : ∀ a ∈ S, A ≤ norm a ∧ norm a ≤ A+A/J) :
    (S.card:ℝ) ≤ 16*(A/J) := by
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hJ0 : 0 < J := zero_lt_one.trans_le hJ
  have hAJ : 0 ≤ A/J := by positivity
  have hB : A+A/J ≤ 2*A := by linarith [div_le_self hA0.le hJ]
  have hs : Real.sqrt (A+A/J) ≤ 2*Real.sqrt A := by
    have hn := Real.sqrt_nonneg (A+A/J)
    have hh := Real.sq_sqrt (show 0 ≤ A+A/J by positivity)
    nlinarith [Real.sq_sqrt hA0.le,Real.sqrt_nonneg A]
  have hr : Real.sqrt A ≤ A/J := by
    apply (le_div_iff₀ hJ0).mpr
    calc
      _ ≤ Real.sqrt A*Real.sqrt A := mul_le_mul_of_nonneg_left hJA (Real.sqrt_nonneg A)
      _ = A := Real.mul_self_sqrt hA0.le
  have hh := eisenstein_annulus_card S hA (by linarith : A ≤ A+A/J) hS
  linarith

end CubicFirstMoment

end

end OAI
