import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.SmoothFiniteWaveSum

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def finiteWaveAmplitude (V : ℕ → E → ℂ) (J : ℕ) (n : ℝ) (x : E) : ℂ :=
  ∑ j ∈ Finset.range (J+1), ((n : ℂ)⁻¹)^j*V j x

lemma contDiff_finiteWaveAmplitude (V : ℕ → E → ℂ) (hV : ∀ j, ContDiff ℝ ∞ (V j))
    (J : ℕ) (n : ℝ) : ContDiff ℝ ∞ (finiteWaveAmplitude V J n) :=
  ContDiff.sum (fun j _ => contDiff_const.mul (hV j))

omit [NormedSpace ℝ E] in
lemma finiteWaveAmplitude_zero (V : ℕ → E → ℂ)
    (hV0 : ∀ j, V j 0 = if j = 0 then 1 else 0) (J : ℕ) (n : ℝ) :
    finiteWaveAmplitude V J n 0 = 1 := by simp [finiteWaveAmplitude,hV0]

lemma norm_inv_frequency_pow {n : ℝ} (hn : 1 ≤ n) (j : ℕ) : ‖((n : ℂ)⁻¹)^j‖ ≤ 1 := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  rw [norm_pow,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hn0]
  exact pow_le_one₀ (inv_nonneg.mpr hn0.le) ((inv_le_one₀ hn0).mpr hn)

theorem finite_amplitude_near_center (V : X → ℕ → E → ℂ)
    (hV : ∀ p j, ContDiff ℝ ∞ (V p j))
    (hV0 : ∀ p j, V p j 0 = if j = 0 then 1 else 0)
    (hB : ∀ j, UniformJetBounds (fun p => V p j) univ (Metric.closedBall 0 1)) (J : ℕ) :
    ∃ C > 0, ∀ p (n : ℝ), 1 ≤ n → ∀ x ∈ Metric.closedBall 0 1,
      ‖finiteWaveAmplitude (V p) J n x-1‖ ≤ C*‖x‖ ∧
      ∀ v : E, ‖v‖ ≤ 1 → ‖waveDeriv v (finiteWaveAmplitude (V p) J n) x‖ ≤ C := by
  choose C hC hb using fun j => hB j 1
  let T := 1+∑ j ∈ Finset.range (J+1), C j
  have hT : 0 < T := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun j _ => (hC j).le))
  refine ⟨T,hT,?_⟩
  intro p n hn x hx
  have hdiff (j : ℕ) : ‖V p j x-V p j 0‖ ≤ C j*‖x‖ := by
    have hm := (convex_closedBall (0 : E) 1).norm_image_sub_le_of_norm_fderiv_le
      (fun y hy => (hV p j).differentiable (by simp) y)
      (fun y hy => by simpa only [norm_iteratedFDeriv_one] using hb j p (mem_univ _) y hy)
      (Metric.mem_closedBall_self zero_le_one) hx
    simpa only [sub_zero] using hm
  constructor
  · rw [←finiteWaveAmplitude_zero (V p) (hV0 p) J n]
    change ‖(∑ j ∈ Finset.range (J+1), _) - ∑ j ∈ Finset.range (J+1), _‖ ≤ _
    rw [←Finset.sum_sub_distrib]
    simp only [←mul_sub]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ j ∈ Finset.range (J+1), C j*‖x‖ := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_right (norm_inv_frequency_pow hn j) (norm_nonneg _)).trans
          (by simpa only [one_mul] using hdiff j)
      _ ≤ T*‖x‖ := by
        rw [←Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (norm_nonneg _)
  · intro v hv
    unfold finiteWaveAmplitude
    rw [waveDeriv_sum _ _ _ (fun j _ => contDiff_const.mul (hV p j))]
    simp only [waveDeriv_const_mul _ _ _ _ ((hV p _).differentiable (by simp) _)]
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum (fun j hj => ?_)).trans (le_add_of_nonneg_left zero_le_one)
    rw [norm_mul]
    apply (mul_le_mul_of_nonneg_right (norm_inv_frequency_pow hn j) (norm_nonneg _)).trans
    rw [one_mul]
    have hd := norm_iteratedFDeriv_waveDeriv (hV p j) v 0 x
    simp only [norm_iteratedFDeriv_zero] at hd
    exact hd.trans ((mul_le_mul hv (hb j p (mem_univ _) x hx)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

theorem phase_derivative_near_center (S : X → E → ℂ)
    (hS : ∀ p, ContDiff ℝ ∞ (S p))
    (hB : UniformJetBounds S univ (Metric.closedBall 0 1)) :
    ∃ C > 0, ∀ p x, x ∈ Metric.closedBall 0 1 → ∀ v : E, ‖v‖ ≤ 1 →
      ‖waveDeriv v (S p) x‖ ≤ C ∧
      ‖waveDeriv v (S p) x-waveDeriv v (S p) 0‖ ≤ C*‖x‖ := by
  obtain ⟨C1,hC1,hb1⟩ := hB 1
  obtain ⟨C2,hC2,hb2⟩ := hB 2
  refine ⟨max C1 C2,lt_of_lt_of_le hC1 (le_max_left _ _),?_⟩
  intro p x hx v hv
  have hder (y) (hy : y ∈ Metric.closedBall (0 : E) 1) :
      ‖fderiv ℝ (waveDeriv v (S p)) y‖ ≤ C2 := by
    have h := norm_iteratedFDeriv_waveDeriv (hS p) v 1 y
    rw [norm_iteratedFDeriv_one] at h
    exact h.trans ((mul_le_mul hv (hb2 p (mem_univ _) y hy)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  constructor
  · have h := norm_iteratedFDeriv_waveDeriv (hS p) v 0 x
    simp only [norm_iteratedFDeriv_zero] at h
    exact (h.trans ((mul_le_mul hv (hb1 p (mem_univ _) x hx)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _))).trans (le_max_left _ _)
  · have h := (convex_closedBall (0 : E) 1).norm_image_sub_le_of_norm_fderiv_le
      (fun y hy => (contDiff_waveDeriv v _ (hS p)).differentiable (by simp) y) hder
      (Metric.mem_closedBall_self zero_le_one) hx
    have h' : ‖waveDeriv v (S p) x-waveDeriv v (S p) 0‖ ≤ C2*‖x‖ := by
      simpa only [sub_zero] using h
    exact h'.trans (mul_le_mul_of_nonneg_right (le_max_right C1 C2) (norm_nonneg x))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma smoothFiniteWave_normalized_value (S : E → ℂ) (V : ℕ → E → ℂ)
    (J : ℕ) (n : ℝ) (x : E) :
    (Complex.exp ((n : ℂ)*S x))⁻¹*smoothFiniteWave S V J n x = finiteWaveAmplitude V J n x := by
  change _⁻¹*(_*_) = _
  rw [←mul_assoc,inv_mul_cancel₀ (Complex.exp_ne_zero _),one_mul]
  rfl

lemma smoothFiniteWave_normalized_derivative (S : E → ℂ) (V : ℕ → E → ℂ)
    (hS : ContDiff ℝ ∞ S) (hV : ∀ j, ContDiff ℝ ∞ (V j))
    (J : ℕ) {n : ℝ} (hn : n ≠ 0) (x v : E) :
    (n : ℂ)⁻¹*(Complex.exp ((n : ℂ)*S x))⁻¹*waveDeriv v (smoothFiniteWave S V J n) x =
      waveDeriv v S x*finiteWaveAmplitude V J n x +
        (n : ℂ)⁻¹*waveDeriv v (finiteWaveAmplitude V J n) x := by
  have hA := contDiff_finiteWaveAmplitude V hV J n
  change _⁻¹*_⁻¹*waveDeriv v (fun y => Complex.exp ((n : ℂ)*S y)*finiteWaveAmplitude V J n y) x = _
  rw [waveDeriv_mul v _ _ x
    ((contDiff_const.mul hS).cexp.differentiable (by simp) x)
    (hA.differentiable (by simp) x),waveDeriv_exp v S _ x (hS.differentiable (by simp) x)]
  have hn' : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  have he := Complex.exp_ne_zero ((n : ℂ)*S x)
  field_simp

theorem finite_wave_near_center (S : X → E → ℂ) (V : X → ℕ → E → ℂ)
    (hS : ∀ p, ContDiff ℝ ∞ (S p)) (hV : ∀ p j, ContDiff ℝ ∞ (V p j))
    (hV0 : ∀ p j, V p j 0 = if j = 0 then 1 else 0)
    (hSB : UniformJetBounds S univ (Metric.closedBall 0 1))
    (hVB : ∀ j, UniformJetBounds (fun p => V p j) univ (Metric.closedBall 0 1)) (J : ℕ) :
    ∃ C > 0, ∀ p (n : ℝ), 1 ≤ n → ∀ x : E, ‖x‖ ≤ 1/n →
      ‖(Complex.exp ((n : ℂ)*S p x))⁻¹*smoothFiniteWave (S p) (V p) J n x-1‖ ≤ C/n ∧
      ∀ v : E, ‖v‖ ≤ 1 →
        ‖(n : ℂ)⁻¹*(Complex.exp ((n : ℂ)*S p x))⁻¹*
          waveDeriv v (smoothFiniteWave (S p) (V p) J n) x-waveDeriv v (S p) 0‖ ≤ C/n := by
  obtain ⟨A,hA,hAb⟩ := finite_amplitude_near_center V hV hV0 hVB J
  obtain ⟨B,hB,hBb⟩ := phase_derivative_near_center S hS hSB
  let C := A+B*A+B+A
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro p n hn x hx
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hxball : x ∈ Metric.closedBall (0 : E) 1 := by
    simp only [Metric.mem_closedBall,dist_zero_right]
    exact hx.trans (by simpa only [one_div] using (inv_le_one₀ hn0).mpr hn)
  obtain ⟨hval,hder⟩ := hAb p n hn x hxball
  have hav : ‖finiteWaveAmplitude (V p) J n x-1‖ ≤ A/n := by
    exact hval.trans (by simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left hx hA.le)
  constructor
  · rw [smoothFiniteWave_normalized_value]
    exact hav.trans (div_le_div_of_nonneg_right (by dsimp [C]; nlinarith [mul_pos hB hA]) hn0.le)
  · intro v hv
    obtain ⟨hs,hsd⟩ := hBb p x hxball v hv
    have hsd' : ‖waveDeriv v (S p) x-waveDeriv v (S p) 0‖ ≤ B/n :=
      hsd.trans (by simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left hx hB.le)
    rw [smoothFiniteWave_normalized_derivative (S p) (V p) (hS p) (hV p) J hn0.ne']
    have he : waveDeriv v (S p) x*finiteWaveAmplitude (V p) J n x +
        (n : ℂ)⁻¹*waveDeriv v (finiteWaveAmplitude (V p) J n) x-waveDeriv v (S p) 0 =
        (waveDeriv v (S p) x*(finiteWaveAmplitude (V p) J n x-1) +
          (waveDeriv v (S p) x-waveDeriv v (S p) 0)) +
          (n : ℂ)⁻¹*waveDeriv v (finiteWaveAmplitude (V p) J n) x := by ring
    rw [he]
    calc
      _ ≤ ‖waveDeriv v (S p) x‖*‖finiteWaveAmplitude (V p) J n x-1‖ +
          ‖waveDeriv v (S p) x-waveDeriv v (S p) 0‖ +
          ‖(n : ℂ)⁻¹‖*‖waveDeriv v (finiteWaveAmplitude (V p) J n) x‖ := by
        calc
          _ ≤ ‖waveDeriv v (S p) x*(finiteWaveAmplitude (V p) J n x-1) +
                (waveDeriv v (S p) x-waveDeriv v (S p) 0)‖ +
              ‖(n : ℂ)⁻¹*waveDeriv v (finiteWaveAmplitude (V p) J n) x‖ := norm_add_le _ _
          _ ≤ (‖waveDeriv v (S p) x*(finiteWaveAmplitude (V p) J n x-1)‖ +
                ‖waveDeriv v (S p) x-waveDeriv v (S p) 0‖) +
              ‖(n : ℂ)⁻¹*waveDeriv v (finiteWaveAmplitude (V p) J n) x‖ :=
            add_le_add (norm_add_le _ _) le_rfl
          _ = _ := by rw [norm_mul,norm_mul]
      _ ≤ B*(A/n)+B/n+n⁻¹*A := by
        rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hn0]
        exact add_le_add (add_le_add (mul_le_mul hs hav (norm_nonneg _) hB.le) hsd')
          (mul_le_mul_of_nonneg_left (hder v hv) (inv_nonneg.mpr hn0.le))
      _ ≤ C/n := by
        dsimp [C]
        simp only [div_eq_mul_inv]
        have hAn := mul_nonneg hA.le (inv_nonneg.mpr hn0.le)
        nlinarith only [hAn]
end YauCounterexamples

end

end OAI
