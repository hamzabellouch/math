import OAI.Analysis.Triangular.Auxiliary.IntegralBounds
import OAI.Analysis.Triangular.Envelope.EnvelopeBoxes
import OAI.Analysis.Triangular.Schwartz.SpectralCLM

namespace OAI

noncomputable section
open scoped BigOperators
open Complex Set MeasureTheory
namespace AtomicTriangular.Construction
lemma frequencyDistance_le (l : Fin 31) : frequencyDistance l≤15 := by revert l; decide +kernel
lemma frequencyDistance_eq (l : Fin 31) : |frequency l| = (frequencyDistance l:ℝ)*(1/18) := by
  fin_cases l <;> norm_num [frequency,frequencyDistance]
lemma range_sum_15 (N : ℕ) (hN : N≤15) (F : ℕ → ℝ) :
    (∑ i ∈ Finset.range N, F i) = ∑ i : Fin 15, if i.val<N then F i.val else 0 := by
  rw [show (∑ i : Fin 15, if i.val<N then F i.val else 0) = ∑ i ∈ Finset.range 15, if i<N then F i else 0 by
    exact Fin.sum_univ_eq_sum_range (fun i => if i<N then F i else 0) 15,←Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_range,Finset.mem_filter]
  omega
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
def spectralCVector (n : ℤ) (f : ℝ → E) : E :=
  ∑ l : Fin 31, (fourierCoeff l * exp (I*Real.pi*frequency l*n)) •
    (-(Real.pi:ℂ)^2 • ∫ t in (0:ℝ)..frequency l,
      (frequency l-t) • (exp (-I*Real.pi*(t:ℂ)*n) • f t))
def spectralDVector (n : ℤ) (f : ℝ → E) : E :=
  ∑ l : Fin 31, (fourierCoeff l * exp (I*Real.pi*frequency l*n)) •
    ((I*Real.pi) • ∫ t in (0:ℝ)..frequency l,
      exp (-I*Real.pi*(t:ℂ)*n) • f t)
omit [CompleteSpace E] in
lemma spectralCVector_bound (n : ℤ) (f : ℝ → E) (hf : Continuous f) (M : Fin 15 → ℝ)
    (hM : ∀ i : Fin 15, ∀ x, (i.val:ℝ)/18≤|x| → |x|≤(i.val+1:ℕ)/18 → ‖f x‖≤M i) :
    ‖spectralCVector n f‖ ≤ ∑ i : Fin 15, M i * fullTailW i 0 := by
  let M' : ℕ → ℝ := fun i => if hi : i<15 then M ⟨i,hi⟩ else 0
  have hb (l : Fin 31) :
      ‖∫ t in (0:ℝ)..frequency l, (frequency l-t) • (exp (-I*Real.pi*(t:ℂ)*n) • f t)‖ ≤
      (1/18:ℝ)^2 * ∑ i : Fin 15, if i.val<frequencyDistance l then
        ((frequencyDistance l:ℝ)-i.val-1/2)*M i else 0 := by
    have hh := IntegralVectors.weighted_integral_grid_abs (by norm_num : (0:ℝ)≤1/18)
      (frequencyDistance l) (frequencyDistance_eq l)
      (fun t : ℝ => exp (-I*Real.pi*(t:ℂ)*n) • f t) (by fun_prop) M'
      (fun i hi x h1 h2 => by
        have hi15 : i<15 := lt_of_lt_of_le hi (frequencyDistance_le l)
        rw [norm_smul,norm_exp_neg_phase,one_mul]
        simpa [M',hi15] using hM ⟨i,hi15⟩ x (by convert h1 using 1; ring) (by convert h2 using 1; ring))
    rw [range_sum_15 _ (frequencyDistance_le l)] at hh
    simpa [M',Fin.is_lt] using hh
  unfold spectralCVector
  calc
    _ ≤ ∑ l : Fin 31, ‖(fourierCoeff l*exp (I*Real.pi*frequency l*n)) •
        (-(Real.pi:ℂ)^2 • ∫ t in (0:ℝ)..frequency l,
          (frequency l-t) • (exp (-I*Real.pi*(t:ℂ)*n) • f t))‖ := norm_sum_le _ _
    _ ≤ ∑ l : Fin 31, ‖fourierCoeff l‖ * Real.pi^2*((1/18:ℝ)^2 *
        ∑ i : Fin 15, if i.val<frequencyDistance l then ((frequencyDistance l:ℝ)-i.val-1/2)*M i else 0) := by
      apply Finset.sum_le_sum
      intro l _
      simp only [norm_smul,norm_mul,norm_exp_phase,mul_one,norm_neg,norm_pow,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb l) (show 0≤‖fourierCoeff l‖*Real.pi^2 by positivity)
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp only [fullTailW,Fin.val_zero,↓reduceIte,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      split_ifs <;> ring
omit [CompleteSpace E] in
lemma spectralDVector_bound (n : ℤ) (f : ℝ → E) (hf : Continuous f) (M : Fin 15 → ℝ)
    (hM : ∀ i : Fin 15, ∀ x, (i.val:ℝ)/18≤|x| → |x|≤(i.val+1:ℕ)/18 → ‖f x‖≤M i) :
    ‖spectralDVector n f‖ ≤ ∑ i : Fin 15, M i * fullTailW i 1 := by
  let M' : ℕ → ℝ := fun i => if hi : i<15 then M ⟨i,hi⟩ else 0
  have hb (l : Fin 31) :
      ‖∫ t in (0:ℝ)..frequency l, exp (-I*Real.pi*(t:ℂ)*n) • f t‖ ≤
      (1/18:ℝ) * ∑ i : Fin 15, if i.val<frequencyDistance l then M i else 0 := by
    have hh := IntegralVectors.norm_integral_grid_abs (by norm_num : (0:ℝ)≤1/18)
      (frequencyDistance l) (frequencyDistance_eq l)
      (fun t : ℝ => exp (-I*Real.pi*(t:ℂ)*n) • f t) (by fun_prop) M'
      (fun i hi x h1 h2 => by
        have hi15 : i<15 := lt_of_lt_of_le hi (frequencyDistance_le l)
        rw [norm_smul,norm_exp_neg_phase,one_mul]
        simpa [M',hi15] using hM ⟨i,hi15⟩ x (by convert h1 using 1; ring) (by convert h2 using 1; ring))
    rw [range_sum_15 _ (frequencyDistance_le l)] at hh
    simpa [M',Fin.is_lt] using hh
  unfold spectralDVector
  calc
    _ ≤ ∑ l : Fin 31, ‖(fourierCoeff l*exp (I*Real.pi*frequency l*n)) •
        ((I*Real.pi) • ∫ t in (0:ℝ)..frequency l, exp (-I*Real.pi*(t:ℂ)*n) • f t)‖ := norm_sum_le _ _
    _ ≤ ∑ l : Fin 31, ‖fourierCoeff l‖ * Real.pi*((1/18:ℝ) *
        ∑ i : Fin 15, if i.val<frequencyDistance l then M i else 0) := by
      apply Finset.sum_le_sum
      intro l _
      simp only [norm_smul,norm_mul,norm_exp_phase,mul_one,norm_I,one_mul,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb l) (show 0≤‖fourierCoeff l‖*Real.pi by positivity)
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp only [fullTailW,Fin.val_one,one_ne_zero,↓reduceIte,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      split_ifs <;> ring
end AtomicTriangular.Construction
end

end OAI
