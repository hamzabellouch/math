import OAI.Combinatorics.SharpThreshold.FourierBasis
import OAI.Combinatorics.SharpThreshold.RussoReindex

namespace OAI

universe u

noncomputable section
open scoped BigOperators
namespace Problem313.BiasedFourier

variable {ι : Type u} [DecidableEq ι]

/-- The discrete derivative, retained as a function on the full cube. -/
def delta (i : ι) (g : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ :=
  g (Function.update x i true) - g (Function.update x i false)

@[simp] theorem delta_update (i : ι) (g : (ι → Bool) → ℝ)
    (x : ι → Bool) (b : Bool) :
    delta i g (Function.update x i b) = delta i g x := by
  simp [delta, Function.update_idem]

@[simp] theorem delta_delta_fun (i : ι) (g : (ι → Bool) → ℝ) :
    delta i (delta i g) = 0 := by
  funext x
  simp [delta, Function.update_idem]

@[simp] theorem delta_delta (i : ι) (g : (ι → Bool) → ℝ) (x : ι → Bool) :
    delta i (delta i g) x = 0 := by simp [delta]

private theorem char_update_aux (p : ℝ) (S : Finset ι) (i : ι) (hi : i ∉ S)
    (x : ι → Bool) (b : Bool) : char p S (Function.update x i b) = char p S x := by
  unfold char
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]

theorem char_update_of_not_mem (p : ℝ) (S : Finset ι) (x : ι → Bool)
    (i : ι) (b : Bool) (hi : i ∉ S) :
    char p S (Function.update x i b) = char p S x :=
  char_update_aux p S i hi x b

variable [Fintype ι]

/-- Integration by parts against one normalized biased character. -/
theorem integral_chi_eq_sqrt_mul_delta {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (i : ι) (g : (ι → Bool) → ℝ) :
    (∑ x, weight p x * g x * chi p (x i)) =
      Real.sqrt (p * (1-p)) * ∑ x, weight p x * delta i g x := by
  have hpos : 0 < p * (1-p) := mul_pos hp (sub_pos.mpr hp1)
  have hs : Real.sqrt (p * (1-p)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  have hsq : Real.sqrt (p * (1-p)) ^ 2 = p * (1-p) := Real.sq_sqrt hpos.le
  calc
    _ = (∑ x, weight p x * g x * ((if x i = true then (1:ℝ) else 0)-p)) /
          Real.sqrt (p * (1-p)) := by
      simp only [chi, Finset.sum_div, mul_div_assoc]
    _ = (p * (1-p) * ∑ x, weight p x * delta i g x) /
          Real.sqrt (p * (1-p)) := by
      congr 1
      exact sum_weight_centered_coordinate p i g
    _ = _ := by
      apply (div_eq_iff hs).2
      calc
        _ = Real.sqrt (p * (1-p)) ^ 2 * (∑ x, weight p x * delta i g x) := by rw [hsq]
        _ = _ := by ring

/-- Fourier coefficients of a coordinate derivative, with the same full cube on both sides. -/
theorem coeff_insert_eq_sqrt_mul_delta {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (ι → Bool) → ℝ) (i : ι) (A : Finset ι) (hi : i ∉ A) :
    coeff p g (insert i A) =
      Real.sqrt (p * (1-p)) * coeff p (delta i g) A := by
  classical
  have hpos : 0 < p * (1-p) := mul_pos hp (sub_pos.mpr hp1)
  have hs : Real.sqrt (p * (1-p)) ^ 2 = p * (1-p) := Real.sq_sqrt hpos.le
  have hn : Real.sqrt (p * (1-p)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  have hc := Problem313.sum_weight_centered_coordinate p i (fun x => g x * char p A x)
  have hcenter :
      (∑ x, weight p x * (g x * char p A x) *
        ((if x i = true then (1 : ℝ) else 0)-p)) =
      p * (1-p) * coeff p (delta i g) A := by
    calc
      _ = p * (1-p) * ∑ x, weight p x *
          (g (Function.update x i true) * char p A (Function.update x i true) -
           g (Function.update x i false) * char p A (Function.update x i false)) := hc
      _ = _ := by
        congr 1
        unfold coeff
        apply Finset.sum_congr (by ext; simp)
        intro x hx
        rw [char_update_aux p A i hi, char_update_aux p A i hi]
        unfold delta
        ring
  apply mul_left_cancel₀ hn
  calc
    Real.sqrt (p * (1-p)) * coeff p g (insert i A) =
        ∑ x, weight p x * (g x * char p A x) *
          ((if x i = true then (1 : ℝ) else 0)-p) := by
      rw [coeff, Finset.mul_sum]
      apply Finset.sum_congr (by ext; simp)
      intro x hx
      rw [char, Finset.prod_insert hi]
      change Real.sqrt (p * (1-p)) *
        (weight p x * g x * (chi p (x i) * char p A x)) = _
      unfold chi
      field_simp
    _ = p * (1-p) * coeff p (delta i g) A := hcenter
    _ = Real.sqrt (p * (1-p)) *
        (Real.sqrt (p * (1-p)) * coeff p (delta i g) A) := by rw [← mul_assoc, ← pow_two, hs]

/-- Erasing a coordinate from a nonzero-degree coefficient gives the derivative coefficient. -/
theorem coeff_eq_sqrt_mul_delta_erase {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (ι → Bool) → ℝ) (i : ι) (S : Finset ι) (hi : i ∈ S) :
    coeff p g S = Real.sqrt (p * (1-p)) * coeff p (delta i g) (S.erase i) := by
  conv_lhs => rw [← Finset.insert_erase hi]
  exact coeff_insert_eq_sqrt_mul_delta hp hp1 g i (S.erase i) (Finset.notMem_erase i S)

/-- Squared Fourier derivative identity, in the normalization used by Dirichlet energy. -/
theorem coeff_sq_eq_variance_mul_delta_erase_sq {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (ι → Bool) → ℝ) (i : ι) (S : Finset ι) (hi : i ∈ S) :
    coeff p g S ^ 2 = p * (1-p) * coeff p (delta i g) (S.erase i) ^ 2 := by
  rw [coeff_eq_sqrt_mul_delta_erase hp hp1 g i S hi, mul_pow,
    Real.sq_sqrt (mul_nonneg hp.le (sub_nonneg.mpr hp1.le))]

/-- A coordinate derivative has no Fourier support containing that coordinate. -/
theorem coeff_delta_eq_zero_of_mem {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (ι → Bool) → ℝ) (i : ι) (S : Finset ι) (hi : i ∈ S) :
    coeff p (delta i g) S = 0 := by
  classical
  rw [← Finset.insert_erase hi]
  rw [coeff_insert_eq_sqrt_mul_delta hp hp1 (delta i g) i (S.erase i)
    (Finset.notMem_erase i S)]
  simp [coeff]

/-- The Fourier derivative identity with coordinate-first parameter order. -/
theorem coeff_insert_eq_sqrt_mul_coeff_delta {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (i : ι) (g : (ι → Bool) → ℝ) (A : Finset ι) (hi : i ∉ A) :
    coeff p g (insert i A) = Real.sqrt (p * (1-p)) * coeff p (delta i g) A :=
  coeff_insert_eq_sqrt_mul_delta hp hp1 g i A hi

/-- The Fourier derivative identity with coordinate-first parameter order. -/
theorem coeff_delta_eq_zero {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (i : ι) (g : (ι → Bool) → ℝ) (S : Finset ι) (hi : i ∈ S) :
    coeff p (delta i g) S = 0 :=
  coeff_delta_eq_zero_of_mem hp hp1 g i S hi

end Problem313.BiasedFourier

end

end OAI
