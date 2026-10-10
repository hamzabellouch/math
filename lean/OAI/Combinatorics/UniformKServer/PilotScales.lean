import Mathlib
import OAI.Combinatorics.UniformKServer.Epochs

namespace OAI

namespace UniformKServer.PilotScales
noncomputable section

theorem scale_logarithms (A B : ℕ → ℝ) (N p : ℕ) (c K : ℝ)
    (hc : 0 < c) (hcK : c ≤ K)
    (hA : ∀ j < N, c ≤ A j)
    (hB : ∀ j < N, A j ≤ B j)
    (hshift : ∀ j < N, B j ≤ if j < p then K else A (j-p)) :
    ∑ j ∈ Finset.range N, Real.log (B j / A j) ≤
      (p : ℝ) * Real.log (K/c) := by
  have hK : 0 < K := lt_of_lt_of_le hc hcK
  have hlog : 0 ≤ Real.log K - Real.log c := by
    linarith [Real.log_le_log hc hcK]
  rw [Real.log_div hK.ne' hc.ne']
  have hpt : ∀ j < N, Real.log (B j/A j) ≤
      (if j < p then Real.log K else Real.log (A (j-p))) - Real.log (A j) := by
    intro j hj
    have ha : 0 < A j := lt_of_lt_of_le hc (hA j hj)
    have hb : 0 < B j := lt_of_lt_of_le ha (hB j hj)
    rw [Real.log_div hb.ne' ha.ne']
    apply sub_le_sub_right
    have hs := Real.log_le_log hb (hshift j hj)
    split_ifs at hs ⊢ <;> exact hs
  calc
    _ ≤ ∑ j ∈ Finset.range N,
        ((if j < p then Real.log K else Real.log (A (j-p))) - Real.log (A j)) :=
      Finset.sum_le_sum fun j hj => hpt j (Finset.mem_range.mp hj)
    _ ≤ (p : ℝ) * (Real.log K - Real.log c) := by
      rw [Finset.sum_sub_distrib]
      by_cases hpN : p ≤ N
      · have hs : (∑ j ∈ Finset.range N,
            if j < p then Real.log K else Real.log (A (j-p))) =
            (p : ℝ)*Real.log K + ∑ j ∈ Finset.range (N-p), Real.log (A j) := by
          conv_lhs => rw [show N = p+(N-p) by omega, Finset.sum_range_add]
          congr 1
          · calc
              _ = ∑ j ∈ Finset.range p, Real.log K := by
                apply Finset.sum_congr rfl
                intro j hj
                simp [Finset.mem_range.mp hj]
              _ = _ := by simp
          · apply Finset.sum_congr rfl
            intro j hj
            simp [show ¬p+j<p by omega]
        have ht : (∑ j ∈ Finset.range N, Real.log (A j)) =
            (∑ j ∈ Finset.range (N-p), Real.log (A j)) +
              ∑ j ∈ Finset.range p, Real.log (A (N-p+j)) := by
          conv_lhs => rw [show N = (N-p)+p by omega, Finset.sum_range_add]
        have hl : (p : ℝ)*Real.log c ≤
            ∑ j ∈ Finset.range p, Real.log (A (N-p+j)) := by
          calc
            _ = ∑ j ∈ Finset.range p, Real.log c := by simp
            _ ≤ _ := Finset.sum_le_sum fun j hj =>
              Real.log_le_log hc (hA _ (by have := Finset.mem_range.mp hj; omega))
        rw [hs, ht]
        nlinarith
      · have hs : (∑ j ∈ Finset.range N,
            if j < p then Real.log K else Real.log (A (j-p))) =
            (N : ℝ)*Real.log K := by
          calc
            _ = ∑ _j ∈ Finset.range N, Real.log K := by
              apply Finset.sum_congr rfl
              intro j hj
              simp [show j<p by have := Finset.mem_range.mp hj; omega]
            _ = _ := by simp
        have hl : (N : ℝ)*Real.log c ≤
            ∑ j ∈ Finset.range N, Real.log (A j) := by
          calc
            _ = ∑ _j ∈ Finset.range N, Real.log c := by simp
            _ ≤ _ := Finset.sum_le_sum fun j hj =>
              Real.log_le_log hc (hA j (Finset.mem_range.mp hj))
        have hnp : (N : ℝ) ≤ p := by exact_mod_cast (show N ≤ p by omega)
        have hm := mul_le_mul_of_nonneg_right hnp hlog
        rw [hs]
        nlinarith

theorem capped_log (u : ℝ) (hu : 0 ≤ u) :
    min 1 u ≤ Real.log (1+u) / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (le_div_iff₀ hl2).mpr
  by_cases hu1 : u ≤ 1
  · rw [min_eq_right hu1]
    have hh := strictConcaveOn_log_Ioi.concaveOn.2
      (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
      (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num)
      (show 0 ≤ 1-u by linarith) hu (show (1-u)+u=1 by ring)
    simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at hh
    convert hh using 1; congr 1; ring
  · rw [min_eq_left (by linarith : 1 ≤ u), one_mul]
    exact Real.log_le_log (by norm_num) (by linarith)

theorem shell_sum (A B : ℕ → ℝ) (N p : ℕ) (c K : ℝ)
    (hc : 0 < c) (hcK : c ≤ K)
    (hA : ∀ j < N, c ≤ A j)
    (hB : ∀ j < N, A j ≤ B j)
    (hshift : ∀ j < N, B j ≤ if j < p then K else A (j-p)) :
    ∑ j ∈ Finset.range N, min 1 ((B j-A j)/A j) ≤
      (p : ℝ) / Real.log 2 * Real.log (K/c) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    _ ≤ ∑ j ∈ Finset.range N, Real.log (B j/A j) / Real.log 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hjN := Finset.mem_range.mp hj
      have ha : 0 < A j := lt_of_lt_of_le hc (hA j hjN)
      have hpos : 0 ≤ (B j-A j)/A j := div_nonneg (sub_nonneg.mpr (hB j hjN)) ha.le
      have he : 1+(B j-A j)/A j = B j/A j := by field_simp; ring
      simpa only [he] using capped_log ((B j-A j)/A j) hpos
    _ = (∑ j ∈ Finset.range N, Real.log (B j/A j)) / Real.log 2 :=
      (Finset.sum_div ..).symm
    _ ≤ ((p : ℝ)*Real.log (K/c)) / Real.log 2 :=
      div_le_div_of_nonneg_right (scale_logarithms A B N p c K hc hcK hA hB hshift) hl2.le
    _ = _ := by ring

/-- Relative increments of positive monotone masses have only logarithmic total. -/
def increment (m : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then m 0 else m i-m (i-1)

theorem increment_nonneg (m : ℕ → ℝ) (hm : Monotone m) (h0 : 0 ≤ m 0) (i : ℕ) :
    0 ≤ increment m i := by
  unfold increment
  split_ifs with hi
  · exact h0
  · exact sub_nonneg.mpr (hm (by omega))

theorem relative_increment (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (b-a)/b ≤ Real.log b - Real.log a := by
  have hh := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at hh
  have he : (b-a)/b = 1-a/b := by field_simp
  rw [he]
  linarith

theorem increment_sum (m : ℕ → ℝ) (hm : ∀ i, 0 < m i) (n : ℕ) :
    (∑ i ∈ Finset.range (n+1), increment m i/m i) ≤
      1+Real.log (m n/m 0) := by
  induction n with
  | zero => simp [increment, div_self (hm 0).ne']
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hstep := relative_increment (m n) (m (n+1)) (hm n) (hm (n+1))
      have he : increment m (n+1) = m (n+1)-m n := by simp [increment]
      rw [he]
      rw [Real.log_div (hm n).ne' (hm 0).ne'] at ih
      rw [Real.log_div (hm (n+1)).ne' (hm 0).ne']
      linarith

def convolution (m : ℕ → ℝ) (τ : ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j+1), (1/τ)^(j-i)*increment m i

theorem geometric_bound (τ : ℝ) (hτ : 2 ≤ τ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (1/τ)^i ≤ 2 := by
  calc
    _ ≤ ∑ i ∈ Finset.range n, (1/2 : ℝ)^i := by
      apply Finset.sum_le_sum
      intro i hi
      exact pow_le_pow_left₀ (by positivity : 0 ≤ 1/τ)
        (one_div_le_one_div_of_le (by norm_num) hτ) i
    _ ≤ 2 := sum_geometric_two_le n

theorem convolution_pointwise (m : ℕ → ℝ) (hm : Monotone m)
    (hpos : ∀ i, 0 < m i) (τ : ℝ) (hτ : 2 ≤ τ) (j : ℕ) :
    convolution m τ j/m j ≤ ∑ i ∈ Finset.range (j+1),
      (increment m i/m i)*(1/τ)^(j-i) := by
  have hτ0 : 0 < τ := by linarith
  unfold convolution
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i hi
  have hij : i ≤ j := by have := Finset.mem_range.mp hi; omega
  have hinc := increment_nonneg m hm (hpos 0).le i
  have hd := div_le_div_of_nonneg_left hinc (hpos i) (hm hij)
  have hp : 0 ≤ (1/τ)^(j-i) := by positivity
  have hh := mul_le_mul_of_nonneg_right hd hp
  convert hh using 1; ring

theorem convolution_total (m : ℕ → ℝ) (hm : Monotone m)
    (hpos : ∀ i, 0 < m i) (τ : ℝ) (hτ : 2 ≤ τ) (N : ℕ) :
    (∑ j ∈ Finset.range N, convolution m τ j/m j) ≤
      2 * ∑ i ∈ Finset.range N, increment m i/m i := by
  have hinc : ∀ i, 0 ≤ increment m i := increment_nonneg m hm (hpos 0).le
  calc
    _ ≤ ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (j+1),
          (increment m i/m i)*(1/τ)^(j-i) :=
      Finset.sum_le_sum fun j hj => convolution_pointwise m hm hpos τ hτ j
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range (N-i),
          (increment m i/m i)*(1/τ)^j :=
      Finset.sum_range_diag_flip N (fun i j => (increment m i/m i)*(1/τ)^j)
    _ ≤ ∑ i ∈ Finset.range N, 2*(increment m i/m i) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← Finset.mul_sum]
      have hh := mul_le_mul_of_nonneg_left (geometric_bound τ hτ (N-i))
        (div_nonneg (hinc i) (hpos i).le)
      simpa only [mul_comm] using hh
    _ = _ := (Finset.mul_sum ..).symm

theorem convolution_succ (m : ℕ → ℝ) (τ : ℝ) (j : ℕ) :
    convolution m τ (j+1) = (1/τ)*convolution m τ j + increment m (j+1) := by
  unfold convolution
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self, pow_zero, one_mul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he : j+1-i = (j-i)+1 := by have := Finset.mem_range.mp hi; omega
  rw [he, pow_succ]
  ring

variable {ι : Type*} [Fintype ι]

def mass (μ d : ι → ℝ) (R : ℝ) : ℝ :=
  ∑ x, if d x ≤ R then μ x else 0

def moment (μ d : ι → ℝ) (R : ℝ) : ℝ :=
  ∑ x, if d x ≤ R then μ x * d x else 0

def radius (r τ : ℝ) (j : ℕ) : ℝ := r * τ^j

theorem mass_nonneg (μ d : ι → ℝ) (hμ : ∀ x, 0 ≤ μ x) (R : ℝ) :
    0 ≤ mass μ d R := by
  apply Finset.sum_nonneg
  intro x hx
  split_ifs
  · exact hμ x
  · exact le_rfl

theorem mass_mono (μ d : ι → ℝ) (hμ : ∀ x, 0 ≤ μ x) : Monotone (mass μ d) := by
  intro R S hRS
  unfold mass
  apply Finset.sum_le_sum
  intro x hx
  split_ifs with hR hS hS
  · rfl
  · exact False.elim (hS (hR.trans hRS))
  · exact hμ x
  · rfl

theorem moment_bound (μ d : ι → ℝ) (hμ : ∀ x, 0 ≤ μ x) (R : ℝ) :
    moment μ d R ≤ R*mass μ d R := by
  unfold moment mass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x hx
  split_ifs with ht
  · nlinarith [mul_le_mul_of_nonneg_left ht (hμ x)]
  · simp

theorem moment_shell (μ d : ι → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (R S : ℝ) (hRS : R ≤ S) :
    moment μ d S ≤ moment μ d R + S*(mass μ d S-mass μ d R) := by
  unfold moment mass
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hx
  by_cases hR : d x ≤ R
  · have hS := hR.trans hRS
    simp [hR, hS]
  · by_cases hS : d x ≤ S
    · simp only [hR, hS, ↓reduceIte, zero_add, sub_zero]
      nlinarith [mul_le_mul_of_nonneg_left hS (hμ x)]
    · simp [hR, hS]

theorem radius_pos (r τ : ℝ) (hr : 0 < r) (hτ : 0 < τ) (j : ℕ) :
    0 < radius r τ j := by unfold radius; positivity

theorem radius_mono (r τ : ℝ) (hr : 0 ≤ r) (hτ : 1 ≤ τ) : Monotone (radius r τ) := by
  apply monotone_nat_of_le_succ
  intro j
  unfold radius
  rw [pow_succ]
  have hp : 0 ≤ τ^j := pow_nonneg (by linarith) j
  have hb := mul_nonneg hr hp
  nlinarith

theorem moment_convolution (μ d : ι → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (r τ γ : ℝ) (hr : 0 < r) (hτ : 2 ≤ τ) (hγ : 0 ≤ γ) (j : ℕ) :
    moment μ d (γ*radius r τ j) ≤
      γ*radius r τ j*convolution (fun i => mass μ d (γ*radius r τ i)) τ j := by
  let m := fun i => mass μ d (γ*radius r τ i)
  have hτ0 : 0 < τ := by linarith
  change _ ≤ γ*radius r τ j*convolution m τ j
  induction j with
  | zero =>
      simpa [convolution, increment, m] using moment_bound μ d hμ (γ*radius r τ 0)
  | succ j ih =>
      have hrs := radius_mono r τ hr.le (by linarith) (Nat.le_succ j)
      have hshell := moment_shell μ d hμ (γ*radius r τ j) (γ*radius r τ (j+1))
        (mul_le_mul_of_nonneg_left hrs hγ)
      have he : increment m (j+1) = m (j+1)-m j := by simp [increment]
      have hid : γ*radius r τ (j+1)*convolution m τ (j+1) =
          γ*radius r τ j*convolution m τ j + γ*radius r τ (j+1)*(m (j+1)-m j) := by
        rw [convolution_succ, he]
        unfold radius
        rw [pow_succ]
        field_simp

      rw [hid]
      change _ ≤ γ*radius r τ j*convolution m τ j +
        γ*radius r τ (j+1)*(mass μ d (γ*radius r τ (j+1))-mass μ d (γ*radius r τ j))
      linarith

theorem pilot_moment_sum (μ d : ι → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (_hd : ∀ x, 0 ≤ d x) (r τ γ : ℝ) (hr : 0 < r) (hτ : 2 ≤ τ)
    (hγ : 0 < γ) (N : ℕ) (hN : 0 < N)
    (hm : 0 < mass μ d (γ*r)) :
    (∑ j ∈ Finset.range N,
      moment μ d (γ * radius r τ j) /
        (radius r τ j * mass μ d (γ * radius r τ j))) ≤
      2*γ*(1+Real.log
        (mass μ d (γ * radius r τ (N-1)) / mass μ d (γ*r))) := by
  let m : ℕ → ℝ := fun j => mass μ d (γ*radius r τ j)
  have hτ0 : 0 < τ := by linarith
  have hm0 : m 0 = mass μ d (γ*r) := by simp [m, radius]
  have hmono : Monotone m := by
    intro i j hij
    exact mass_mono μ d hμ (mul_le_mul_of_nonneg_left
      (radius_mono r τ hr.le (by linarith) hij) hγ.le)
  have hpos : ∀ i, 0 < m i := fun i =>
    lt_of_lt_of_le (by simpa [hm0] using hm) (hmono (Nat.zero_le i))
  have hconv := convolution_total m hmono hpos τ hτ N
  have hinc := increment_sum m hpos (N-1)
  have hn : N-1+1 = N := by omega
  rw [hn] at hinc
  have hpoint : ∀ j, moment μ d (γ*radius r τ j) /
      (radius r τ j*m j) ≤ γ*(convolution m τ j/m j) := by
    intro j
    have hrj := radius_pos r τ hr hτ0 j
    have hh := div_le_div_of_nonneg_right
      (moment_convolution μ d hμ r τ γ hr hτ hγ.le j)
      (mul_nonneg hrj.le (hpos j).le)
    change _ ≤ (γ*radius r τ j*convolution m τ j)/(radius r τ j*m j) at hh
    calc
      _ ≤ _ := hh
      _ = _ := by field_simp
  calc
    _ ≤ ∑ j ∈ Finset.range N, γ*(convolution m τ j/m j) :=
      Finset.sum_le_sum fun j hj => hpoint j
    _ = γ*(∑ j ∈ Finset.range N, convolution m τ j/m j) :=
      (Finset.mul_sum ..).symm
    _ ≤ γ*(2*∑ j ∈ Finset.range N, increment m j/m j) :=
      mul_le_mul_of_nonneg_left hconv hγ.le
    _ ≤ γ*(2*(1+Real.log (m (N-1)/m 0))) := by
      gcongr
    _ = _ := by rw [hm0]; ring

end
end UniformKServer.PilotScales



end OAI
