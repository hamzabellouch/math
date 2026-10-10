import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.CountCoupling

theorem weighted_covariance_identity {ι : Type*} (s : Finset ι)
    (w a b : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, w i * w j * (a i - a j) * (b i - b j)) =
      2 * ((∑ i ∈ s, w i) * (∑ i ∈ s, w i * a i * b i) -
        (∑ i ∈ s, w i * a i) * (∑ i ∈ s, w i * b i)) := by
  calc
    _ = ∑ i ∈ s, ∑ j ∈ s,
        (w i * a i * b i * w j - w i * a i * (w j * b j) -
          w i * b i * (w j * a j) + w i * (w j * a j * b j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul]
      ring

theorem weighted_chebyshev {ι : Type*} (s : Finset ι)
    (w a b : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hab : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ (a i - a j) * (b i - b j)) :
    (∑ i ∈ s, w i * a i) * (∑ i ∈ s, w i * b i) ≤
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * a i * b i) := by
  have hnonneg : 0 ≤ ∑ i ∈ s, ∑ j ∈ s,
      w i * w j * (a i - a j) * (b i - b j) := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    simpa only [mul_assoc] using
      mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) (hab i hi j hj)
  rw [weighted_covariance_identity] at hnonneg
  linarith

theorem weighted_chebyshev_of_monotone {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (w a b : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (ha : MonotoneOn a s) (hb : MonotoneOn b s) :
    (∑ i ∈ s, w i * a i) * (∑ i ∈ s, w i * b i) ≤
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * a i * b i) := by
  apply weighted_chebyshev s w a b hw
  intro i hi j hj
  rcases le_total i j with hij | hji
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (ha hi hj hij))
      (sub_nonpos.mpr (hb hi hj hij))
  · exact mul_nonneg (sub_nonneg.mpr (ha hj hi hji))
      (sub_nonneg.mpr (hb hj hi hji))

theorem monotone_reweighting {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (w a b : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hW : 0 < ∑ i ∈ s, w i)
    (hA : 0 < ∑ i ∈ s, w i * a i)
    (ha : MonotoneOn a s) (hb : MonotoneOn b s) :
    (∑ i ∈ s, w i * b i) / (∑ i ∈ s, w i) ≤
      (∑ i ∈ s, w i * a i * b i) / (∑ i ∈ s, w i * a i) := by
  apply (div_le_div_iff₀ hW hA).mpr
  simpa only [mul_comm] using weighted_chebyshev_of_monotone s w a b hw ha hb

def countWeight (α t : ℕ) : ℝ :=
  1 / ((t.factorial : ℝ) * ((t + α).factorial : ℝ))

theorem countWeight_pos (α t : ℕ) : 0 < countWeight α t := by
  unfold countWeight
  positivity

theorem countWeight_succ (α t : ℕ) :
    countWeight α (t + 1) =
      countWeight α t / (((t : ℝ) + 1) * ((t : ℝ) + 1 + α)) := by
  unfold countWeight
  rw [show t + 1 + α = (t + α) + 1 by omega,
    Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  rw [div_div]
  congr 1
  ring

theorem adjacent_likelihood_monotone (α s : ℕ) :
    MonotoneOn
      (fun y : ℕ => 1 / (((s - y : ℕ) : ℝ) * ((s - y + α : ℕ) : ℝ)))
      (Finset.range s) := by
  intro y hy z hz hyz
  have hys : y < s := Finset.mem_range.mp hy
  have hzs : z < s := Finset.mem_range.mp hz
  have hsub : s - z ≤ s - y := Nat.sub_le_sub_left hyz s
  have hzpos : (0 : ℝ) < (s - z : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hzs
  have hsubR : ((s - z : ℕ) : ℝ) ≤ (s - y : ℕ) := by exact_mod_cast hsub
  apply one_div_le_one_div_of_le
  · have hzpos' : (0 : ℝ) < ((s - z + α : ℕ) : ℝ) := by
      have : 0 < s - z + α := by omega
      exact_mod_cast this
    exact mul_pos hzpos hzpos'
  · push_cast
    exact mul_le_mul hsubR (add_le_add hsubR le_rfl) (by positivity)
      (by positivity)

theorem mean_le_add_top_mass {ι : Type*} (s : Finset ι)
    (w b : ι → ℝ) (a B : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hW : 0 < ∑ i ∈ s, w i)
    (ha : 0 ≤ a) (hB : ∀ i ∈ s, b i ≤ B) :
    (∑ i ∈ s, w i * b i) / (∑ i ∈ s, w i) ≤
      ((∑ i ∈ s, w i * b i) + a * B) / ((∑ i ∈ s, w i) + a) := by
  have hsum : (∑ i ∈ s, w i * b i) ≤ (∑ i ∈ s, w i) * B := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hB i hi) (hw i hi))
  apply (div_le_div_iff₀ hW (by linarith)).mpr
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hsum)]

def pairWeight (α β s y : ℕ) : ℝ :=
  countWeight α y * countWeight β (s - y)

theorem pairWeight_pos (α β s y : ℕ) : 0 < pairWeight α β s y := by
  exact mul_pos (countWeight_pos α y) (countWeight_pos β (s - y))

theorem pairWeight_succ (α β s y : ℕ) (hy : y ≤ s) :
    pairWeight α β (s + 1) y = pairWeight α β s y *
      (1 / (((s + 1 - y : ℕ) : ℝ) * ((s + 1 - y + β : ℕ) : ℝ))) := by
  unfold pairWeight
  have hsub : s + 1 - y = (s - y) + 1 := by omega
  rw [hsub, countWeight_succ]
  push_cast
  ring

def pairExpectation (α β s : ℕ) (b : ℕ → ℝ) : ℝ :=
  (∑ y ∈ Finset.range (s + 1), pairWeight α β s y * b y) /
    (∑ y ∈ Finset.range (s + 1), pairWeight α β s y)

theorem pairExpectation_le_succ (α β s : ℕ) (b : ℕ → ℝ)
    (hb : Monotone b) : pairExpectation α β s b ≤ pairExpectation α β (s + 1) b := by
  let S := Finset.range (s + 1)
  let w := pairWeight α β s
  let a : ℕ → ℝ := fun y =>
    1 / (((s + 1 - y : ℕ) : ℝ) * ((s + 1 - y + β : ℕ) : ℝ))
  have hw : ∀ y ∈ S, 0 ≤ w y := fun y _ => le_of_lt (pairWeight_pos α β s y)
  have hW : 0 < ∑ y ∈ S, w y := by
    apply Finset.sum_pos
    · intro y hy
      exact pairWeight_pos α β s y
    · exact ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hnew : ∀ y ∈ S, w y * a y = pairWeight α β (s + 1) y := by
    intro y hy
    symm
    exact pairWeight_succ α β s y (by have := Finset.mem_range.mp hy; omega)
  have hA : 0 < ∑ y ∈ S, w y * a y := by
    apply Finset.sum_pos
    · intro y hy
      rw [hnew y hy]
      exact pairWeight_pos α β (s + 1) y
    · exact ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hfirst := monotone_reweighting S w a b hw hW hA
    (adjacent_likelihood_monotone β (s + 1)) (hb.monotoneOn _)
  have hnext := mean_le_add_top_mass S (fun y => w y * a y) b
    (pairWeight α β (s + 1) (s + 1)) (b (s + 1))
    (fun y hy => by rw [hnew y hy]; exact le_of_lt (pairWeight_pos α β (s + 1) y))
    hA (le_of_lt (pairWeight_pos α β (s + 1) (s + 1)))
    (fun y hy => hb (by have := Finset.mem_range.mp hy; omega))
  have hnum : (∑ y ∈ S, w y * a y * b y) =
      ∑ y ∈ S, pairWeight α β (s + 1) y * b y := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [hnew y hy]
  have hden : (∑ y ∈ S, w y * a y) =
      ∑ y ∈ S, pairWeight α β (s + 1) y := by
    exact Finset.sum_congr rfl hnew
  rw [hnum, hden] at hfirst hnext
  simpa only [pairExpectation, S, w, Finset.sum_range_succ] using hfirst.trans hnext

theorem pairExpectation_congr (α β s : ℕ) (b c : ℕ → ℝ)
    (h : ∀ y ≤ s, b y = c y) :
    pairExpectation α β s b = pairExpectation α β s c := by
  unfold pairExpectation
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  rw [h y (by have := Finset.mem_range.mp hy; omega)]

theorem sum_pairWeight_reflect (α β s : ℕ) (b : ℕ → ℝ) :
    (∑ y ∈ Finset.range (s + 1), pairWeight α β s y * b y) =
      ∑ y ∈ Finset.range (s + 1), pairWeight β α s y * b (s - y) := by
  calc
    _ = ∑ y ∈ Finset.range (s + 1), pairWeight α β s (s - y) * b (s - y) := by
      simpa using (Finset.sum_range_reflect
        (fun y => pairWeight α β s y * b y) (s + 1)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y hy
      have hys : y ≤ s := by have := Finset.mem_range.mp hy; omega
      have hsub : s - (s - y) = y := by omega
      simp only [pairWeight, hsub]
      ring

theorem pairExpectation_reflect (α β s : ℕ) (b : ℕ → ℝ) :
    pairExpectation α β s b = pairExpectation β α s (fun y => b (s - y)) := by
  unfold pairExpectation
  rw [sum_pairWeight_reflect]
  have hden := sum_pairWeight_reflect α β s (fun _ => (1 : ℝ))
  simp only [mul_one] at hden
  rw [hden]

theorem pairExpectation_neg (α β s : ℕ) (b : ℕ → ℝ) :
    pairExpectation α β s (fun y => -b y) = -pairExpectation α β s b := by
  simp only [pairExpectation, mul_neg, Finset.sum_neg_distrib, neg_div]

theorem pairExpectation_succ_le_of_antitone (α β s : ℕ) (b : ℕ → ℝ)
    (hb : Antitone b) : pairExpectation α β (s + 1) b ≤ pairExpectation α β s b := by
  have h := pairExpectation_le_succ α β s (fun y => -b y)
    (fun _ _ hij => neg_le_neg (hb hij))
  rw [pairExpectation_neg, pairExpectation_neg] at h
  linarith

theorem pairExpectation_succ_le_shift (α β s : ℕ) (b : ℕ → ℝ)
    (hb : Monotone b) :
    pairExpectation α β (s + 1) b ≤ pairExpectation α β s (fun y => b (y + 1)) := by
  let c : ℕ → ℝ := fun y => b (s + 1 - y)
  have hc : Antitone c := by
    intro y z hyz
    exact hb (Nat.sub_le_sub_left hyz (s + 1))
  rw [pairExpectation_reflect α β (s + 1) b]
  calc
    pairExpectation β α (s + 1) c ≤ pairExpectation β α s c :=
      pairExpectation_succ_le_of_antitone β α s c hc
    _ = pairExpectation α β s (fun y => c (s - y)) :=
      pairExpectation_reflect β α s c
    _ = pairExpectation α β s (fun y => b (y + 1)) := by
      apply pairExpectation_congr
      intro y hy
      dsimp [c]
      congr 1
      omega

end Problem315.CountCoupling

end

end OAI
