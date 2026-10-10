import OAI.MathematicalPhysics.RapidForcing.MachineDigits

namespace OAI

open scoped BigOperators ENNReal Topology
open Set MeasureTheory
namespace RapidForcing
namespace Machine
variable (M : Machine)

lemma initialDigit_eq (w : M.Input) :
    M.initialDigit w = M.initial.val + (M.scaleData w).S *
      ((M.scaleData w).P 0 * Nat.ofDigits (M.scaleData w).A (w.map Fin.val)) := by
  simp only [initialDigit, Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_zipIdx_map]

lemma initialDigit_lt (w : M.Input) : M.initialDigit w < (M.scaleData w).capacity 0 := by
  let d := M.scaleData w
  have hA : 1 < d.A := lt_of_le_of_lt M.symbols_pos (M.alphabet_lt_A w)
  have hw : ∀ z ∈ w.map Fin.val, z < d.A := by
    intro z hz
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hz
    exact lt_trans a.isLt (M.alphabet_lt_A w)
  have hT := Nat.ofDigits_lt_base_pow_length hA hw
  simp only [List.length_map] at hT
  have hT' : Nat.ofDigits d.A (w.map Fin.val) < d.A ^ (2 * 0 + d.B + 1) := by
    apply lt_of_lt_of_le hT
    apply Nat.pow_le_pow_right d.one_le_A
    change w.length ≤ 2 * 0 + w.length + 1
    omega
  rw [M.initialDigit_eq w, d.capacity_eq]
  have hq : M.initial.val < d.S := lt_trans M.initial.isLt (M.states_lt_S w)
  have hj : 0 < d.P 0 := d.P_pos _
  have h := radix_pair_lt hq (radix_pair_lt hj hT')
  simpa only [zero_add, Nat.mul_assoc] using h

lemma terminalDigit_le_one (d : ScaleData) (k : ℕ) : M.terminalDigit d k ≤ 1 := by
  unfold terminalDigit
  split_ifs <;> omega

end Machine

@[simp] lemma vec_zero_coord (a b c : ℝ) : vec a b c 0 = a := rfl
@[simp] lemma vec_one_coord (a b c : ℝ) : vec a b c 1 = b := rfl
@[simp] lemma vec_two_coord (a b c : ℝ) : vec a b c 2 = c := rfl
@[simp] lemma vec_all_zero : vec 0 0 0 = (0 : Space) := by
  ext i
  fin_cases i <;> rfl

lemma theta_nonneg (t : ℝ) : 0 ≤ θ t := Real.smoothTransition.nonneg _
lemma theta_le_one (t : ℝ) : θ t ≤ 1 := Real.smoothTransition.le_one _
lemma theta_zero {t : ℝ} (h : t ≤ 1 / 4) : θ t = 0 := by
  exact Real.smoothTransition.zero_of_nonpos (by linarith)
lemma theta_one {t : ℝ} (h : 3 / 4 ≤ t) : θ t = 1 := by
  exact Real.smoothTransition.one_of_one_le (by linarith)
lemma theta_smooth : ContDiff ℝ (⊤ : ℕ∞) θ := by
  unfold θ
  fun_prop

def supportBox (c : Space) (r : ℝ) : Set Space := {x | ∀ i : Fin 3, |x i - c i| ≤ r}

lemma supportBox_closed (c : Space) (r : ℝ) : IsClosed (supportBox c r) := by
  unfold supportBox
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro i
  exact isClosed_le (((EuclideanSpace.proj i).continuous.sub continuous_const).abs) continuous_const

lemma zeta_nonneg (v : Space) : 0 ≤ ζ v := by
  apply Finset.prod_nonneg
  intro i _
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma zeta_le_one (v : Space) : ζ v ≤ 1 := by
  apply Finset.prod_le_one₀
  · intro i _
    exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · intro i _
    exact (mul_le_of_le_one_left (Real.smoothTransition.nonneg _)
      (Real.smoothTransition.le_one _)).trans (Real.smoothTransition.le_one _)

lemma zeta_zero {v : Space} {i : Fin 3} (h : 1 / 8 ≤ |v i|) : ζ v = 0 := by
  unfold ζ
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rcases le_or_gt (v i) 0 with hsign | hsign
  · rw [abs_of_nonpos hsign] at h
    rw [Real.smoothTransition.zero_of_nonpos (by linarith : 16 * (v i + 1 / 8) ≤ 0),
      zero_mul]
  · rw [abs_of_nonneg hsign.le] at h
    rw [Real.smoothTransition.zero_of_nonpos (by linarith : 16 * (1 / 8 - v i) ≤ 0),
      mul_zero]

lemma zeta_one {v : Space} (h : ∀ i : Fin 3, |v i| ≤ 1 / 16) : ζ v = 1 := by
  apply Finset.prod_eq_one
  intro i _
  obtain ⟨h₁, h₂⟩ := abs_le.mp (h i)
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 16 * (v i + 1 / 8)),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 16 * (1 / 8 - v i)), one_mul]

lemma zeta_smooth : ContDiff ℝ (⊤ : ℕ∞) ζ := by
  unfold ζ
  fun_prop

lemma curl_tsupport_subset (v : Space → Space) : tsupport (curl v) ⊆ tsupport v := by
  apply closure_minimal _ (isClosed_tsupport v)
  intro x hx
  by_contra hn
  have hd := fderiv_of_notMem_tsupport ℝ hn
  apply hx
  simp [curl, hd]

lemma movingCurl_tsupport_subset (c : ℝ → Space) {δ : ℝ} (hδ : 0 < δ) (σ : ℝ) :
    tsupport (movingCurl c δ σ) ⊆ supportBox (c σ) (δ / 8) := by
  apply (curl_tsupport_subset _).trans
  apply closure_minimal _ (supportBox_closed _ _)
  intro x hx
  change ζ (δ⁻¹ • (x - c σ)) • ((1 / 2 : ℝ) • cross (deriv c σ) (x - c σ)) ≠ 0 at hx
  intro i
  by_contra hn
  have hi : δ / 8 < |x i - c σ i| := lt_of_not_ge hn
  have hco : (δ⁻¹ • (x - c σ)) i = (x i - c σ i) / δ := by
    simp [div_eq_mul_inv, mul_comm]
  have hz : ζ (δ⁻¹ • (x - c σ)) = 0 := by
    apply zeta_zero (i := i)
    rw [hco, abs_div, abs_of_pos hδ]
    apply (le_div_iff₀ hδ).mpr
    linarith
  exact hx (by rw [hz, zero_smul])

end RapidForcing

end OAI
