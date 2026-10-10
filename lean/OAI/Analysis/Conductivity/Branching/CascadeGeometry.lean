import Mathlib
import OAI.Analysis.Conductivity.Variational.ScaledSmoothSeries

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

def cascadePhase (D k : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  (2:ℝ)^j*(k*t-2*D)+2*D

lemma cascadePhase_zero (D k t : ℝ) : cascadePhase D k 0 t = k*t := by
  simp [cascadePhase]

lemma cascadePhase_succ (D k t : ℝ) (j : ℕ) :
    cascadePhase D k (j+1) t = 2*(cascadePhase D k j t-D) := by
  unfold cascadePhase
  rw [pow_succ]
  ring

lemma cascadePhase_add (D k t : ℝ) (j n : ℕ) :
    cascadePhase D k (j+n) t = (2:ℝ)^n*(cascadePhase D k j t-2*D)+2*D := by
  unfold cascadePhase
  rw [pow_add]
  ring

lemma cascadePhase_antitone {D k t : ℝ} (ht : k*t ≤ 2*D) :
    Antitone (fun j => cascadePhase D k j t) := by
  apply antitone_nat_of_succ_le
  intro j
  have hp : 0 ≤ (2:ℝ)^j := by positivity
  rw [cascadePhase_succ]
  have : cascadePhase D k j t ≤ 2*D := by
    unfold cascadePhase
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hp (by linarith : k*t-2*D≤0)]
  linarith

lemma cascadePhase_before {D k t : ℝ} (hD : 0 < D) {i j : ℕ}
    (hij : i < j) (hj : 0 ≤ cascadePhase D k j t) :
    D ≤ cascadePhase D k i t := by
  by_cases ht : k*t ≤ 2*D
  · have h := cascadePhase_antitone ht (show i+1≤j by omega)
    dsimp only at h
    rw [cascadePhase_succ] at h
    linarith
  · have hp : 0 ≤ (2:ℝ)^i := by positivity
    have : 0 ≤ (2:ℝ)^i*(k*t-2*D) := mul_nonneg hp (by linarith)
    unfold cascadePhase
    linarith

lemma cascadePhase_after {D k t : ℝ} (hD : 0 < D) {i j : ℕ}
    (hij : j+1 < i) (hj : cascadePhase D k j t ≤ D) :
    cascadePhase D k i t ≤ -2*D := by
  have ht : k*t ≤ 2*D := by
    by_contra hh
    have hp : 0 < (2:ℝ)^j := by positivity
    have : 0 < (2:ℝ)^j*(k*t-2*D) := mul_pos hp (by linarith)
    unfold cascadePhase at hj
    linarith
  have h := cascadePhase_antitone ht (show j + 2 ≤ i by omega)
  dsimp only at h
  rw [show j+2=(j+1)+1 by omega,cascadePhase_succ,cascadePhase_succ] at h
  linarith

lemma cascadeProfile_only_two {L K k t : ℝ} (hL : 0 < L) (hK : 0 < K)
    {j i : ℕ} (hj₁ : 0 ≤ cascadePhase (cascadeLength L K) k j t)
    (hj₂ : cascadePhase (cascadeLength L K) k j t ≤ cascadeLength L K)
    (hi : i ≠ j) (hi' : i ≠ j+1) :
    cascadeProfile L K (cascadePhase (cascadeLength L K) k i t) = 0 := by
  have hD := cascade_length_positive hL hK
  by_cases hij : i < j
  · apply cascadeProfile_zero_right hL
    have hh := cascadePhase_before hD hij hj₁
    change K+2+2*L ≤ cascadePhase (cascadeLength L K) k i t at hh
    linarith
  · apply cascadeProfile_zero_left hL
    have hh := cascadePhase_after hD (show j+1 < i by omega) hj₂
    change cascadePhase (cascadeLength L K) k i t ≤ -2*(K+2+2*L) at hh
    linarith

lemma cascadeProfile_terminal {L K k t : ℝ} (hL : 0 < L) (hK : 0 < K)
    (ht : 2*cascadeLength L K ≤ k*t) (j : ℕ) :
    cascadeProfile L K (cascadePhase (cascadeLength L K) k j t) = 0 := by
  apply cascadeProfile_zero_right hL
  have hp : 0 ≤ (2:ℝ)^j*(k*t-2*cascadeLength L K) :=
    mul_nonneg (by positivity) (by linarith)
  unfold cascadePhase cascadeLength at *
  linarith

lemma exists_cascade_stage {D k t : ℝ} (_ : 0 < D)
    (ht₀ : 0 ≤ k*t) (ht : k*t < 2*D) :
    ∃ j : ℕ, 0 ≤ cascadePhase D k j t ∧ cascadePhase D k j t ≤ D := by
  have hex : ∃ j : ℕ, cascadePhase D k j t ≤ D := by
    obtain ⟨j,hj⟩ := pow_unbounded_of_one_lt (D/(2*D-k*t)) (by norm_num : (1:ℝ)<2)
    refine ⟨j,?_⟩
    have hh : D ≤ (2:ℝ)^j*(2*D-k*t) := by
      exact (div_le_iff₀ (by linarith : 0<2*D-k*t)).mp hj.le
    unfold cascadePhase
    nlinarith
  let j := Nat.find hex
  refine ⟨j,?_,Nat.find_spec hex⟩
  cases hj : j with
  | zero => simpa [hj,cascadePhase_zero] using ht₀
  | succ n =>
    have hn : n < Nat.find hex := by change n < j; omega
    have hh := Nat.find_min hex hn
    rw [not_le] at hh
    rw [cascadePhase_succ]
    linarith

def cascadeAxis (j : ℕ) : Fin 3 := if Even j then 1 else 2

lemma cascadeAxis_ne_zero (j : ℕ) : cascadeAxis j ≠ 0 := by
  unfold cascadeAxis
  split <;> decide

lemma cascadeAxis_succ (j : ℕ) : cascadeAxis (j+1) = if Even j then 2 else 1 := by
  simp only [cascadeAxis,Nat.even_add_one]
  split <;> simp_all

def cascadeCenter (D k : ℝ) (j : ℕ) : Coord3 :=
  Pi.single 0 ((2*D/k)*(1-1/(2:ℝ)^j))

lemma cascade_dilation_time {k : ℝ} (hk : k ≠ 0) (D : ℝ) (j : ℕ) (x : Coord3) :
    ((k*2^j) • (x-cascadeCenter D k j)) 0 = cascadePhase D k j (x 0) := by
  simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul,cascadeCenter,Pi.single_eq_same,cascadePhase]
  field_simp
  ring

lemma cascade_dilation_angular (D k : ℝ) (j : ℕ) (x : Coord3) :
    ((k*2^j) • (x-cascadeCenter D k j)) (cascadeAxis j) = k*2^j*x (cascadeAxis j) := by
  simp [cascadeCenter,Pi.single_eq_of_ne (cascadeAxis_ne_zero j)]

def cascadeTerm (L K k A : ℝ) (j : ℕ) (x : Coord3) : ℝ :=
  (A*cascadeRatio L K^j)*cascadeProfile L K (cascadePhase (cascadeLength L K) k j (x 0))*
    cos (k*2^j*x (cascadeAxis j))

def cascadeValue (L K k A : ℝ) (x : Coord3) : ℝ := ∑' j : ℕ, cascadeTerm L K k A j x

lemma cascadeTerm_scaled {k : ℝ} (hk : k ≠ 0) (L K A : ℝ) (j : ℕ) (x : Coord3) :
    cascadeTerm L K k A j x = (A*cascadeRatio L K^j)*
      cascadeMother L K (cascadeAxis j) ((k*2^j) • (x-cascadeCenter (cascadeLength L K) k j)) := by
  rw [cascadeMother,cascade_dilation_time hk,cascade_dilation_angular]
  unfold cascadeTerm
  ring

theorem cascadeValue_C2 {L K k : ℝ} (hL : 1 ≤ L) (hK : 0 < K) (hk : k ≠ 0) (A : ℝ) :
    ContDiff ℝ 2 (cascadeValue L K k A) := by
  have hh := geometric_scaled_C2
    (f := fun j => cascadeMother L K (cascadeAxis j))
    (fun _ => cascadeMother_smooth _ _ _)
    (fun n => by
      obtain ⟨C,hC,hb⟩ := cascadeMother_iterated_bound (lt_of_lt_of_le (by norm_num) hL) n
      exact ⟨C,hC,fun j x => hb (cascadeAxis j) x⟩)
    (cascadeRatio_pos L K).le (cascadeRatio_small hL hK) A k
    (cascadeCenter (cascadeLength L K) k)
  convert hh using 1
  funext x
  exact tsum_congr fun j => cascadeTerm_scaled hk L K A j x

lemma cascadeValue_terminal {L K k : ℝ} (hL : 0 < L) (hK : 0 < K) (A : ℝ)
    (x : Coord3) (hx : 2*cascadeLength L K ≤ k*x 0) : cascadeValue L K k A x = 0 := by
  change (∑' j : ℕ, cascadeTerm L K k A j x) = 0
  have h : ∀ j, cascadeTerm L K k A j x = 0 := by
    intro j
    rw [cascadeTerm,cascadeProfile_terminal hL hK hx,mul_zero,zero_mul]
  simp only [h,tsum_zero]

lemma cascadeValue_two_modes {L K k : ℝ} (hL : 0 < L) (hK : 0 < K) (A : ℝ)
    (x : Coord3) (j : ℕ) (hj₁ : 0 ≤ cascadePhase (cascadeLength L K) k j (x 0))
    (hj₂ : cascadePhase (cascadeLength L K) k j (x 0) ≤ cascadeLength L K) :
    cascadeValue L K k A x = cascadeTerm L K k A j x + cascadeTerm L K k A (j+1) x := by
  have h : (∑' i : ℕ, cascadeTerm L K k A i x) = ∑ i ∈ ({j,j+1} : Finset ℕ), cascadeTerm L K k A i x := tsum_eq_sum (s := ({j,j+1} : Finset ℕ)) (f := fun i => cascadeTerm L K k A i x) (by
    intro i hi
    have hi₁ : i ≠ j := by simpa using fun h => hi (by simp [h])
    have hi₂ : i ≠ j+1 := by simpa using fun h => hi (by simp [h])
    rw [cascadeTerm,cascadeProfile_only_two hL hK hj₁ hj₂ hi₁ hi₂,mul_zero,zero_mul])
  simpa [cascadeValue,Finset.sum_pair (show j ≠ j+1 by omega)] using h

lemma cascadeValue_zero_phase {L K k : ℝ} (hL : 0 < L) (hK : 0 < K) (A : ℝ)
    (x : Coord3) (hx : x 0 = 0) : cascadeValue L K k A x = A*cos (k*x 1) := by
  have h₁ : 0 ≤ cascadePhase (cascadeLength L K) k 0 (x 0) := by simp [cascadePhase_zero,hx]
  have h₂ : cascadePhase (cascadeLength L K) k 0 (x 0) ≤ cascadeLength L K := by
    simpa [cascadePhase_zero,hx] using (cascade_length_positive hL hK).le
  rw [cascadeValue_two_modes hL hK A x 0 h₁ h₂]
  have hz : cascadeProfile L K (cascadePhase (cascadeLength L K) k 1 (x 0)) = 0 := by
    apply cascadeProfile_zero_left hL
    simp [cascadePhase,hx,cascadeLength]
    linarith
  rw [cascadeTerm,cascadeTerm,hz]
  simp [cascadePhase_zero,hx,cascadeProfile_connector hL (le_refl 0) (show (0:ℝ)≤K+2 by linarith),
    connectorProfile,cascadeAxis]

end ScalarConductivity

end

end OAI
