import Mathlib
import OAI.Probability.JammingConcavity.DeletionUniformGapCountFailureBound

namespace OAI

/-! Deletion Uniform Row Estimates. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open scoped Topology NNReal
open scoped Topology BigOperators
open scoped ENNReal NNReal
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
open Classical
open scoped ENNReal NNReal Topology BigOperators MatrixOrder
open scoped NNReal BigOperators
open MeasureTheory Metric Set
open Metric
open scoped RealInnerProductSpace
namespace MicroscopicJamming

 
lemma net_power_cancel {b k : ℕ} (hbk : b ≤ k) {L a c : ℝ} (hc : c ≠ 0) :
    (L/c)^b * (a*c)^k = L^b * a^k * c^(k-b) := by
  have hcp : c^k = c^b * c^(k-b) := by
    rw [← pow_add, Nat.add_sub_of_le hbk]
  rw [div_pow, mul_pow, hcp]
  field_simp

 

lemma row_net_geometric_bound {m n b k B q : ℕ} {L a d : ℝ}
    (hL : 1 ≤ L) (ha : 1 ≤ a) (hd : 0 < d) (hd1 : d ≤ 1)
    (hm : m ≤ B*n) (hbk : b ≤ k) (hkn : k ≤ n) (hslack : n ≤ q*(k-b)) :
    (2:ℝ)^m * (L/(d^q))^b * ((2:ℝ)^n * (a*d^q)^k) ≤
      ((2:ℝ)^(B+1)*L*a*d)^n := by
  have hb : b ≤ n := hbk.trans hkn
  have hcan := net_power_cancel hbk (L := L) (a := a) (pow_ne_zero q hd.ne')
  have hdq : 0 < d^q := pow_pos hd q
  calc
    _ = (2:ℝ)^(m+n) * (L^b * a^k * (d^q)^(k-b)) := by
      rw [pow_add, ← hcan]
      ring
    _ ≤ (2:ℝ)^((B+1)*n) * (L^n * a^n * d^n) := by
      apply mul_le_mul
      · exact pow_le_pow_right₀ (by norm_num) (by nlinarith)
      · apply mul_le_mul
        · exact mul_le_mul (pow_le_pow_right₀ hL hb) (pow_le_pow_right₀ ha hkn)
            (by positivity) (by positivity)
        · rw [← pow_mul]
          exact pow_le_pow_of_le_one hd.le hd1 hslack
        · positivity
        · positivity
      · positivity
      · positivity
    _ = _ := by rw [pow_mul]; ring

 

lemma gap_net_geometric_bound {m n k B q : ℕ} {L a d : ℝ}
    (hL : 1 ≤ L) (ha : 1 ≤ a) (hd : 0 < d) (hd1 : d ≤ 1)
    (hm : m ≤ B*n) (hnk : n ≤ k) (hk : k ≤ 2*n) (hslack : n ≤ q*(k-n)) :
    (L/(d^q))^n * ((2:ℝ)^m * (a*d^q)^k) ≤
      (L*(2:ℝ)^B*a^2*d)^n := by
  have hcan := net_power_cancel hnk (L := L) (a := a) (pow_ne_zero q hd.ne')
  calc
    _ = (2:ℝ)^m * (L^n * a^k * (d^q)^(k-n)) := by rw [← hcan]; ring
    _ ≤ (2:ℝ)^(B*n) * (L^n * a^(2*n) * d^n) := by
      apply mul_le_mul
      · exact pow_le_pow_right₀ (by norm_num) hm
      · apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ha hk) (by positivity)
        · rw [← pow_mul]
          exact pow_le_pow_of_le_one hd.le hd1 hslack
        · positivity
        · positivity
      · positivity
      · positivity
    _ = _ := by simp only [pow_mul, mul_pow]; ring

 

lemma geometry_indices {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1/8)
    {q n : ℕ} (hq : 8 ≤ ρ*q) (hn : q ≤ n) :
    let b := ⌊(1-ρ)*(n:ℝ)⌋₊
    let k := ⌊(1-ρ/2)*(n:ℝ)⌋₊
    let j := ⌈(1+ρ/4)*(n:ℝ)⌉₊
    b ≤ k ∧ k ≤ n ∧ n ≤ q*(k-b) ∧
      ρ*n/4 ≤ (n:ℝ)-k ∧
      n ≤ j ∧ j ≤ 2*n ∧ n ≤ q*(j-n) ∧
      ρ*n/16 ≤ (1+ρ/2)*n-j := by
  dsimp only
  let b := ⌊(1-ρ)*(n:ℝ)⌋₊
  let k := ⌊(1-ρ/2)*(n:ℝ)⌋₊
  let j := ⌈(1+ρ/4)*(n:ℝ)⌉₊
  have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hq0 : 0 ≤ (q:ℝ) := Nat.cast_nonneg _
  have hqn : (q:ℝ) ≤ n := by exact_mod_cast hn
  have hlarge : 8 ≤ ρ*n := hq.trans (mul_le_mul_of_nonneg_left hqn hρ.le)
  have hn1 : 1 ≤ (n:ℝ) := by nlinarith
  have hb0 : 0 ≤ (1-ρ)*(n:ℝ) := mul_nonneg (by linarith) hn0
  have hk0 : 0 ≤ (1-ρ/2)*(n:ℝ) := mul_nonneg (by linarith) hn0
  have hj0 : 0 ≤ (1+ρ/4)*(n:ℝ) := mul_nonneg (by linarith) hn0
  have hbU : (b:ℝ) ≤ (1-ρ)*n := Nat.floor_le hb0
  have hkU : (k:ℝ) ≤ (1-ρ/2)*n := Nat.floor_le hk0
  have hkL : (1-ρ/2)*(n:ℝ) < k+1 := Nat.lt_floor_add_one _
  have hjU : (j:ℝ) < (1+ρ/4)*n+1 := Nat.ceil_lt_add_one hj0
  have hjL : (1+ρ/4)*(n:ℝ) ≤ j := Nat.le_ceil _
  have hbk : b ≤ k := Nat.floor_mono (by nlinarith : (1-ρ)*(n:ℝ) ≤ (1-ρ/2)*n)
  have hkn : k ≤ n := by exact_mod_cast (show (k:ℝ) ≤ n by nlinarith)
  have hnk : n ≤ j := by exact_mod_cast (show (n:ℝ) ≤ j by nlinarith)
  have hdiff : ρ*n/4 ≤ (k:ℝ)-b := by nlinarith
  have hgdiff : ρ*n/4 ≤ (j:ℝ)-n := by nlinarith
  have hsn := mul_le_mul_of_nonneg_right hq hn0
  have hsl := mul_le_mul_of_nonneg_left hdiff hq0
  have hgsl := mul_le_mul_of_nonneg_left hgdiff hq0
  refine ⟨hbk, hkn, ?_, ?_, hnk, ?_, ?_, ?_⟩
  · have hh : (n:ℝ) ≤ q*((k:ℝ)-b) := by nlinarith
    exact_mod_cast hh
  · nlinarith
  · have hh : (j:ℝ) ≤ 2*n := by nlinarith
    exact_mod_cast hh
  · have hh : (n:ℝ) ≤ q*((j:ℝ)-n) := by nlinarith
    exact_mod_cast hh
  · nlinarith

end MicroscopicJamming

namespace MicroscopicJamming

lemma lower_bound_of_unit {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (c : ℝ)
    (h : ∀ v : E, ‖v‖ = 1 → c ≤ ‖L v‖) (v : E) : c*‖v‖ ≤ ‖L v‖ := by
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have heq : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by simp [norm_smul, hn.ne']
  have hh := h ((‖v‖⁻¹ : ℝ) • v) heq
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)] at hh
  have hmul := mul_le_mul_of_nonneg_right hh hn.le
  calc
    c*‖v‖ ≤ (‖v‖⁻¹ * ‖L v‖)*‖v‖ := hmul
    _ = ‖L v‖ := by field_simp

 
def RowGeometry {m n : ℕ} (ρ K c u : ℝ) (A : Fin m → Fin n → ℝ) : Prop :=
  ‖matrixOperator A‖ ≤ K*Real.sqrt n ∧
  (∀ T : Finset (Fin m), (T.card:ℝ) ≤ (1-ρ)*n →
    ∀ v : EuclideanSpace ℝ T,
      c*Real.sqrt n*‖v‖ ≤ ‖(matrixOperator A).adjoint (rowEmbedding T v)‖) ∧
  (∀ y : EuclideanSpace ℝ (Fin n), ‖y‖ = 1 →
    (nearGapCount A y u:ℝ) ≤ (1+ρ/2)*n)

 
lemma small_power_choice {D : ℝ} (hD : 1 ≤ D) (q : ℕ) :
    let d := Real.exp (-1) / D
    0 < d ∧ d ≤ 1 ∧ 0 < d^q ∧ d^q ≤ 1 ∧ D*d = Real.exp (-1) := by
  dsimp only
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hdp : 0 < Real.exp (-1) / D := div_pos (Real.exp_pos _) hDp
  have he : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hd1 : Real.exp (-1) / D ≤ 1 := (div_le_one hDp).mpr (he.trans hD)
  exact ⟨hdp, hd1, pow_pos hdp q, pow_le_one₀ hdp.le hd1,
    mul_div_cancel₀ _ hDp.ne'⟩

lemma exp_neg_one_pow (n : ℕ) : (Real.exp (-1))^n = Real.exp (-(n:ℝ)) := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

 
lemma mixture_operator_geometric {m n B : ℕ} {ε : ℝ}
    (he : ε ∈ Set.Icc (0:ℝ) (1/2)) (hm : m ≤ B*n) :
    (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => coordinateLaw ε).real
      {A | (12*((B:ℝ)+1))*Real.sqrt n < ‖matrixOperator A‖} ≤
        2*Real.exp (-(n:ℝ)) := by
  let K : ℝ := 12*((B:ℝ)+1)
  have hK : 0 < K := by dsimp [K]; positivity
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have ht : 0 ≤ (K/2)*Real.sqrt n := by positivity
  have htail := mixture_operator_tail (m := m) (n := n) he ht
  have heq : 2*(K/2*Real.sqrt n) = K*Real.sqrt n := by ring
  rw [heq] at htail
  have h9 : (9:ℝ) ≤ Real.exp 9 := le_trans (by norm_num) (Real.add_one_le_exp 9)
  have hm' : (m:ℝ)+(n:ℝ) ≤ ((B:ℝ)+1)*n := by exact_mod_cast (show m+n ≤ (B+1)*n by nlinarith)
  have hpow : (9:ℝ)^(m+n) ≤ Real.exp (9*((B:ℝ)+1)*n) := by
    calc
      _ ≤ (Real.exp 9)^(m+n) := pow_le_pow_left₀ (by norm_num) h9 _
      _ = Real.exp (9*((m:ℝ)+n)) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hsq : ((K/2)*Real.sqrt n)^2/3 = (K^2/12)*n := by
    rw [mul_pow, Real.sq_sqrt hn]
    ring
  have hlarge : 9*((B:ℝ)+1) + 1 ≤ K^2/12 := by
    dsimp [K]
    nlinarith [show 0 ≤ (B:ℝ) by positivity]
  calc
    _ ≤ 2*(9:ℝ)^(m+n)*Real.exp (-((K/2)*Real.sqrt n)^2/3) := htail
    _ ≤ 2*Real.exp (9*((B:ℝ)+1)*n)*Real.exp (-((K/2)*Real.sqrt n)^2/3) := by
      gcongr
    _ = 2*Real.exp ((9*((B:ℝ)+1)-K^2/12)*n) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      rw [neg_div, hsq]
      ring
    _ ≤ _ := by
      gcongr
      nlinarith [mul_le_mul_of_nonneg_right hlarge hn]

end MicroscopicJamming

namespace MicroscopicJamming

lemma uniform_row_geometric {ρ K : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1/8)
    (hK : 0 < K) (B q : ℕ) (hq : 8 ≤ ρ*q) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ {m n : ℕ}, q ≤ n → m ≤ B*n →
      ∀ {ε : ℝ}, ε ∈ Set.Icc (0:ℝ) (1/2) →
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => coordinateLaw ε).real
        {A | ‖matrixOperator A‖ ≤ K*Real.sqrt n ∧
          ∃ T : Finset (Fin m), (T.card:ℝ) ≤ (1-ρ)*n ∧
            ∃ v : EuclideanSpace ℝ T, ‖v‖ = 1 ∧
              ‖(matrixOperator A).adjoint (rowEmbedding T v)‖ < c*Real.sqrt n} ≤
          Real.exp (-(n:ℝ)) := by
  let a : ℝ := 8/Real.sqrt ρ
  let L : ℝ := 1+2*K
  let D : ℝ := (2:ℝ)^(B+1)*L*a
  let d : ℝ := Real.exp (-1)/D
  let c : ℝ := d^q
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have hs1 : Real.sqrt ρ ≤ 1 := by nlinarith [Real.sq_sqrt hρ.le]
  have ha : 1 ≤ a := (le_div_iff₀ hs).mpr (by linarith)
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hD : 1 ≤ D := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hL) ha
  obtain ⟨hd, hd1, hc, hc1, hDd⟩ := small_power_choice hD q
  change 0 < d at hd
  change d ≤ 1 at hd1
  change 0 < c at hc
  change c ≤ 1 at hc1
  change D*d = Real.exp (-1) at hDd
  refine ⟨c, hc, hc1, ?_⟩
  intro m n hn hm ε he
  let b := ⌊(1-ρ)*(n:ℝ)⌋₊
  let k := ⌊(1-ρ/2)*(n:ℝ)⌋₊
  obtain ⟨hbk, hkn, hslack, hgap, _⟩ := geometry_indices hρ hρ1 hq hn
  have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hnlarge : 8 ≤ ρ*n := hq.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hn) hρ.le)
  have hnp : 0 < (n:ℝ) := by nlinarith
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnp
  have harg : 0 ≤ (1-ρ)*(n:ℝ) := mul_nonneg (by linarith) hn0
  have ht : 0 < 4*c/Real.sqrt ρ := div_pos (by positivity) hs
  have hsmall : (2*(c*Real.sqrt n))^2 ≤ ((n:ℝ)-k)*(4*c/Real.sqrt ρ)^2 := by
    calc
      _ = (ρ*n/4)*(4*c/Real.sqrt ρ)^2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hn0, div_pow, Real.sq_sqrt hρ.le]
        field_simp
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hgap (sq_nonneg _)
  have hf := uniform_row_lower_failure_bound (m := m) (n := n) he b k (mul_pos hK hsn)
    (mul_pos hc hsn) ht hsmall
  have hratio : 1+2*(K*Real.sqrt n)/(c*Real.sqrt n) = 1+2*K/c := by
    field_simp
  have hinterval : 2*(4*c/Real.sqrt ρ) = a*c := by dsimp [a]; ring
  rw [hratio, hinterval] at hf
  have hfin := ENNReal.toReal_mono (by finiteness) hf
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at hfin
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at hfin
  have hbase : 1+2*K/c ≤ L/c := by
    apply (le_div_iff₀ hc).mpr
    calc
      (1+2*K/c)*c = c+2*K := by field_simp
      _ ≤ L := by dsimp [L]; linarith
  have hgeo := row_net_geometric_bound hL ha hd hd1 hm hbk hkn hslack
  change (2:ℝ)^m*(L/c)^b*((2:ℝ)^n*(a*c)^k) ≤ (D*d)^n at hgeo
  rw [hDd, exp_neg_one_pow] at hgeo
  calc
    _ ≤ (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => coordinateLaw ε).real
        {A | ‖matrixOperator A‖ ≤ K*Real.sqrt n ∧
          ∃ T : Finset (Fin m), T.card ≤ b ∧
            ∃ v : EuclideanSpace ℝ T, ‖v‖ = 1 ∧
              ‖(matrixOperator A).adjoint (rowEmbedding T v)‖ < c*Real.sqrt n} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      rintro A ⟨hA, T, hT, v, hv, hAv⟩
      exact ⟨hA, T, Nat.le_floor hT, v, hv, hAv⟩
    _ ≤ (2:ℝ)^m*(1+2*K/c)^b*((2:ℝ)^n*(a*c)^k) := hfin
    _ ≤ (2:ℝ)^m*(L/c)^b*((2:ℝ)^n*(a*c)^k) := by gcongr
    _ ≤ _ := hgeo

end MicroscopicJamming

namespace MicroscopicJamming

lemma uniform_gap_geometric {ρ K : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1/8)
    (hK : 0 < K) (B q : ℕ) (hq : 8 ≤ ρ*q) :
    ∃ u : ℝ, 0 < u ∧ u ≤ 1 ∧ ∀ {m n : ℕ}, q ≤ n → m ≤ B*n →
      ∀ {ε : ℝ}, ε ∈ Set.Icc (0:ℝ) (1/2) →
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => coordinateLaw ε).real
        {A | ‖matrixOperator A‖ ≤ K*Real.sqrt n ∧
          ∃ y : EuclideanSpace ℝ (Fin n), ‖y‖ = 1 ∧
            (1+ρ/2)*n < (nearGapCount A y u:ℝ)} ≤ Real.exp (-(n:ℝ)) := by
  let L : ℝ := 1+8*K/Real.sqrt ρ
  let D : ℝ := L*(2:ℝ)^B*4^2
  let d : ℝ := Real.exp (-1)/D
  let u : ℝ := d^q
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have hL : 1 ≤ L := by dsimp [L]; exact le_add_of_nonneg_right (by positivity)
  have hD : 1 ≤ D := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hL (one_le_pow₀ (by norm_num))) (by norm_num)
  obtain ⟨hd, hd1, hu, hu1, hDd⟩ := small_power_choice hD q
  change 0 < d at hd
  change d ≤ 1 at hd1
  change 0 < u at hu
  change u ≤ 1 at hu1
  change D*d = Real.exp (-1) at hDd
  refine ⟨u, hu, hu1, ?_⟩
  intro m n hn hm ε he
  let j := ⌈(1+ρ/4)*(n:ℝ)⌉₊
  obtain ⟨_, _, _, _, hnj, hj, hslack, hgap⟩ := geometry_indices hρ hρ1 hq hn
  let δ : ℝ := u*Real.sqrt ρ/(4*K)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hC : (K*Real.sqrt n)^2*δ^2 ≤ ((1+ρ/2)*n-j)*u^2 := by
    calc
      _ = (ρ*n/16)*u^2 := by
        dsimp [δ]
        rw [mul_pow, Real.sq_sqrt hn0, div_pow, mul_pow, Real.sq_sqrt hρ.le]
        field_simp
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hgap (sq_nonneg _)
  have hf := uniform_gap_count_failure_bound (m := m) (n := n) he j (mul_nonneg hK.le (Real.sqrt_nonneg _)) hu hδ hC
  have hfin := ENNReal.toReal_mono (by finiteness) hf
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at hfin
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at hfin
  have hbase : 1+2/δ ≤ L/u := by
    apply (le_div_iff₀ hu).mpr
    calc
      (1+2/δ)*u = u+8*K/Real.sqrt ρ := by dsimp [δ]; field_simp; ring
      _ ≤ L := by dsimp [L]; linarith
  have hgeo := gap_net_geometric_bound hL (by norm_num : (1:ℝ) ≤ 4) hd hd1 hm hnj hj hslack
  change (L/u)^n*((2:ℝ)^m*(4*u)^j) ≤ (D*d)^n at hgeo
  rw [hDd, exp_neg_one_pow] at hgeo
  calc
    _ ≤ (1+2/δ)^n*((2:ℝ)^m*(4*u)^j) := hfin
    _ ≤ (L/u)^n*((2:ℝ)^m*(4*u)^j) := by gcongr
    _ ≤ _ := hgeo

end MicroscopicJamming

namespace MicroscopicJamming

 

theorem uniform_row_estimates (B₀ ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1/8) :
    ∃ K c u : ℝ, 0 < K ∧ 0 < c ∧ 0 < u ∧ c ≤ 1 ∧ u ≤ 1 ∧
      ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ m : ℕ, (m:ℝ) ≤ B₀*n →
        ∀ ε ∈ Set.Icc (0:ℝ) (1/2),
        let ν := Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => coordinateLaw ε
        ν.real {A | ¬ RowGeometry ρ K c u A} ≤ 4*Real.exp (-(n:ℝ)) ∧
        1-4*Real.exp (-(n:ℝ)) ≤ ν.real {A | RowGeometry ρ K c u A} := by
  classical
  let B := ⌈B₀⌉₊
  let q := ⌈8/ρ⌉₊
  let K : ℝ := 12*((B:ℝ)+1)
  have hK : 0 < K := by dsimp [K]; positivity
  have hB : B₀ ≤ (B:ℝ) := Nat.le_ceil _
  have hq : 8 ≤ ρ*q := by
    have h := (div_le_iff₀ hρ).mp (Nat.le_ceil (8/ρ))
    nlinarith
  obtain ⟨c, hc, hc1, hrow⟩ := uniform_row_geometric hρ hρ1 hK B q hq
  obtain ⟨u, hu, hu1, hgap⟩ := uniform_gap_geometric hρ hρ1 hK B q hq
  refine ⟨K, c, u, hK, hc, hu, hc1, hu1, q, ?_⟩
  intro n hn m hm ε he
  dsimp only
  let ν := Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => coordinateLaw ε
  have hm' : m ≤ B*n := by
    have hh := hm.trans (mul_le_mul_of_nonneg_right hB (Nat.cast_nonneg n))
    exact_mod_cast hh
  let S₁ := {A : Fin m → Fin n → ℝ | K*Real.sqrt n < ‖matrixOperator A‖}
  let S₂ := {A : Fin m → Fin n → ℝ | ‖matrixOperator A‖ ≤ K*Real.sqrt n ∧
    ∃ T : Finset (Fin m), (T.card:ℝ) ≤ (1-ρ)*n ∧
      ∃ v : EuclideanSpace ℝ T, ‖v‖ = 1 ∧
        ‖(matrixOperator A).adjoint (rowEmbedding T v)‖ < c*Real.sqrt n}
  let S₃ := {A : Fin m → Fin n → ℝ | ‖matrixOperator A‖ ≤ K*Real.sqrt n ∧
    ∃ y : EuclideanSpace ℝ (Fin n), ‖y‖ = 1 ∧
      (1+ρ/2)*n < (nearGapCount A y u:ℝ)}
  have hS₁ : ν.real S₁ ≤ 2*Real.exp (-(n:ℝ)) := mixture_operator_geometric he hm'
  have hS₂ : ν.real S₂ ≤ Real.exp (-(n:ℝ)) := hrow hn hm' he
  have hS₃ : ν.real S₃ ≤ Real.exp (-(n:ℝ)) := hgap hn hm' he
  have hsub : {A : Fin m → Fin n → ℝ | ¬ RowGeometry ρ K c u A} ⊆
      (S₁ ∪ S₂) ∪ S₃ := by
    intro A hA
    by_cases hnA : ‖matrixOperator A‖ ≤ K*Real.sqrt n
    · by_cases hrA : A ∈ S₂
      · exact Or.inl (Or.inr hrA)
      · have htrans : ∀ T : Finset (Fin m), (T.card:ℝ) ≤ (1-ρ)*n →
            ∀ v : EuclideanSpace ℝ T,
              c*Real.sqrt n*‖v‖ ≤ ‖(matrixOperator A).adjoint (rowEmbedding T v)‖ := by
          intro T hT
          apply lower_bound_of_unit ((matrixOperator A).adjoint.comp (rowEmbedding T))
          intro v hv
          exact le_of_not_gt (fun hvA => hrA ⟨hnA, T, hT, v, hv, hvA⟩)
        have hbad : ∃ y : EuclideanSpace ℝ (Fin n), ‖y‖ = 1 ∧
            (1+ρ/2)*n < (nearGapCount A y u:ℝ) := by
          by_contra! hh
          exact hA ⟨hnA, htrans, hh⟩
        exact Or.inr ⟨hnA, hbad⟩
    · exact Or.inl (Or.inl (lt_of_not_ge hnA))
  have hbad : ν.real {A | ¬ RowGeometry ρ K c u A} ≤ 4*Real.exp (-(n:ℝ)) := by
    calc
      _ ≤ ν.real ((S₁ ∪ S₂) ∪ S₃) := measureReal_mono hsub (measure_ne_top ν _)
      _ ≤ ν.real (S₁ ∪ S₂) + ν.real S₃ := measureReal_union_le _ _
      _ ≤ (ν.real S₁+ν.real S₂)+ν.real S₃ := add_le_add (measureReal_union_le (μ := ν) S₁ S₂) le_rfl
      _ ≤ _ := by linarith
  refine ⟨hbad, ?_⟩
  have hcover : (Set.univ : Set (Fin m → Fin n → ℝ)) =
      {A | RowGeometry ρ K c u A} ∪ {A | ¬ RowGeometry ρ K c u A} := by
    ext A
    simp only [mem_univ, mem_union, mem_ofPred_eq, true_iff]
    exact Classical.em _
  have hh := measureReal_union_le (μ := ν) {A | RowGeometry ρ K c u A}
    {A | ¬ RowGeometry ρ K c u A}
  rw [← hcover, probReal_univ] at hh
  linarith

end MicroscopicJamming

end

end OAI
