import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import OAI.NumberTheory.SiegelZeros.Structure.MasterContradiction

namespace OAI

namespace SiegelZeros

section

open Filter
open scoped Topology

namespace WeightedTorusJets.W48

noncomputable def auxiliaryN (γ q : ℝ) : ℕ := Nat.ceil (q ^ γ)

noncomputable def auxiliaryU (γ q : ℝ) : ℝ :=
  (auxiliaryN γ q : ℝ) ^ (4 / 3 : ℝ)

theorem N_real_tendsto_atTop {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun q : ℝ => (auxiliaryN γ q : ℝ)) atTop atTop :=
  tendsto_atTop_mono (fun q => Nat.le_ceil (q ^ γ)) (tendsto_rpow_atTop hγ)

theorem N_nat_tendsto_atTop {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (auxiliaryN γ) atTop atTop :=
  tendsto_natCast_atTop_iff.mp (N_real_tendsto_atTop hγ)

theorem U_tendsto_atTop {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (auxiliaryU γ) atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 3)).comp
    (N_real_tendsto_atTop hγ)

theorem log_U_tendsto_atTop {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun q => Real.log (auxiliaryU γ q)) atTop atTop :=
  Real.tendsto_log_atTop.comp (U_tendsto_atTop hγ)

theorem auxiliaryN_pos {γ q : ℝ} (hq : 0 < q) :
    0 < (auxiliaryN γ q : ℝ) :=
  (Real.rpow_pos_of_pos hq γ).trans_le (Nat.le_ceil (q ^ γ))

theorem log_N_bounds {γ q : ℝ} (hγ : 0 ≤ γ) (hq : 1 ≤ q) :
    γ * Real.log q ≤ Real.log (auxiliaryN γ q) ∧
      Real.log (auxiliaryN γ q) ≤ γ * Real.log q + Real.log 2 := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hp : 0 < q ^ γ := Real.rpow_pos_of_pos hq0 γ
  have hone : 1 ≤ q ^ γ := Real.one_le_rpow hq hγ
  have hlo : q ^ γ ≤ (auxiliaryN γ q : ℝ) := Nat.le_ceil _
  have hhi : (auxiliaryN γ q : ℝ) ≤ 2 * q ^ γ := by
    have hceil := Nat.ceil_lt_add_one hp.le
    dsimp [auxiliaryN]
    linarith
  constructor
  · simpa only [Real.log_rpow hq0] using Real.log_le_log hp hlo
  · have hlog := Real.log_le_log (auxiliaryN_pos hq0) hhi
    rw [Real.log_mul (by norm_num) (ne_of_gt hp), Real.log_rpow hq0] at hlog
    linarith

theorem log_N_div_log_tendsto {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun q : ℝ => Real.log (auxiliaryN γ q) / Real.log q)
      atTop (𝓝 γ) := by
  have hupper : Tendsto (fun q : ℝ => γ + Real.log 2 / Real.log q)
      atTop (𝓝 γ) := by
    simpa using tendsto_const_nhds.add
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => Real.log 2) atTop
        (𝓝 (Real.log 2))).div_atTop Real.tendsto_log_atTop)
  apply tendsto_const_nhds.squeeze' hupper
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with q hq
    exact (le_div_iff₀ (Real.log_pos hq)).2 (log_N_bounds hγ.le hq.le).1
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with q hq
    apply (div_le_iff₀ (Real.log_pos hq)).2
    have hlog : Real.log q ≠ 0 := ne_of_gt (Real.log_pos hq)
    rw [add_mul, div_mul_cancel₀ _ hlog]
    exact (log_N_bounds hγ.le hq.le).2

theorem log_U_div_log_tendsto {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun q : ℝ => Real.log (auxiliaryU γ q) / Real.log q)
      atTop (𝓝 (4 * γ / 3)) := by
  have h := (log_N_div_log_tendsto hγ).const_mul (4 / 3 : ℝ)
  have heq : (4 / 3 : ℝ) * γ = 4 * γ / 3 := by ring
  rw [heq] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with q hq
  dsimp [auxiliaryU]
  rw [Real.log_rpow (auxiliaryN_pos hq)]
  ring

theorem eventually_N_ge {γ : ℝ} (hγ : 0 < γ) (H : ℕ) :
    ∀ᶠ q in atTop, H ≤ auxiliaryN γ q :=
  (N_nat_tendsto_atTop hγ).eventually_ge_atTop H

theorem log_div_log_U_tendsto {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun q : ℝ => Real.log q / Real.log (auxiliaryU γ q))
      atTop (𝓝 (3 / (4 * γ))) := by
  simpa only [inv_div] using
    (log_U_div_log_tendsto hγ).inv₀ (by positivity : 4 * γ / 3 ≠ 0)

theorem natural_conductor_limits {ι : Type*} {l : Filter ι} {q : ι → ℕ}
    {γ : ℝ} (hγ : 0 < γ) (hq : Tendsto q l atTop) :
    Tendsto (fun i => auxiliaryN γ (q i)) l atTop ∧
      Tendsto (fun i => auxiliaryU γ (q i)) l atTop ∧
      Tendsto (fun i => Real.log (auxiliaryU γ (q i)) / Real.log (q i))
        l (𝓝 (4 * γ / 3)) := by
  have hqR : Tendsto (fun i => (q i : ℝ)) l atTop :=
    tendsto_natCast_atTop_atTop.comp hq
  exact ⟨(N_nat_tendsto_atTop hγ).comp hqR,
    (U_tendsto_atTop hγ).comp hqR, (log_U_div_log_tendsto hγ).comp hqR⟩

end WeightedTorusJets.W48

end


namespace W49

open Filter Topology

theorem count_error_bound {M U S k : ℝ} (hM : 0 < M) (hU : 1 < U)
    (hk : 0 < k) (hS : k * M * U ≤ S) :
    M * U / (S * Real.log U) ≤ (1 / k) / Real.log U := by
  have hUp : 0 < U := lt_trans zero_lt_one hU
  have hlog : 0 < Real.log U := Real.log_pos hU
  calc
    M * U / (S * Real.log U) ≤ M * U / ((k * M * U) * Real.log U) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_right hS hlog.le)
    _ = (1 / k) / Real.log U := by
      field_simp [ne_of_gt hk, ne_of_gt hM, ne_of_gt hUp, ne_of_gt hlog]

theorem entropy_error_bound {M U S k : ℝ} (hM : 0 < M) (hU : 1 < U)
    (hk : 0 < k) (hS : k * M * U ≤ S)
    (hlogM : Real.log M = 3 * Real.log U) :
    M * Real.log M / (S * Real.log U) ≤ (3 / k) / U := by
  have hUp : 0 < U := lt_trans zero_lt_one hU
  have hlog : 0 < Real.log U := Real.log_pos hU
  have hlogMp : 0 ≤ Real.log M := by rw [hlogM]; positivity
  calc
    M * Real.log M / (S * Real.log U) ≤
        M * Real.log M / ((k * M * U) * Real.log U) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_right hS hlog.le)
    _ = (3 / k) / U := by
      rw [hlogM]
      field_simp [ne_of_gt hk, ne_of_gt hM, ne_of_gt hUp, ne_of_gt hlog]

theorem delta_error_tendsto {ι : Type*} {l : Filter ι}
    {δ U ell : ι → ℝ} {a : ℝ} (C : ℝ)
    (hδ : Tendsto δ l (𝓝 0))
    (hratio : Tendsto (fun i => Real.log (U i) / ell i) l (𝓝 a)) :
    Tendsto (fun i => C * δ i * Real.log (U i) / ell i) l (𝓝 0) := by
  simpa [mul_div_assoc] using (hδ.const_mul C).mul hratio

theorem fixed_error_tendsto {ι : Type*} {l : Filter ι}
    {U r : ι → ℝ} {CH R : ℝ} (hCH : 0 ≤ CH)
    (hU : Tendsto U l atTop)
    (hr : ∀ᶠ i in l, 0 ≤ r i ∧ r i ≤ R) :
    Tendsto (fun i => (CH + (1 + r i) * Real.log 8) / Real.log (U i))
      l (𝓝 0) := by
  have hlog8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hlogU := Real.tendsto_log_atTop.comp hU
  apply squeeze_zero' (g := fun i => (CH + (1 + R) * Real.log 8) / Real.log (U i))
  · filter_upwards [hr, hlogU.eventually_gt_atTop 0] with i hi hu
    exact div_nonneg (add_nonneg hCH (mul_nonneg (by linarith [hi.1]) hlog8)) hu.le
  · filter_upwards [hr, hlogU.eventually_gt_atTop 0] with i hi hu
    have hcoef : 1 + r i ≤ 1 + R := by linarith [hi.2]
    have hnum : CH + (1 + r i) * Real.log 8 ≤ CH + (1 + R) * Real.log 8 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hcoef hlog8)
    exact div_le_div_of_nonneg_right hnum hu.le
  · exact tendsto_const_nhds.div_atTop hlogU

theorem count_error_tendsto {ι : Type*} {l : Filter ι}
    {M U S : ι → ℝ} {k : ℝ} (hk : 0 < k)
    (hU : Tendsto U l atTop)
    (hM : ∀ᶠ i in l, 0 < M i)
    (hS : ∀ᶠ i in l, k * M i * U i ≤ S i) :
    Tendsto (fun i => M i * U i / (S i * Real.log (U i))) l (𝓝 0) := by
  have hlogU := Real.tendsto_log_atTop.comp hU
  apply squeeze_zero' (g := fun i => (1 / k) / Real.log (U i))
  · filter_upwards [hM, hS, hU.eventually_gt_atTop 1] with i hm hs hu
    have hup : 0 < U i := lt_trans zero_lt_one hu
    have hsp : 0 < S i := lt_of_lt_of_le (by positivity) hs
    have hl : 0 < Real.log (U i) := Real.log_pos hu
    positivity
  · filter_upwards [hM, hS, hU.eventually_gt_atTop 1] with i hm hs hu
    exact count_error_bound hm hu hk hs
  · exact tendsto_const_nhds.div_atTop hlogU

theorem entropy_error_tendsto {ι : Type*} {l : Filter ι}
    {M U S : ι → ℝ} {k : ℝ} (hk : 0 < k)
    (hU : Tendsto U l atTop)
    (hM : ∀ᶠ i in l, 0 < M i)
    (hS : ∀ᶠ i in l, k * M i * U i ≤ S i)
    (hlogM : ∀ᶠ i in l, Real.log (M i) = 3 * Real.log (U i)) :
    Tendsto (fun i => M i * Real.log (M i) / (S i * Real.log (U i)))
      l (𝓝 0) := by
  apply squeeze_zero' (g := fun i => (3 / k) / U i)
  · filter_upwards [hM, hS, hlogM, hU.eventually_gt_atTop 1] with i hm hs hlm hu
    have hup : 0 < U i := lt_trans zero_lt_one hu
    have hsp : 0 < S i := lt_of_lt_of_le (by positivity) hs
    have hl : 0 < Real.log (U i) := Real.log_pos hu
    rw [hlm]
    positivity
  · filter_upwards [hM, hS, hlogM, hU.eventually_gt_atTop 1] with i hm hs hlm hu
    exact entropy_error_bound hm hu hk hs hlm
  · exact tendsto_const_nhds.div_atTop hU

theorem determinant_error_tendsto {ι : Type*} {l : Filter ι}
    {M U S : ι → ℝ} {k : ℝ} (C : ℝ) (hk : 0 < k)
    (hU : Tendsto U l atTop)
    (hM : ∀ᶠ i in l, 0 < M i)
    (hS : ∀ᶠ i in l, k * M i * U i ≤ S i)
    (hlogM : ∀ᶠ i in l, Real.log (M i) = 3 * Real.log (U i)) :
    Tendsto (fun i => (C * M i * U i + (1 / 2 : ℝ) * M i * Real.log (M i)) /
      (S i * Real.log (U i))) l (𝓝 0) := by
  have hc := (count_error_tendsto hk hU hM hS).const_mul C
  have he := (entropy_error_tendsto hk hU hM hS hlogM).const_mul (1 / 2 : ℝ)
  have hsum : Tendsto
      (fun i => C * (M i * U i / (S i * Real.log (U i))) +
        (1 / 2 : ℝ) * (M i * Real.log (M i) / (S i * Real.log (U i))))
      l (𝓝 0) := by
    simpa only [mul_zero, add_zero] using hc.add he
  apply hsum.congr
  intro i
  ring

theorem log_volume_identity {ι : Type*} {l : Filter ι} {M U : ι → ℝ}
    (hvol : ∀ᶠ i in l, M i = U i ^ 3) :
    ∀ᶠ i in l, Real.log (M i) = 3 * Real.log (U i) := by
  filter_upwards [hvol] with i hi
  rw [hi, Real.log_pow]
  norm_num

end W49



open Filter
open scoped Topology

namespace SiegelZerosAwei.W50

theorem false_of_master_and_pivot_estimates
    {ι : Type*} {l : Filter ι} [NeBot l]
    (S₁ S₂ M U ell delta : ι → ℝ) (C C_H k a : ℝ)
    (hk : 0 < k) (ha : 0 < a) (hCH : 0 ≤ C_H)
    (hU : Tendsto U l atTop)
    (hdelta : Tendsto delta l (𝓝 0))
    (hratio : Tendsto (fun n => Real.log (U n) / ell n) l (𝓝 a))
    (hell : ∀ᶠ n in l, 0 < ell n)
    (hM : ∀ᶠ n in l, 0 < M n)
    (hS : ∀ᶠ n in l, k * M n * U n ≤ S₁ n)
    (hr : ∀ᶠ n in l, 0 ≤ S₂ n / S₁ n ∧ S₂ n / S₁ n ≤ 1 / 12)
    (hlogM : ∀ᶠ n in l, Real.log (M n) = 3 * Real.log (U n))
    (hallow : (C + 13 / 24) / a < 1 / 16)
    (hmaster : ∀ᶠ n in l,
      1 ≤ W46.masterRHS (S₁ n) (S₂ n) (M n) (U n) C C_H
        (ell n) (delta n) (Real.log (U n)) (Real.log (M n)) (Real.log 8)) :
    False := by
  have ht : Tendsto (fun n => ell n / Real.log (U n)) l (𝓝 a⁻¹) := by
    simpa only [inv_div] using hratio.inv₀ (ne_of_gt ha)
  have htnonneg : ∀ᶠ n in l, 0 ≤ ell n / Real.log (U n) := by
    filter_upwards [hell, hU.eventually_gt_atTop 1] with n hn hu
    exact div_nonneg hn.le (Real.log_pos hu).le
  have he₁ : Tendsto (fun n => C * delta n * (Real.log (U n) / ell n)) l
      (𝓝 0) := by
    simpa only [mul_div_assoc] using
      SiegelZeros.W49.delta_error_tendsto C hdelta hratio
  exact false_of_exact_master S₁ S₂ M U ell delta
    (fun n => Real.log (U n)) (fun n => Real.log (M n))
    C C_H (Real.log 8) a⁻¹ hmaster (hr.mono fun _ h => h.2)
    htnonneg ht (by simpa only [div_eq_mul_inv] using hallow) he₁
    (SiegelZeros.W49.fixed_error_tendsto hCH hU hr)
    (SiegelZeros.W49.determinant_error_tendsto C hk hU hM hS hlogM)

theorem false_of_ceiling_master
    {ι : Type*} {l : Filter ι} [NeBot l]
    (γ C C_H k : ℝ) (hγ : 0 < γ) (hk : 0 < k) (hCH : 0 ≤ C_H)
    (hallow : (C + 13 / 24) / (4 * γ / 3) < 1 / 16)
    (q S₁ S₂ M delta : ι → ℝ)
    (hq : Tendsto q l atTop) (hdelta : Tendsto delta l (𝓝 0))
    (hM : ∀ᶠ n in l, 0 < M n)
    (hS : ∀ᶠ n in l,
      k * M n * WeightedTorusJets.W48.auxiliaryU γ (q n) ≤ S₁ n)
    (hr : ∀ᶠ n in l, 0 ≤ S₂ n / S₁ n ∧ S₂ n / S₁ n ≤ 1 / 12)
    (hvol : ∀ᶠ n in l, M n = (WeightedTorusJets.W48.auxiliaryU γ (q n)) ^ 3)
    (hmaster : ∀ᶠ n in l,
      1 ≤ W46.masterRHS (S₁ n) (S₂ n) (M n)
        (WeightedTorusJets.W48.auxiliaryU γ (q n)) C C_H
        (Real.log (q n)) (delta n)
        (Real.log (WeightedTorusJets.W48.auxiliaryU γ (q n)))
        (Real.log (M n)) (Real.log 8)) : False := by
  apply false_of_master_and_pivot_estimates S₁ S₂ M
    (fun n => WeightedTorusJets.W48.auxiliaryU γ (q n))
    (fun n => Real.log (q n)) delta C C_H k (4 * γ / 3) hk
    (by positivity) hCH
    ((WeightedTorusJets.W48.U_tendsto_atTop hγ).comp hq) hdelta
    ((WeightedTorusJets.W48.log_U_div_log_tendsto hγ).comp hq)
  · filter_upwards [hq.eventually_gt_atTop 1] with n hn
    exact Real.log_pos hn
  · exact hM
  · exact hS
  · exact hr
  · exact SiegelZeros.W49.log_volume_identity hvol
  · exact hallow
  · exact hmaster

end SiegelZerosAwei.W50


end SiegelZeros

end OAI
