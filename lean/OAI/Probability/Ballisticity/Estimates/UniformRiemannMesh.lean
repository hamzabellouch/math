import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

section

open MeasureTheory Filter
open scoped BigOperators Topology
namespace DirectionalTransience

noncomputable def realMesh (s t : ℝ) (n j : ℕ) : ℝ := s+(j:ℝ)*(t-s)/n

lemma realMesh_zero (s t : ℝ) (n : ℕ) : realMesh s t n 0=s := by simp [realMesh]
lemma realMesh_last (s t : ℝ) {n : ℕ} (hn : 0 < n) : realMesh s t n n=t := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [realMesh,mul_div_cancel_left₀ _ hn0]
  ring
lemma realMesh_sub (s t : ℝ) (n j : ℕ) : realMesh s t n (j+1)-realMesh s t n j=(t-s)/n := by
  simp only [realMesh,Nat.cast_add,Nat.cast_one]
  ring
lemma realMesh_mono {s t : ℝ} (hst : s ≤ t) (n : ℕ) : Monotone (realMesh s t n) := by
  intro i j hij
  simpa only [realMesh, add_comm] using add_le_add_left (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr hij) (sub_nonneg.mpr hst)) (Nat.cast_nonneg n)) s

lemma riemann_error_le (f : ℝ → ℝ) (hf : Continuous f) {s t ε δ : ℝ}
    (hst : s ≤ t) (hε : 0 ≤ ε) (hmod : ∀ x y, dist x y < δ → dist (f x) (f y) ≤ ε)
    {n : ℕ} (hn : 0 < n) (hδ : (t-s)/n < δ) :
    |(∑ j ∈ Finset.range n, (t-s)/n*f (realMesh s t n j))-(∫ u in s..t, f u)| ≤ ε*(t-s) := by
  have hmono := realMesh_mono hst n
  have hi : ∀ k < n, IntervalIntegrable f volume (realMesh s t n k) (realMesh s t n (k+1)) :=
    fun _ _ => hf.intervalIntegrable _ _
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hi
  rw [realMesh_zero,realMesh_last s t hn] at hsum
  rw [← hsum,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range n, |(t-s)/n*f (realMesh s t n j)-
        (∫ u in realMesh s t n j..realMesh s t n (j+1), f u)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range n, ε*((t-s)/n) := by
      apply Finset.sum_le_sum
      intro j hj
      have he : (t-s)/n*f (realMesh s t n j) =
          ∫ _u in realMesh s t n j..realMesh s t n (j+1), f (realMesh s t n j) := by
        rw [intervalIntegral.integral_const,realMesh_sub,smul_eq_mul]
      rw [he,← intervalIntegral.integral_sub intervalIntegrable_const (hf.intervalIntegrable _ _)]
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := realMesh s t n j)
        (b := realMesh s t n (j+1)) (C := |ε|) (f := fun u => f (realMesh s t n j)-f u) (fun u hu => by
          rw [Set.uIoc_of_le (hmono (Nat.le_succ j))] at hu
          have hd : dist (realMesh s t n j) u < δ := by
            rw [Real.dist_eq,abs_of_nonpos (by linarith [hu.1] : realMesh s t n j-u ≤ 0)]
            have hw := realMesh_sub s t n j
            linarith [hu.2]
          simpa only [Real.norm_eq_abs,Real.dist_eq,abs_of_nonneg hε] using hmod _ _ hd)
      simpa only [Real.norm_eq_abs,realMesh_sub,abs_of_nonneg hε,abs_of_nonneg (div_nonneg (sub_nonneg.mpr hst) (Nat.cast_nonneg n))] using hb
    _ = ε*(t-s) := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp

lemma tendsto_riemann_mesh (f : ℝ → ℝ) (hf : UniformContinuous f) {s t : ℝ} (hst : s < t) :
    Tendsto (fun n => ∑ j ∈ Finset.range n, (t-s)/n*f (realMesh s t n j)) atTop
      (𝓝 (∫ u in s..t, f u)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have he : 0 < ε/(2*(t-s)) := div_pos hε (mul_pos (by norm_num) (sub_pos.mpr hst))
  obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuous_iff.mp hf (ε/(2*(t-s))) he
  have hh : Tendsto (fun n : ℕ => (t-s)/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((hh.eventually_lt_const hδ).and (eventually_gt_atTop 0))
  refine ⟨N,fun n hn => ?_⟩
  have hb := riemann_error_le f hf.continuous hst.le he.le
    (fun x y hxy => (hmod hxy).le) (hN n hn).2 (hN n hn).1
  rw [Real.dist_eq]
  have heq : ε/(2*(t-s))*(t-s)=ε/2 := by field_simp [ne_of_gt (sub_pos.mpr hst)]
  rw [heq] at hb
  exact hb.trans_lt (by linarith)

end DirectionalTransience

end

section

open MeasureTheory Filter
open scoped BigOperators Topology
namespace DirectionalTransience

noncomputable def unitMesh (s t : unitInterval) (n j : ℕ) : unitInterval :=
  Set.projIcc 0 1 zero_le_one (realMesh s t n j)

lemma realMesh_between {s t : ℝ} (hst : s ≤ t) {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    s ≤ realMesh s t n j ∧ realMesh s t n j ≤ t := by
  constructor
  · simpa only [realMesh_zero] using (realMesh_mono hst n (Nat.zero_le j))
  · simpa only [realMesh_last s t hn] using (realMesh_mono hst n hj)

lemma unitMesh_coe (s t : unitInterval) (hst : s ≤ t) {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    (unitMesh s t n j:ℝ)=realMesh s t n j := by
  have hb := realMesh_between hst hn hj
  have hm : realMesh (s:ℝ) t n j ∈ unitInterval := ⟨s.property.1.trans hb.1,hb.2.trans t.property.2⟩
  simp only [unitMesh,Set.projIcc_of_mem zero_le_one hm]

lemma unitMesh_between (s t : unitInterval) (hst : s ≤ t) {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    s ≤ unitMesh s t n j ∧ unitMesh s t n j ≤ t := by
  change (s:ℝ) ≤ (unitMesh s t n j:ℝ) ∧ (unitMesh s t n j:ℝ) ≤ t
  rw [unitMesh_coe s t hst hn hj]
  exact realMesh_between hst hn hj

lemma unitMesh_zero (s t : unitInterval) (n : ℕ) : unitMesh s t n 0=s := by
  simp only [unitMesh,realMesh_zero,Set.projIcc_of_mem zero_le_one s.property]

lemma unitMesh_last (s t : unitInterval) {n : ℕ} (hn : 0 < n) : unitMesh s t n n=t := by
  simp only [unitMesh,realMesh_last (s:ℝ) t hn,Set.projIcc_of_mem zero_le_one t.property]

lemma unitMesh_sub (s t : unitInterval) (hst : s ≤ t) {n j : ℕ} (hn : 0 < n) (hj : j < n) :
    (unitMesh s t n (j+1):ℝ)-(unitMesh s t n j:ℝ)=((t:ℝ)-s)/n := by
  rw [unitMesh_coe s t hst hn (Nat.succ_le_of_lt hj),unitMesh_coe s t hst hn hj.le,realMesh_sub]

lemma unitMesh_step_lt (s t : unitInterval) (hst : s < t) {n j : ℕ} (hn : 0 < n) (hj : j < n) :
    unitMesh s t n j < unitMesh s t n (j+1) := by
  have hh := unitMesh_sub s t hst.le hn hj
  have hp : 0 < ((t:ℝ)-s)/(n:ℝ) := div_pos (sub_pos.mpr (show (s:ℝ) < t from hst))
    (Nat.cast_pos.mpr hn)
  change (unitMesh s t n j:ℝ) < (unitMesh s t n (j+1):ℝ)
  linarith

end DirectionalTransience

end

section

open Filter
open scoped BigOperators Topology
namespace DirectionalTransience

lemma contraction_recurrence_error (z : ℕ → ℂ) (r : ℂ) (e : ℕ → ℝ) (n : ℕ)
    (hr : ‖r‖ ≤ 1) (he : ∀ j < n, ‖z (j+1)-r*z j‖ ≤ e j) :
    ‖z n-r^n*z 0‖ ≤ ∑ j ∈ Finset.range n, e j := by
  induction n with
  | zero => simp
  | succ n ihn =>
    have hn := ihn (fun j hj => he j (Nat.lt_succ_of_lt hj))
    have heq : z (n+1)-r^(n+1)*z 0=(z (n+1)-r*z n)+r*(z n-r^n*z 0) := by
      rw [pow_succ]; ring
    rw [heq,Finset.sum_range_succ]
    calc
      _ ≤ ‖z (n+1)-r*z n‖+‖r‖*‖z n-r^n*z 0‖ := by
        simpa only [norm_mul] using norm_add_le (z (n+1)-r*z n) (r*(z n-r^n*z 0))
      _ ≤ e n+‖z n-r^n*z 0‖ := add_le_add (he n (Nat.lt_succ_self n))
        ((mul_le_mul_of_nonneg_right hr (norm_nonneg _)).trans_eq (one_mul _))
      _ ≤ _ := by linarith

lemma realEulerCoefficient_norm {lam δ : ℝ} (hlam : 0 ≤ lam) (hδ : 0 ≤ δ) (h : lam*δ ≤ 1) :
    ‖(1-((lam*δ:ℝ):ℂ))‖ ≤ 1 := by
  rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr h)]
  nlinarith

lemma scaled_exp_tendsto_zero {A L : ℝ} (hA : 0 < A) (hL : 0 < L) :
    Tendsto (fun n : ℕ => (n:ℝ)*Real.exp (-A/(L/n))) atTop (𝓝 0) := by
  have hat : Tendsto (fun n : ℕ => (A/L)*(n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (div_pos hA hL)
  have hh := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hat).const_mul (L/A)
  simp only [pow_one,mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hid : -A/(L/(n:ℝ))= -(A/L*(n:ℝ)) := by field_simp
  rw [hid]
  simp only [Function.comp_apply]
  field_simp

lemma scaled_sqrt_cube_tendsto_zero {c L : ℝ} (hc : 0 ≤ c) (hL : 0 ≤ L) :
    Tendsto (fun n : ℕ => (n:ℝ)*(Real.sqrt (c*(L/n)))^3) atTop (𝓝 0) := by
  have hh : Tendsto (fun n : ℕ => c*(L/n)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ => L/(n:ℝ)) atTop (𝓝 0)).const_mul c
  have hs := (Real.continuous_sqrt.tendsto 0).comp hh
  simp only [Real.sqrt_zero] at hs
  have hj := hs.const_mul (c*L)
  simp only [mul_zero] at hj
  apply hj.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hp : 0 ≤ c*(L/(n:ℝ)) := mul_nonneg hc (div_nonneg hL (Nat.cast_nonneg n))
  calc
    c*L*Real.sqrt (c*(L/(n:ℝ))) = (n:ℝ)*(c*(L/(n:ℝ)))*Real.sqrt (c*(L/(n:ℝ))) := by field_simp
    _ = _ := by
      have hcube : (Real.sqrt (c*(L/(n:ℝ))))^3=c*(L/(n:ℝ))*Real.sqrt (c*(L/(n:ℝ))) := by
        calc
          _ = (Real.sqrt (c*(L/(n:ℝ))))^2*Real.sqrt (c*(L/(n:ℝ))) := by ring
          _ = _ := by rw [Real.sq_sqrt hp]
      rw [hcube]
      ring

end DirectionalTransience

end

end

end OAI
