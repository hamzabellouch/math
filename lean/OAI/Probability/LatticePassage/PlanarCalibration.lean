import OAI.Probability.LatticePassage.RectangleCalibration
import OAI.Probability.LatticePassage.OffsetCalibration
import OAI.Probability.LatticePassage.MeanPositivity

namespace OAI

namespace CompanionFPP
open MeasureTheory Real Finset Filter Topology

lemma abs_range_average_le {f : ℕ → ℝ} {N : ℕ} (hN : 1 ≤ N) {B : ℝ}
    (h : ∀ k ∈ range N, |f k| ≤ B) : |(∑ k ∈ range N, f k) / N| ≤ B := by
  rw [abs_div, show |(N : ℝ)| = N from abs_of_nonneg (Nat.cast_nonneg N)]
  have hb : |∑ k ∈ range N, f k| ≤ (N : ℝ)*B :=
    (abs_sum_le_sum_abs _ _).trans (by simpa using sum_le_sum h)
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  exact (div_le_iff₀ hn).mpr (by simpa only [mul_comm B] using hb)

noncomputable def planarTargetCocycle (d a b : Vertex) (N M : ℕ)
    (ω : Environment) (x y : Vertex) : ℝ :=
  (∑ k ∈ range N, rectangleTargetCocycle (scaleVertex (k+1) d) a b M M ω x y) / N

@[fun_prop] lemma measurable_planarTargetCocycle (d a b x y : Vertex) (N M : ℕ) :
    Measurable (fun ω => planarTargetCocycle d a b N M ω x y) := by
  unfold planarTargetCocycle
  fun_prop

lemma integrable_planarTargetCocycle (d a b x y : Vertex) (N M : ℕ) :
    Integrable (fun ω => planarTargetCocycle d a b N M ω x y) environmentLaw :=
  (integrable_finsetSum _ (fun _ _ => integrable_rectangleTargetCocycle _ _ _ _ _ _ _)).div_const _

theorem planarTargetCocycle_add (d a b : Vertex) (N M : ℕ)
    (ω : Environment) (x y z : Vertex) :
    planarTargetCocycle d a b N M ω x z =
      planarTargetCocycle d a b N M ω x y + planarTargetCocycle d a b N M ω y z := by
  unfold planarTargetCocycle
  simp_rw [rectangleTargetCocycle_add _ _ _ _ _ _ x y z]
  rw [sum_add_distrib, add_div]

theorem planarTargetCocycle_dominated (d a b : Vertex) (N M : ℕ)
    (hN : 1 ≤ N) (hM : 1 ≤ M) :
    ∀ᵐ ω ∂environmentLaw, ∀ x y,
      |planarTargetCocycle d a b N M ω x y| ≤ passageTime ω x y := by
  have hall : ∀ᵐ ω ∂environmentLaw, ∀ k : ℕ, ∀ x y,
      |rectangleTargetCocycle (scaleVertex (k+1) d) a b M M ω x y| ≤ passageTime ω x y :=
    ae_all_iff.mpr (fun k => rectangleTargetCocycle_dominated _ _ _ _ _ hM hM)
  filter_upwards [hall] with ω hω
  intro x y
  exact abs_range_average_le hN (fun k _ => hω k x y)

theorem planarTargetCocycle_memLp_two (d a b x y : Vertex) (N M : ℕ)
    (hN : 1 ≤ N) (hM : 1 ≤ M) :
    MemLp (fun ω => planarTargetCocycle d a b N M ω x y) 2 environmentLaw := by
  apply (passageTime_memLp_two x y).mono' (by fun_prop)
  filter_upwards [planarTargetCocycle_dominated d a b N M hN hM] with ω hω
  simpa only [Real.norm_eq_abs] using hω x y

theorem planarTargetCocycle_second_moment (d a b x y : Vertex) (N M : ℕ)
    (hN : 1 ≤ N) (hM : 1 ≤ M) :
    (∫ ω, (planarTargetCocycle d a b N M ω x y)^2 ∂environmentLaw) ≤
      (latticeDistance x y : ℝ)*(latticeDistance x y+1) := by
  apply (integral_mono_ae (planarTargetCocycle_memLp_two d a b x y N M hN hM).integrable_sq
    (passageTime_memLp_two x y).integrable_sq (by
      filter_upwards [planarTargetCocycle_dominated d a b N M hN hM] with ω hω
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hω x y) 2)).trans
    (passageTime_second_moment x y)

theorem planarTargetCocycle_swap (d a b : Vertex) (N M : ℕ)
    (ω : Environment) (x y : Vertex) :
    planarTargetCocycle d a b N M ω x y = planarTargetCocycle d b a N M ω x y := by
  simp only [planarTargetCocycle, rectangleTargetCocycle_swap _ a b]

theorem planarTargetCocycle_shift_bound (d a b x y : Vertex) (N M : ℕ)
    (hN : 1 ≤ N) (hM : 1 ≤ M) :
    ∀ᵐ ω ∂environmentLaw,
      |planarTargetCocycle d a b N M (environmentTranslation a ω) x y -
        planarTargetCocycle d a b N M ω (a+x) (a+y)| ≤
      2*passageTime ω (a+x) (a+y)/M := by
  have hall : ∀ᵐ ω ∂environmentLaw, ∀ k : ℕ,
      |rectangleTargetCocycle (scaleVertex (k+1) d) a b M M (environmentTranslation a ω) x y -
        rectangleTargetCocycle (scaleVertex (k+1) d) a b M M ω (a+x) (a+y)| ≤
      2*passageTime ω (a+x) (a+y)/M :=
    ae_all_iff.mpr (fun k => rectangleTargetCocycle_shift_bound _ _ _ _ _ hM hM x y)
  filter_upwards [hall] with ω hω
  simp only [planarTargetCocycle, ← sub_div, ← sum_sub_distrib]
  exact abs_range_average_le hN (fun k _ => hω k)

theorem planarTargetCocycle_shift_integral (d a b x y : Vertex) (N M : ℕ)
    (hN : 1 ≤ N) (hM : 1 ≤ M) :
    (∫ ω, |planarTargetCocycle d a b N M (environmentTranslation a ω) x y -
      planarTargetCocycle d a b N M ω (a+x) (a+y)| ∂environmentLaw) ≤
      2*(latticeDistance x y : ℝ)/M := by
  have hi := ((environmentTranslation_preserving a).integrable_comp_of_integrable
    (integrable_planarTargetCocycle d a b x y N M)).sub
    (integrable_planarTargetCocycle d a b (a+x) (a+y) N M)
  apply (integral_mono_ae hi.abs
    (((integrable_passageTime (a+x) (a+y)).const_mul 2).div_const M)
    (planarTargetCocycle_shift_bound d a b x y N M hN hM)).trans
  rw [integral_div, integral_const_mul, mean_passageTime_translation]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (mean_passageTime_le_distance x y) (by norm_num)) (Nat.cast_nonneg M)

theorem planarTargetCocycle_eq_offsets (d a b : Vertex) (N M : ℕ)
    (ω : Environment) (x y : Vertex) :
    planarTargetCocycle d a b N M ω x y =
      (∑ i ∈ range M, ∑ j ∈ range M,
        offsetTargetCocycle (scaleVertex i a+scaleVertex j b) d N ω x y) / ((M : ℝ)*M) := by
  unfold planarTargetCocycle rectangleTargetCocycle offsetTargetCocycle
  simp only [← sum_div]
  rw [sum_comm (s := range N), sum_congr rfl (fun i _ => sum_comm (s := range N))]
  have he : ∀ k i j : ℕ,
      scaleVertex (k+1) d+scaleVertex i a+scaleVertex j b =
      scaleVertex i a+scaleVertex j b+scaleVertex (k+1) d := by intros; abel
  simp only [he]
  ring

theorem planarTargetCocycle_mean_error (d a b : Vertex) (N M : ℕ) (hM : 1 ≤ M)
    (K : ℝ) (hK : ∀ i ∈ range M, ∀ j ∈ range M,
      (latticeDistance 0 (scaleVertex i a+scaleVertex j b) : ℝ) ≤ K) :
    |(∫ ω, planarTargetCocycle d a b N M ω 0 d ∂environmentLaw) -
      meanPassageSequence d N/N| ≤ 2*K/N := by
  simp_rw [planarTargetCocycle_eq_offsets]
  rw [integral_div, integral_finsetSum _ (fun _ _ => integrable_finsetSum _
    (fun _ _ => integrable_offsetTargetCocycle _ _ _ _ _))]
  simp_rw [integral_finsetSum _ (fun _ _ => integrable_offsetTargetCocycle _ _ _ _ _)]
  have hn : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have he (c : ℝ) :
      (∑ i ∈ range M, ∑ j ∈ range M,
        ((∫ ω, offsetTargetCocycle (scaleVertex i a+scaleVertex j b) d N ω 0 d ∂environmentLaw)-c)) /
          ((M : ℝ)*M) =
      (∑ i ∈ range M, ∑ j ∈ range M,
        ∫ ω, offsetTargetCocycle (scaleVertex i a+scaleVertex j b) d N ω 0 d ∂environmentLaw) /
          ((M : ℝ)*M)-c := by
    simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    field_simp
  rw [← he]
  have he' : ∀ f : ℕ → ℕ → ℝ,
      (∑ i ∈ range M, ∑ j ∈ range M, f i j) / ((M : ℝ)*M) =
      (∑ i ∈ range M, (∑ j ∈ range M, f i j)/M)/M := by
    intro f; rw [← sum_div, div_div]
  rw [he']
  apply abs_range_average_le hM
  intro i hi
  apply abs_range_average_le hM
  intro j hj
  exact (offsetTargetCocycle_mean_error _ d N).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hK i hi j hj) (by norm_num))
      (Nat.cast_nonneg N))

lemma latticeDistance_planar_offset_le (a b : Vertex) (M i j : ℕ)
    (hi : i ∈ range M) (hj : j ∈ range M) :
    (latticeDistance 0 (scaleVertex i a+scaleVertex j b) : ℝ) ≤
      (M : ℝ)*((latticeDistance 0 a : ℝ)+latticeDistance 0 b) := by
  have ht := latticeDistance_triangle 0 (scaleVertex i a) (scaleVertex i a+scaleVertex j b)
  have he : latticeDistance (scaleVertex i a) (scaleVertex i a+scaleVertex j b) =
      latticeDistance 0 (scaleVertex j b) := by simp [latticeDistance]
  rw [he, latticeDistance_scaleVertex, latticeDistance_scaleVertex] at ht
  have hb : i*latticeDistance 0 a+j*latticeDistance 0 b ≤
      M*latticeDistance 0 a+M*latticeDistance 0 b :=
    Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.le_of_lt (mem_range.mp hi)))
      (Nat.mul_le_mul_right _ (Nat.le_of_lt (mem_range.mp hj)))
  have hc := ht.trans hb
  exact_mod_cast (by simpa only [Nat.mul_add] using hc)

noncomputable def calibrationApprox (d a b : Vertex) (n : ℕ)
    (ω : Environment) (x y : Vertex) : ℝ :=
  planarTargetCocycle d a b ((n+1)*(n+1)) (n+1) ω x y

theorem calibrationApprox_mean_error (d a b : Vertex) (n : ℕ) :
    |(∫ ω, calibrationApprox d a b n ω 0 d ∂environmentLaw) -
      meanPassageSequence d ((n+1)*(n+1))/((n+1)*(n+1))| ≤
      (2*((latticeDistance 0 a : ℝ)+latticeDistance 0 b))/(n+1) := by
  have h := planarTargetCocycle_mean_error d a b ((n+1)*(n+1)) (n+1) (by omega)
    ((n+1)*((latticeDistance 0 a : ℝ)+latticeDistance 0 b))
    (by
      intro i hi j hj
      simpa only [Nat.cast_add, Nat.cast_one] using latticeDistance_planar_offset_le a b (n+1) i j hi hj)
  convert h using 1 <;> push_cast <;> try rfl
  field_simp

theorem calibrationApprox_mean_tendsto (d a b : Vertex) :
    Tendsto (fun n : ℕ => ∫ ω, calibrationApprox d a b n ω 0 d ∂environmentLaw)
      atTop (𝓝 (directionalMeanConstant d)) := by
  have hn : Tendsto (fun n : ℕ => n+1) atTop atTop := tendsto_add_atTop_nat 1
  have hs : Tendsto (fun n : ℕ => (n+1)*(n+1)) atTop atTop :=
    tendsto_atTop_mono (fun n => by nlinarith : ∀ n : ℕ, n+1 ≤ (n+1)*(n+1)) hn
  have hmean := (meanPassageSequence_tendsto d).comp hs
  have herr := (tendsto_const_div_atTop_nhds_zero_nat
    (2*((latticeDistance 0 a : ℝ)+latticeDistance 0 b))).comp hn
  have hz : Tendsto (fun n : ℕ =>
      (∫ ω, calibrationApprox d a b n ω 0 d ∂environmentLaw) -
      meanPassageSequence d ((n+1)*(n+1))/((n+1)*(n+1))) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) (by simpa only [Nat.cast_add, Nat.cast_one] using herr)
    simpa only [Real.norm_eq_abs, Function.comp_apply, Nat.cast_add, Nat.cast_one] using calibrationApprox_mean_error d a b n
  have ht := hz.add hmean
  simpa only [Function.comp_apply, Nat.cast_mul, Nat.cast_add, Nat.cast_one, sub_add_cancel, zero_add] using ht

theorem calibrationApprox_shift_tendsto (d a b x y : Vertex) :
    Tendsto (fun n : ℕ => ∫ ω,
      |calibrationApprox d a b n (environmentTranslation a ω) x y -
        calibrationApprox d a b n ω (a+x) (a+y)| ∂environmentLaw) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => abs_nonneg _))
    (fun n => planarTargetCocycle_shift_integral d a b x y _ _ (by nlinarith) (by omega))
    ((tendsto_const_div_atTop_nhds_zero_nat (2*(latticeDistance x y : ℝ))).comp
      (tendsto_add_atTop_nat 1))

theorem calibrationApprox_second_shift_tendsto (d a b x y : Vertex) :
    Tendsto (fun n : ℕ => ∫ ω,
      |calibrationApprox d a b n (environmentTranslation b ω) x y -
        calibrationApprox d a b n ω (b+x) (b+y)| ∂environmentLaw) atTop (𝓝 0) := by
  unfold calibrationApprox
  simp_rw [planarTargetCocycle_swap d a b]
  exact calibrationApprox_shift_tendsto d b a x y

end CompanionFPP

end OAI
