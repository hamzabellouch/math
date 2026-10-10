import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.OneBounded
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Poly

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory

namespace OrdinaryCorrelations
namespace SourceRoughFourier
open Finset
variable {N : ℕ} [NeZero N]
variable {ι κ : Type*}

noncomputable def meanC (f : ZMod N → ℂ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ k, f k
noncomputable def meanR (f : ZMod N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ k, f k
theorem meanC_add (f g : ZMod N → ℂ) :
    meanC (fun k => f k + g k) = meanC f + meanC g := by
  simp only [meanC, sum_add_distrib, mul_add]

theorem meanC_sum (s : Finset ι) (f : ι → ZMod N → ℂ) :
    meanC (fun k => ∑ i ∈ s, f i k) = ∑ i ∈ s, meanC (f i) := by
  simp only [meanC, ← mul_sum]
  rw [sum_comm]

theorem meanC_mul_left (c : ℂ) (f : ZMod N → ℂ) :
    meanC (fun k => c * f k) = c * meanC f := by
  simp only [meanC, ← mul_sum]
  ring

theorem mean_char (a : ZMod N) :
    meanC (fun k => ZMod.stdAddChar (a * k)) = if a = 0 then 1 else 0 := by
  classical
  unfold meanC
  by_cases ha : a = 0
  · subst a
    simp [ZMod.card, NeZero.ne N]
  · rw [ite_eq_right ha]
    have hsum : ∑ k : ZMod N, ZMod.stdAddChar (a * k) = 0 :=
      AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N ha)
    rw [hsum, mul_zero]

theorem poly_mul (s : Finset ι) (t : Finset κ) (w : ι → ℂ)
    (v : κ → ℂ) (a : ι → ZMod N) (b : κ → ZMod N) (k : ZMod N) :
    poly s w a k * poly t v b k =
      poly (s ×ˢ t) (fun ij => w ij.1 * v ij.2) (fun ij => a ij.1 + b ij.2) k := by
  classical
  simp only [poly, sum_mul_sum, sum_product]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [add_mul, AddChar.map_add_eq_mul]
  ring

theorem mean_poly (s : Finset ι) (w : ι → ℂ) (a : ι → ZMod N) :
    meanC (poly s w a) = ∑ i ∈ s, if a i = 0 then w i else 0 := by
  classical
  change meanC (fun k => ∑ i ∈ s, w i * ZMod.stdAddChar (a i * k)) = _
  rw [meanC_sum]
  simp only [meanC_mul_left, mean_char]
  apply sum_congr rfl
  intro i hi
  split_ifs <;> simp

theorem mean_poly_mul (s : Finset ι) (t : Finset κ) (w : ι → ℂ)
    (v : κ → ℂ) (a : ι → ZMod N) (b : κ → ZMod N) :
    meanC (fun k => poly s w a k * poly t v b k) =
      ∑ i ∈ s, ∑ j ∈ t, if a i + b j = 0 then w i * v j else 0 := by
  classical
  simp_rw [poly_mul]
  rw [mean_poly, sum_product]

theorem conjugate_poly (s : Finset ι) (w : ι → ℂ) (a : ι → ZMod N)
    (k : ZMod N) :
    (starRingEnd ℂ) (poly s w a k) =
      poly s (fun i => (starRingEnd ℂ) (w i)) (fun i => -a i) k := by
  simp only [poly, map_sum, map_mul, neg_mul, AddChar.map_neg_eq_inv,
    AddChar.inv_apply_eq_conj]

theorem meanR_cast (f : ZMod N → ℝ) :
    (meanR f : ℂ) = meanC (fun k => (f k : ℂ)) := by
  simp only [meanR, meanC, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_sum, Complex.ofReal_natCast]

theorem parseval (s : Finset ι) (w : ι → ℂ) (a : ι → ZMod N)
    (ha : Set.InjOn a s) :
    meanR (fun k => ‖poly s w a k‖ ^ 2) = ∑ i ∈ s, ‖w i‖ ^ 2 := by
  classical
  apply Complex.ofReal_injective
  rw [meanR_cast, Complex.ofReal_sum]
  simp only [Complex.ofReal_pow, ← Complex.mul_conj']
  simp_rw [conjugate_poly]
  rw [mean_poly_mul]
  apply sum_congr rfl
  intro i hi
  rw [sum_eq_single i]
  · simp
  · intro j hj hji
    rw [ite_eq_right]
    intro hh
    have he : a i = a j := sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hh)
    exact hji (ha hj hi he.symm)
  · exact fun h => (h hi).elim

theorem meanR_nonneg (f : ZMod N → ℝ) (hf : ∀ k, 0 ≤ f k) :
    0 ≤ meanR f := by
  unfold meanR
  exact mul_nonneg (by positivity) (sum_nonneg (fun k _ => hf k))

theorem meanR_mono (f g : ZMod N → ℝ) (hfg : ∀ k, f k ≤ g k) :
    meanR f ≤ meanR g := by
  unfold meanR
  exact mul_le_mul_of_nonneg_left (sum_le_sum (fun k _ => hfg k)) (by positivity)

theorem meanR_sum (s : Finset ι) (f : ι → ZMod N → ℝ) :
    meanR (fun k => ∑ i ∈ s, f i k) = ∑ i ∈ s, meanR (f i) := by
  simp only [meanR, ← mul_sum]
  rw [sum_comm]

theorem energy_real (s : Finset ι) (w : ι → ℝ) (a : ι → ZMod N) :
    meanR (fun k => ‖poly s (fun i => (w i : ℂ)) a k‖ ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, if a i = a j then w i * w j else 0 := by
  classical
  apply Complex.ofReal_injective
  rw [meanR_cast]
  simp only [Complex.ofReal_pow, ← Complex.mul_conj', Complex.ofReal_sum,
    apply_ite, Complex.ofReal_zero, Complex.ofReal_mul]
  simp_rw [conjugate_poly]
  rw [mean_poly_mul]
  simp only [← sub_eq_add_neg, sub_eq_zero, Complex.conj_ofReal]

theorem fourth_moment_real (s : Finset ι) (w : ι → ℝ) (a : ι → ZMod N) :
    meanR (fun k => ‖poly s (fun i => (w i : ℂ)) a k‖ ^ 4) =
      ∑ i ∈ s, ∑ j ∈ s, ∑ u ∈ s, ∑ v ∈ s,
        if a i + a j = a u + a v then (w i * w j) * (w u * w v) else 0 := by
  classical
  have hp (k : ZMod N) :
      ‖poly s (fun i => (w i : ℂ)) a k‖ ^ 4 =
      ‖poly (s ×ˢ s) (fun ij => ((w ij.1 * w ij.2 : ℝ) : ℂ))
        (fun ij => a ij.1 + a ij.2) k‖ ^ 2 := by
    simp only [Complex.ofReal_mul]
    rw [← poly_mul s s (fun i => (w i : ℂ)) (fun i => (w i : ℂ)) a a, norm_mul]
    ring
  simp_rw [hp]
  rw [energy_real]
  simp only [sum_product]

noncomputable def additiveEnergy [DecidableEq (ZMod N)]
    (s : Finset ι) (a : ι → ZMod N) : ℕ :=
  (((s ×ˢ s) ×ˢ (s ×ˢ s)).filter
    (fun ij => a ij.1.1 + a ij.1.2 = a ij.2.1 + a ij.2.2)).card

theorem fourth_moment_le_energy (s : Finset ι) (w : ι → ℝ) (a : ι → ZMod N)
    (W : ℝ) (hW : 0 ≤ W) (hw : ∀ i ∈ s, 0 ≤ w i ∧ w i ≤ W) :
    meanR (fun k => ‖poly s (fun i => (w i : ℂ)) a k‖ ^ 4) ≤
      additiveEnergy s a * W ^ 4 := by
  classical
  rw [fourth_moment_real]
  let E := ((s ×ˢ s) ×ˢ (s ×ˢ s)).filter
    (fun ij => a ij.1.1 + a ij.1.2 = a ij.2.1 + a ij.2.2)
  have heq : (∑ i ∈ s, ∑ j ∈ s, ∑ u ∈ s, ∑ v ∈ s,
      if a i + a j = a u + a v then (w i * w j) * (w u * w v) else 0) =
      ∑ ij ∈ E, (w ij.1.1 * w ij.1.2) * (w ij.2.1 * w ij.2.2) := by
    simp only [E, sum_filter, sum_product]
  rw [heq]
  calc
    _ ≤ ∑ _ij ∈ E, W ^ 4 := by
      apply sum_le_sum
      intro ij hij
      obtain ⟨hij, _⟩ := mem_filter.mp hij
      obtain ⟨hij, huv⟩ := mem_product.mp hij
      obtain ⟨hi, hj⟩ := mem_product.mp hij
      obtain ⟨hu, hv⟩ := mem_product.mp huv
      obtain ⟨hi0, hiW⟩ := hw ij.1.1 hi
      obtain ⟨hj0, hjW⟩ := hw ij.1.2 hj
      obtain ⟨hu0, huW⟩ := hw ij.2.1 hu
      obtain ⟨hv0, hvW⟩ := hw ij.2.2 hv
      calc
        _ ≤ (W * W) * (W * W) := by gcongr
        _ = _ := by ring
    _ = _ := by simp [additiveEnergy, E, nsmul_eq_mul]

theorem low_high_frequency_bound {V K : Type*} (s : Finset V) (t : Finset K)
    (B : K → ℂ) (F G : V → K → ℂ) (τ M G₀ S P Q : ℝ)
    (hτ : 0 < τ) (hM : 0 ≤ M) (hG₀ : 0 ≤ G₀) (hS : 0 ≤ S)
    (hB : ∀ k ∈ t, ‖B k‖ ≤ M)
    (hG : ∀ v ∈ s, ∀ k ∈ t, ‖G v k‖ ≤ G₀)
    (hF : ∀ k ∈ t, ∑ v ∈ s, ‖F v k‖ ≤ S)
    (hFG : ∀ v ∈ s, ∑ k ∈ t, ‖F v k‖ * ‖G v k‖ ≤ P)
    (hB₄ : ∑ k ∈ t, ‖B k‖ ^ 4 ≤ Q) :
    (∑ v ∈ s, ∑ k ∈ t, ‖B k‖ * ‖F v k‖ * ‖G v k‖) ≤
      (s.card : ℝ) * τ * P + Q / τ ^ 4 * M * G₀ * S := by
  classical
  let E := t.filter (fun k => τ < ‖B k‖)
  have hcount : (E.card : ℝ) * τ ^ 4 ≤ Q := by
    calc
      _ = ∑ _k ∈ E, τ ^ 4 := by simp
      _ ≤ ∑ k ∈ E, ‖B k‖ ^ 4 := by
        apply sum_le_sum
        intro k hk
        exact pow_le_pow_left₀ hτ.le (mem_filter.mp hk).2.le 4
      _ ≤ ∑ k ∈ t, ‖B k‖ ^ 4 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
      _ ≤ Q := hB₄
  have hc : (E.card : ℝ) ≤ Q / τ ^ 4 := (le_div_iff₀ (pow_pos hτ 4)).mpr hcount
  have hp (v : V) (hv : v ∈ s) (k : K) (hk : k ∈ t) :
      ‖B k‖ * ‖F v k‖ * ‖G v k‖ ≤
        τ * (‖F v k‖ * ‖G v k‖) +
          if τ < ‖B k‖ then M * G₀ * ‖F v k‖ else 0 := by
    by_cases hh : τ < ‖B k‖
    · rw [ite_eq_left hh]
      have he : ‖B k‖ * ‖F v k‖ * ‖G v k‖ ≤ M * G₀ * ‖F v k‖ := by
        calc
          _ ≤ M * ‖F v k‖ * G₀ := by gcongr; exact hB k hk; exact hG v hv k hk
          _ = _ := by ring
      exact he.trans (le_add_of_nonneg_left (by positivity))
    · rw [ite_eq_right hh, add_zero, ← mul_assoc]
      gcongr
      exact le_of_not_gt hh
  have hlo : (∑ v ∈ s, ∑ k ∈ t, τ * (‖F v k‖ * ‖G v k‖)) ≤
      (s.card : ℝ) * τ * P := by
    simp only [← mul_sum]
    calc
      _ ≤ τ * ∑ _v ∈ s, P := by gcongr with v hv; exact hFG v hv
      _ = _ := by simp [mul_left_comm, mul_comm]
  have hhi : (∑ v ∈ s, ∑ k ∈ t,
      if τ < ‖B k‖ then M * G₀ * ‖F v k‖ else 0) ≤
      Q / τ ^ 4 * M * G₀ * S := by
    rw [sum_comm]
    have heq : (∑ k ∈ t, ∑ v ∈ s,
        if τ < ‖B k‖ then M * G₀ * ‖F v k‖ else 0) =
        M * G₀ * ∑ k ∈ E, ∑ v ∈ s, ‖F v k‖ := by
      simp only [E, sum_filter, mul_sum]
      apply sum_congr rfl
      intro k hk
      by_cases hh : τ < ‖B k‖ <;> simp [hh, mul_assoc, mul_sum]
    rw [heq]
    calc
      _ ≤ M * G₀ * ∑ _k ∈ E, S := by
        gcongr with k hk
        exact hF k (mem_filter.mp hk).1
      _ = (E.card : ℝ) * M * G₀ * S := by simp [mul_comm, mul_left_comm, mul_assoc]
      _ ≤ Q / τ ^ 4 * M * G₀ * S := by gcongr
  calc
    _ ≤ ∑ v ∈ s, ∑ k ∈ t,
        (τ * (‖F v k‖ * ‖G v k‖) +
          if τ < ‖B k‖ then M * G₀ * ‖F v k‖ else 0) :=
      sum_le_sum (fun v hv => sum_le_sum (fun k hk => hp v hv k hk))
    _ = (∑ v ∈ s, ∑ k ∈ t, τ * (‖F v k‖ * ‖G v k‖)) +
        (∑ v ∈ s, ∑ k ∈ t, if τ < ‖B k‖ then M * G₀ * ‖F v k‖ else 0) := by
      simp only [sum_add_distrib]
    _ ≤ _ := add_le_add hlo hhi

omit [NeZero N] in
theorem natCast_inj_of_lt {x y : ℕ} (hx : x < N) (hy : y < N) :
    (x : ZMod N) = (y : ZMod N) ↔ x = y := by
  constructor
  · intro hh
    simpa only [ZMod.val_natCast_of_lt hx, ZMod.val_natCast_of_lt hy] using
      congrArg ZMod.val hh
  · rintro rfl
    rfl

theorem mean_poly_three (s : Finset ι) (t : Finset κ) {ν : Type*}
    (r : Finset ν) (w : ι → ℂ) (v : κ → ℂ) (u : ν → ℂ)
    (a : ι → ZMod N) (b : κ → ZMod N) (c : ν → ZMod N) :
    meanC (fun k => poly s w a k * poly t v b k * poly r u c k) =
      ∑ i ∈ s, ∑ j ∈ t, ∑ l ∈ r,
        if a i + b j + c l = 0 then w i * v j * u l else 0 := by
  classical
  simp_rw [poly_mul s t w v a b]
  rw [mean_poly_mul, sum_product]

theorem short_convolution (Z : Finset ℕ) (h D v : ℕ) (f g : ℕ → ℂ)
    (hZ : ∀ z ∈ Z, z < 2 * D) (hN : (2 * h + 1) * D < N) :
    meanC (fun k : ZMod N =>
      poly Z (fun z => (z : ℂ)⁻¹) (fun z => ((h * z : ℕ) : ZMod N)) k *
      poly (Icc 1 D) (fun m => f (v + m)) (fun m => (m : ZMod N)) k *
      poly (Icc 1 ((2 * h + 1) * D)) (fun a => g (v + a))
        (fun a => -(a : ZMod N)) k) =
      ∑ z ∈ Z, ∑ m ∈ Icc 1 D, (z : ℂ)⁻¹ * f (v + m) * g (v + m + h * z) := by
  classical
  rw [mean_poly_three]
  apply sum_congr rfl
  intro z hz
  apply sum_congr rfl
  intro m hm
  obtain ⟨hm1, hmD⟩ := mem_Icc.mp hm
  have hsum : m + h * z ≤ (2 * h + 1) * D := by
    have hh := Nat.mul_le_mul_left h (hZ z hz).le
    nlinarith
  have hmem : m + h * z ∈ Finset.Icc 1 ((2 * h + 1) * D) := Finset.mem_Icc.mpr ⟨by omega, hsum⟩
  have hid (a : ℕ) (ha : a ∈ Finset.Icc 1 ((2 * h + 1) * D)) :
      ((h * z : ℕ) : ZMod N) + (m : ZMod N) + -(a : ZMod N) = 0 ↔
        a = m + h * z := by
    rw [← sub_eq_add_neg, sub_eq_zero, ← Nat.cast_add,
      natCast_inj_of_lt (by omega) (lt_of_le_of_lt (mem_Icc.mp ha).2 hN)]
    omega
  have heq : (∑ a ∈ Icc 1 ((2 * h + 1) * D),
      if ((h * z : ℕ) : ZMod N) + (m : ZMod N) + -(a : ZMod N) = 0 then
        (z : ℂ)⁻¹ * f (v + m) * g (v + a) else 0) =
      ∑ a ∈ Icc 1 ((2 * h + 1) * D),
        if a = m + h * z then (z : ℂ)⁻¹ * f (v + m) * g (v + a) else 0 := by
    apply sum_congr rfl
    intro a ha
    simp only [hid a ha]
  rw [heq, sum_ite_eq', ite_eq_left hmem]
  simp only [Nat.add_assoc]

theorem interval_parseval_bound (D : ℕ) (w : ℕ → ℂ) (hD : D < N)
    (hw : ∀ m ∈ Finset.Icc 1 D, ‖w m‖ ≤ 1) :
    meanR (fun k => ‖poly (Icc 1 D) w (fun m => (m : ZMod N)) k‖ ^ 2) ≤ D := by
  have hinj : Set.InjOn (fun m : ℕ => (m : ZMod N)) (Finset.Icc 1 D) := by
    intro x hx y hy he
    exact (natCast_inj_of_lt (lt_of_le_of_lt (Finset.mem_Icc.mp hx).2 hD)
      (lt_of_le_of_lt (Finset.mem_Icc.mp hy).2 hD)).mp he
  rw [parseval _ _ _ hinj]
  calc
    _ ≤ ∑ _m ∈ Icc 1 D, (1 : ℝ) := by
      apply sum_le_sum
      intro m hm
      simpa using pow_le_pow_left₀ (norm_nonneg _) (hw m hm) 2
    _ = _ := by simp

theorem norm_meanC_le (f : ZMod N → ℂ) :
    ‖meanC f‖ ≤ meanR (fun k => ‖f k‖) := by
  simp only [meanC, meanR, norm_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

theorem norm_poly_le (s : Finset ι) (w : ι → ℂ) (a : ι → ZMod N) (k : ZMod N) :
    ‖poly s w a k‖ ≤ ∑ i ∈ s, ‖w i‖ := by
  unfold poly
  calc
    _ ≤ ∑ i ∈ s, ‖w i * ZMod.stdAddChar (a i * k)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, AddChar.norm_apply, mul_one]

theorem norm_poly_le_card (s : Finset ι) (w : ι → ℂ) (a : ι → ZMod N)
    (hw : ∀ i ∈ s, ‖w i‖ ≤ 1) (k : ZMod N) :
    ‖poly s w a k‖ ≤ s.card := by
  calc
    _ ≤ ∑ i ∈ s, ‖w i‖ := norm_poly_le s w a k
    _ ≤ ∑ _i ∈ s, (1 : ℝ) := sum_le_sum hw
    _ = _ := by simp

theorem sum_eq_mul_meanR (f : ZMod N → ℝ) :
    ∑ k, f k = (N : ℝ) * meanR f := by
  simp [meanR, NeZero.ne N]

theorem meanR_cauchy (f g : ZMod N → ℝ) :
    meanR (fun k => f k * g k) ≤
      Real.sqrt (meanR (fun k => f k ^ 2)) * Real.sqrt (meanR (fun k => g k ^ 2)) := by
  have hh : meanR (fun k => f k * g k) ^ 2 ≤
      meanR (fun k => f k ^ 2) * meanR (fun k => g k ^ 2) := by
    unfold meanR
    calc
      _ = (N : ℝ)⁻¹ ^ 2 * (∑ k, f k * g k) ^ 2 := by ring
      _ ≤ (N : ℝ)⁻¹ ^ 2 * ((∑ k, f k ^ 2) * ∑ k, g k ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_mul_sq_le_sq_mul_sq univ f g) (sq_nonneg _)
      _ = _ := by ring
  exact (Real.le_sqrt_of_sq_le hh).trans_eq
    (Real.sqrt_mul (meanR_nonneg _ (fun k => sq_nonneg _)) _)

theorem low_high_mean_bound {V : Type*} (s : Finset V)
    (B : ZMod N → ℂ) (F G : V → ZMod N → ℂ) (τ M G₀ S P Q : ℝ)
    (hτ : 0 < τ) (hM : 0 ≤ M) (hG₀ : 0 ≤ G₀) (hS : 0 ≤ S)
    (hB : ∀ k, ‖B k‖ ≤ M)
    (hG : ∀ v ∈ s, ∀ k, ‖G v k‖ ≤ G₀)
    (hF : ∀ k, ∑ v ∈ s, ‖F v k‖ ≤ S)
    (hFG : ∀ v ∈ s, meanR (fun k => ‖F v k‖ * ‖G v k‖) ≤ P)
    (hB₄ : meanR (fun k => ‖B k‖ ^ 4) ≤ Q) :
    meanR (fun k => ∑ v ∈ s, ‖B k‖ * ‖F v k‖ * ‖G v k‖) ≤
      (s.card : ℝ) * τ * P + Q / τ ^ 4 * M * G₀ * S := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hfg (v : V) (hv : v ∈ s) :
      (∑ k, ‖F v k‖ * ‖G v k‖) ≤ (N : ℝ) * P := by
    rw [sum_eq_mul_meanR]
    exact mul_le_mul_of_nonneg_left (hFG v hv) hN.le
  have hb4 : (∑ k, ‖B k‖ ^ 4) ≤ (N : ℝ) * Q := by
    rw [sum_eq_mul_meanR]
    exact mul_le_mul_of_nonneg_left hB₄ hN.le
  have he := low_high_frequency_bound s univ B F G τ M G₀ S ((N : ℝ) * P)
    ((N : ℝ) * Q) hτ hM hG₀ hS (fun k _ => hB k)
    (fun v hv k _ => hG v hv k) (fun k _ => hF k) hfg hb4
  unfold meanR
  rw [sum_comm]
  calc
    _ ≤ (N : ℝ)⁻¹ * ((s.card : ℝ) * τ * ((N : ℝ) * P) +
        ((N : ℝ) * Q) / τ ^ 4 * M * G₀ * S) :=
      mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hN.le)
    _ = _ := by field_simp

noncomputable def natEnergyQuadruples (Z : Finset ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((Z ×ˢ Z) ×ˢ (Z ×ˢ Z)).filter (fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2)

noncomputable def natAdditiveEnergy (Z : Finset ℕ) : ℕ := (natEnergyQuadruples Z).card

omit [NeZero N] in

theorem energy_natCast_eq (Z : Finset ℕ) (h M : ℕ) (hh : 0 < h)
    (hZ : ∀ z ∈ Z, z < M) (hN : 2 * h * M ≤ N) :
    additiveEnergy Z (fun z => ((h * z : ℕ) : ZMod N)) = natAdditiveEnergy Z := by
  classical
  unfold additiveEnergy natAdditiveEnergy natEnergyQuadruples
  congr 1
  apply filter_congr
  intro q hq
  obtain ⟨h12, h34⟩ := mem_product.mp hq
  obtain ⟨h1, h2⟩ := mem_product.mp h12
  obtain ⟨h3, h4⟩ := mem_product.mp h34
  have hab (x : ℕ) (hx : x ∈ Z) (y : ℕ) (hy : y ∈ Z) : h * x + h * y < N := by
    have hx' := Nat.mul_lt_mul_of_pos_left (hZ x hx) hh
    have hy' := Nat.mul_lt_mul_of_pos_left (hZ y hy) hh
    nlinarith
  rw [← Nat.cast_add, ← Nat.cast_add,
    natCast_inj_of_lt (hab _ h1 _ h2) (hab _ h3 _ h4)]
  constructor <;> intro he <;> nlinarith

noncomputable def predicateTriples (Z : Finset ℕ) (P : ℕ → Prop)
    [DecidablePred P] : Finset ((ℕ × ℕ) × ℕ) :=
  ((Z ×ˢ Z) ×ˢ Z).filter (fun t => P (t.1.1 + t.1.2 - t.2))

omit [NeZero N] in

theorem energy_le_predicate_triples (Z : Finset ℕ) (P : ℕ → Prop)
    [DecidablePred P] (hP : ∀ z ∈ Z, P z) :
    natAdditiveEnergy Z ≤ (predicateTriples Z P).card := by
  classical
  let f : ((ℕ × ℕ) × (ℕ × ℕ)) → ((ℕ × ℕ) × ℕ) := fun q => (q.1, q.2.1)
  have hinj : Set.InjOn f (natEnergyQuadruples Z) := by
    intro q hq r hr he
    have hqe := (mem_filter.mp hq).2
    have hre := (mem_filter.mp hr).2
    have he' : q.1 = r.1 ∧ q.2.1 = r.2.1 := by simpa only [f, Prod.mk.injEq] using he
    have h4 : q.2.2 = r.2.2 := by
      rw [he'.1, he'.2] at hqe
      omega
    exact Prod.ext he'.1 (Prod.ext he'.2 h4)
  have hsub : (natEnergyQuadruples Z).image f ⊆ predicateTriples Z P := by
    intro t ht
    obtain ⟨q, hq, rfl⟩ := mem_image.mp ht
    obtain ⟨hq, he⟩ := mem_filter.mp hq
    obtain ⟨h12, h34⟩ := mem_product.mp hq
    obtain ⟨h3, h4⟩ := mem_product.mp h34
    apply mem_filter.mpr
    constructor
    · exact mem_product.mpr ⟨h12, h3⟩
    · dsimp [f]
      have he' : q.1.1 + q.1.2 - q.2.1 = q.2.2 := by omega
      rw [he']
      exact hP _ h4
  calc
    _ = ((natEnergyQuadruples Z).image f).card := (card_image_iff.mpr hinj).symm
    _ ≤ _ := Finset.card_le_card hsub

theorem reciprocal_poly_norm_le (Z : Finset ℕ) (h : ℕ) (k : ZMod N) :
    ‖poly Z (fun z => (z : ℂ)⁻¹) (fun z => ((h * z : ℕ) : ZMod N)) k‖ ≤
      ∑ z ∈ Z, (z : ℝ)⁻¹ := by
  simpa only [norm_inv, Complex.norm_natCast] using
    norm_poly_le Z (fun z => (z : ℂ)⁻¹) (fun z => ((h * z : ℕ) : ZMod N)) k

theorem reciprocal_poly_norm_le_count (Z : Finset ℕ) (h D : ℕ) (hD : 0 < D)
    (hZ : ∀ z ∈ Z, D ≤ z) (k : ZMod N) :
    ‖poly Z (fun z => (z : ℂ)⁻¹) (fun z => ((h * z : ℕ) : ZMod N)) k‖ ≤
      (Z.card : ℝ) / D := by
  calc
    _ ≤ ∑ z ∈ Z, (z : ℝ)⁻¹ := reciprocal_poly_norm_le Z h k
    _ ≤ ∑ _z ∈ Z, (D : ℝ)⁻¹ := by
      apply sum_le_sum
      intro z hz
      exact inv_anti₀ (by exact_mod_cast hD) (by exact_mod_cast hZ z hz)
    _ = _ := by simp [div_eq_mul_inv]

theorem reciprocal_fourth_moment_le (Z : Finset ℕ) (h D : ℕ) (hh : 0 < h)
    (hD : 0 < D) (hZ : ∀ z ∈ Z, D ≤ z ∧ z < 2 * D) (hN : 4 * h * D ≤ N) :
    meanR (fun k : ZMod N =>
      ‖poly Z (fun z => (z : ℂ)⁻¹) (fun z => ((h * z : ℕ) : ZMod N)) k‖ ^ 4) ≤
        natAdditiveEnergy Z * (D : ℝ)⁻¹ ^ 4 := by
  have he := fourth_moment_le_energy Z (fun z => (z : ℝ)⁻¹)
    (fun z => ((h * z : ℕ) : ZMod N)) (D : ℝ)⁻¹ (by positivity)
    (fun z hz => ⟨by positivity,
      inv_anti₀ (by exact_mod_cast hD) (by exact_mod_cast (hZ z hz).1)⟩)
  have hN' : 2 * h * (2 * D) ≤ N := by nlinarith
  rw [energy_natCast_eq Z h (2 * D) hh (fun z hz => (hZ z hz).2) hN'] at he
  simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using he

omit [NeZero N] in
theorem sum_Icc_one_eq_range {E : Type*} [AddCommMonoid E] (H : ℕ → E) (U : ℕ) :
    ∑ v ∈ Icc 1 U, H v = ∑ v ∈ range U, H (v + 1) := by
  have hi : Finset.Icc 1 U = Finset.Ico 1 (U + 1) := by
    ext v
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hi, sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

omit [NeZero N] in

theorem prefix_translation_bound (H : ℕ → ℂ) (U m : ℕ) (C : ℝ)
    (hH : ∀ n, ‖H n‖ ≤ C) :
    ‖(∑ v ∈ Icc 1 U, H (v + m)) - ∑ v ∈ Icc 1 U, H v‖ ≤ 2 * m * C := by
  rw [sum_Icc_one_eq_range, sum_Icc_one_eq_range]
  have he : (∑ v ∈ range U, H (v + 1 + m)) - ∑ v ∈ range U, H (v + 1) =
      (∑ v ∈ range m, H (U + v + 1)) - ∑ v ∈ range m, H (v + 1) := by
    have ha := sum_range_add (fun v => H (v + 1)) U m
    have hb := sum_range_add (fun v => H (v + 1)) m U
    rw [Nat.add_comm m U] at hb
    simp only [Nat.add_comm m _, Nat.add_right_comm _ m 1] at hb
    rw [ha] at hb
    linear_combination -hb
  rw [he]
  calc
    _ ≤ ‖∑ v ∈ range m, H (U + v + 1)‖ + ‖∑ v ∈ range m, H (v + 1)‖ :=
      norm_sub_le _ _
    _ ≤ (∑ v ∈ range m, ‖H (U + v + 1)‖) + ∑ v ∈ range m, ‖H (v + 1)‖ :=
      add_le_add (norm_sum_le _ _) (norm_sum_le _ _)
    _ ≤ (∑ _v ∈ range m, C) + ∑ _v ∈ range m, C :=
      add_le_add (sum_le_sum (fun v _ => hH _)) (sum_le_sum (fun v _ => hH _))
    _ = _ := by simp; ring

omit [NeZero N] in
theorem averaged_prefix_translation_bound (H : ℕ → ℂ) (U D : ℕ) (C : ℝ)
    (hD : 0 < D) (hC : 0 ≤ C) (hH : ∀ n, ‖H n‖ ≤ C) :
    ‖(D : ℂ)⁻¹ * (∑ m ∈ Icc 1 D, ∑ v ∈ Icc 1 U, H (v + m)) -
      ∑ v ∈ Icc 1 U, H v‖ ≤ 2 * D * C := by
  have hDz : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have he : (D : ℂ)⁻¹ * (∑ m ∈ Icc 1 D, ∑ v ∈ Icc 1 U, H (v + m)) -
      ∑ v ∈ Icc 1 U, H v =
      (D : ℂ)⁻¹ * ∑ m ∈ Icc 1 D,
        ((∑ v ∈ Icc 1 U, H (v + m)) - ∑ v ∈ Icc 1 U, H v) := by
    rw [sum_sub_distrib, mul_sub]
    simp [hDz]
  rw [he, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (D : ℝ)⁻¹ * ∑ m ∈ Icc 1 D,
        ‖(∑ v ∈ Icc 1 U, H (v + m)) - ∑ v ∈ Icc 1 U, H v‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (D : ℝ)⁻¹ * ∑ _m ∈ Icc 1 D, (2 * D * C) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum
      intro m hm
      have hmD : (m : ℝ) ≤ D := by exact_mod_cast (mem_Icc.mp hm).2
      apply (prefix_translation_bound H U m C hH).trans
      gcongr
    _ = _ := by simp [hDr.ne', mul_assoc]

theorem shortEnvelope_bound (D U : ℕ) (f : ℕ → ℂ) (k : ZMod N) :
    (∑ v ∈ Icc 1 U, ‖poly (Icc 1 D) (fun m => f (v + m))
      (fun m => (m : ZMod N)) k‖) ≤ shortEnvelope (N := N) D U f := by
  unfold shortEnvelope
  exact le_sup' (fun k : ZMod N =>
    ∑ v ∈ Icc 1 U, ‖poly (Icc 1 D) (fun m => f (v + m))
      (fun m => (m : ZMod N)) k‖) (mem_univ k)

theorem shortEnvelope_nonneg (D U : ℕ) (f : ℕ → ℂ) :
    0 ≤ shortEnvelope (N := N) D U f :=
  (sum_nonneg (fun _ _ => norm_nonneg _)).trans (shortEnvelope_bound D U f 0)

theorem interval_parseval_neg_bound (D : ℕ) (w : ℕ → ℂ) (hD : D < N)
    (hw : ∀ m ∈ Finset.Icc 1 D, ‖w m‖ ≤ 1) :
    meanR (fun k => ‖poly (Icc 1 D) w (fun m => -(m : ZMod N)) k‖ ^ 2) ≤ D := by
  have hinj : Set.InjOn (fun m : ℕ => -(m : ZMod N)) (Finset.Icc 1 D) := by
    intro x hx y hy he
    exact (natCast_inj_of_lt (lt_of_le_of_lt (Finset.mem_Icc.mp hx).2 hD)
      (lt_of_le_of_lt (Finset.mem_Icc.mp hy).2 hD)).mp (neg_inj.mp he)
  rw [parseval _ _ _ hinj]
  calc
    _ ≤ ∑ _m ∈ Icc 1 D, (1 : ℝ) := by
      apply sum_le_sum
      intro m hm
      simpa using pow_le_pow_left₀ (norm_nonneg _) (hw m hm) 2
    _ = _ := by simp

theorem rough_correlation_bound (Z : Finset ℕ) (h D U : ℕ) (f g : ℕ → ℂ)
    (hh : 0 < h) (hD : 0 < D)
    (hZ : ∀ z ∈ Z, D ≤ z ∧ z < 2 * D)
    (hN₁ : (2 * h + 1) * D < N) (hN₂ : 4 * h * D ≤ N)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    (τ : ℝ) (hτ : 0 < τ) :
    ‖∑ v ∈ Icc 1 U, ∑ z ∈ Z, (z : ℂ)⁻¹ * f v * g (v + h * z)‖ ≤
      2 * D * (∑ z ∈ Z, (z : ℝ)⁻¹) +
      ((U : ℝ) * τ * (Real.sqrt D * Real.sqrt ((2 * h + 1) * D)) +
        ((natAdditiveEnergy Z : ℝ) * (D : ℝ)⁻¹ ^ 4) / τ ^ 4 *
          (∑ z ∈ Z, (z : ℝ)⁻¹) * ((2 * h + 1) * D) *
            shortEnvelope (N := N) D U f) / D := by
  classical
  let M : ℝ := ∑ z ∈ Z, (z : ℝ)⁻¹
  let A : ℕ := (2 * h + 1) * D
  let B : ZMod N → ℂ := poly Z (fun z => (z : ℂ)⁻¹)
    (fun z => ((h * z : ℕ) : ZMod N))
  let F : ℕ → ZMod N → ℂ := fun v => poly (Icc 1 D) (fun m => f (v + m))
    (fun m => (m : ZMod N))
  let G : ℕ → ZMod N → ℂ := fun v => poly (Icc 1 A) (fun a => g (v + a))
    (fun a => -(a : ZMod N))
  let H : ℕ → ℂ := fun v => ∑ z ∈ Z, (z : ℂ)⁻¹ * f v * g (v + h * z)
  let R : ℝ := (U : ℝ) * τ * (Real.sqrt D * Real.sqrt A) +
    ((natAdditiveEnergy Z : ℝ) * (D : ℝ)⁻¹ ^ 4) / τ ^ 4 * M * A *
      shortEnvelope (N := N) D U f
  have hM : 0 ≤ M := sum_nonneg (fun z _ => by positivity)
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hDN : D < N := by nlinarith
  have hFG (v : ℕ) (_hv : v ∈ Finset.Icc 1 U) :
      meanR (fun k => ‖F v k‖ * ‖G v k‖) ≤ Real.sqrt D * Real.sqrt A := by
    apply (meanR_cauchy _ _).trans
    apply mul_le_mul (Real.sqrt_le_sqrt (interval_parseval_bound D
      (fun m => f (v + m)) hDN (fun m _ => hf _)))
      (Real.sqrt_le_sqrt (interval_parseval_neg_bound A
        (fun a => g (v + a)) hN₁ (fun a _ => hg _)))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hfreq : meanR (fun k => ∑ v ∈ Icc 1 U, ‖B k‖ * ‖F v k‖ * ‖G v k‖) ≤ R := by
    have he := low_high_mean_bound (Icc 1 U) B F G τ M A
      (shortEnvelope (N := N) D U f) (Real.sqrt D * Real.sqrt A)
      ((natAdditiveEnergy Z : ℝ) * (D : ℝ)⁻¹ ^ 4) hτ hM (by positivity)
      (shortEnvelope_nonneg D U f) (fun k => reciprocal_poly_norm_le Z h k)
      (fun v _ k => by
        have hb := norm_poly_le_card (Icc 1 A) (fun a => g (v + a))
          (fun a => -(a : ZMod N)) (fun a _ => hg _) k
        simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hb)
      (fun k => shortEnvelope_bound D U f k) hFG
      (reciprocal_fourth_moment_le Z h D hh hD hZ hN₂)
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using he
  have hconv : meanC (fun k => ∑ v ∈ Icc 1 U, B k * F v k * G v k) =
      ∑ m ∈ Icc 1 D, ∑ v ∈ Icc 1 U, H (v + m) := by
    rw [meanC_sum]
    simp only [B, F, G, A]
    simp_rw [short_convolution Z h D _ f g (fun z hz => (hZ z hz).2) hN₁]
    rw [sum_comm (s := Icc 1 D) (t := Icc 1 U)]
    apply sum_congr rfl
    intro v hv
    exact sum_comm
  have hnorm : ‖∑ m ∈ Icc 1 D, ∑ v ∈ Icc 1 U, H (v + m)‖ ≤ R := by
    rw [← hconv]
    apply (norm_meanC_le _).trans
    apply le_trans _ hfreq
    apply meanR_mono
    intro k
    simpa only [norm_mul] using
      (norm_sum_le (Icc 1 U) (fun v => B k * F v k * G v k))
  have hH (n : ℕ) : ‖H n‖ ≤ M := by
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro z hz
    simp only [norm_mul, norm_inv, Complex.norm_natCast]
    calc
      _ ≤ (z : ℝ)⁻¹ * 1 * 1 := by gcongr <;> [exact hf n; exact hg _]
      _ = _ := by ring
  have hend := averaged_prefix_translation_bound H U D M hD hM hH
  have htot : ‖∑ v ∈ Icc 1 U, H v‖ ≤ 2 * D * M + R / D := by
    calc
      _ ≤ ‖(∑ v ∈ Icc 1 U, H v) -
          (D : ℂ)⁻¹ * ∑ m ∈ Icc 1 D, ∑ v ∈ Icc 1 U, H (v + m)‖ +
          ‖(D : ℂ)⁻¹ * ∑ m ∈ Icc 1 D, ∑ v ∈ Icc 1 U, H (v + m)‖ :=
        norm_le_norm_sub_add _ _
      _ ≤ 2 * D * M + (D : ℝ)⁻¹ * R := by
        rw [norm_sub_rev, norm_mul, norm_inv, Complex.norm_natCast]
        exact add_le_add hend (mul_le_mul_of_nonneg_left hnorm (by positivity))
      _ = _ := by ring
  simpa only [H, R, M, A, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    using htot

omit [NeZero N] in
@[simp] theorem abs_liouville_le_one (n : ℕ) : |liouville n| ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    norm_num [liouville]
  · have hs : liouville n ^ 2 = 1 := by
      rw [liouville, ArithmeticFunction.liouville_apply hn]
      push_cast
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    nlinarith [sq_abs (liouville n), abs_nonneg (liouville n)]

theorem progressionCoeff_norm_le (l : ℕ) (b : ℤ) (n : ℕ) :
    ‖progressionCoeff l b n‖ ≤ 1 := by
  unfold progressionCoeff
  split_ifs
  · simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_liouville_le_one n
  · simp

theorem liouville_rough_shift_bound (Z : Finset ℕ) (h D l : ℕ) (b : ℤ) (Y : ℝ)
    (hh : 0 < h) (hD : 0 < D) (hY : 0 < Y)
    (hZ : ∀ z ∈ Z, D ≤ z ∧ z < 2 * D)
    (hN₁ : (2 * h + 1) * D < N) (hN₂ : 4 * h * D ≤ N)
    (τ : ℝ) (hτ : 0 < τ) :
    |Y⁻¹ * ∑ v ∈ Icc 1 ⌊Y⌋₊, ∑ z ∈ Z, (z : ℝ)⁻¹ *
      (if (v : ℤ) ≡ b [ZMOD (l : ℤ)] then liouville v * liouville (v + h * z) else 0)| ≤
      Y⁻¹ * (2 * D * (∑ z ∈ Z, (z : ℝ)⁻¹) +
        ((⌊Y⌋₊ : ℝ) * τ * (Real.sqrt D * Real.sqrt ((2 * h + 1) * D)) +
          ((natAdditiveEnergy Z : ℝ) * (D : ℝ)⁻¹ ^ 4) / τ ^ 4 *
            (∑ z ∈ Z, (z : ℝ)⁻¹) * ((2 * h + 1) * D) *
              shortEnvelope (N := N) D ⌊Y⌋₊ (progressionCoeff l b)) / D) := by
  have he := rough_correlation_bound Z h D ⌊Y⌋₊ (progressionCoeff l b)
    (fun n => (liouville n : ℂ)) hh hD hZ hN₁ hN₂
    (progressionCoeff_norm_le l b)
    (fun n => by simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_liouville_le_one n)
    τ hτ
  have hcast : ((∑ v ∈ Icc 1 ⌊Y⌋₊, ∑ z ∈ Z, (z : ℝ)⁻¹ *
      (if (v : ℤ) ≡ b [ZMOD (l : ℤ)] then liouville v * liouville (v + h * z) else 0) : ℝ) : ℂ) =
      ∑ v ∈ Icc 1 ⌊Y⌋₊, ∑ z ∈ Z, (z : ℂ)⁻¹ * progressionCoeff l b v *
        (liouville (v + h * z) : ℂ) := by
    push_cast
    apply sum_congr rfl
    intro v hv
    apply sum_congr rfl
    intro z hz
    unfold progressionCoeff
    split_ifs <;> simp [mul_assoc]
  rw [← hcast, Complex.norm_real, Real.norm_eq_abs] at he
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hY.le)]
  exact mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hY.le)

omit [NeZero N] in
theorem natAdditiveEnergy_mono {Z W : Finset ℕ} (hZW : Z ⊆ W) :
    natAdditiveEnergy Z ≤ natAdditiveEnergy W := by
  apply Finset.card_le_card
  apply filter_subset_filter
  exact product_subset_product (product_subset_product hZW hZW) (product_subset_product hZW hZW)

def IsRough (y : ℝ) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → (p : ℝ) ≤ y → ¬ p ∣ n

noncomputable def roughIntegers (D : ℕ) (y : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Ico D (2 * D)).filter (IsRough y)

noncomputable def roughTriples (D : ℕ) (y : ℝ) : Finset ((ℕ × ℕ) × ℕ) := by
  classical
  exact predicateTriples (roughIntegers D y) (IsRough y)

omit [NeZero N] in
theorem energy_le_roughTriples (Z : Finset ℕ) (D : ℕ) (y : ℝ)
    (hZ : ∀ z ∈ Z, D ≤ z ∧ z < 2 * D ∧ IsRough y z) :
    natAdditiveEnergy Z ≤ (roughTriples D y).card := by
  classical
  have hsub : Z ⊆ roughIntegers D y := by
    intro z hz
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨(hZ z hz).1, (hZ z hz).2.1⟩, (hZ z hz).2.2⟩
  apply (natAdditiveEnergy_mono hsub).trans
  exact energy_le_predicate_triples (roughIntegers D y) (IsRough y)
    (fun z hz => (mem_filter.mp hz).2)

omit [NeZero N] in
theorem reciprocal_mass_le_rough_count (Z : Finset ℕ) (D : ℕ) (y : ℝ)
    (hD : 0 < D) (hZ : ∀ z ∈ Z, D ≤ z ∧ z < 2 * D ∧ IsRough y z) :
    (∑ z ∈ Z, (z : ℝ)⁻¹) ≤ (roughIntegers D y).card / (D : ℝ) := by
  classical
  have hsub : Z ⊆ roughIntegers D y := by
    intro z hz
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨(hZ z hz).1, (hZ z hz).2.1⟩, (hZ z hz).2.2⟩
  calc
    _ ≤ ∑ _z ∈ Z, (D : ℝ)⁻¹ := by
      apply sum_le_sum
      intro z hz
      exact inv_anti₀ (by exact_mod_cast hD) (by exact_mod_cast (hZ z hz).1)
    _ = (Z.card : ℝ) / D := by simp [div_eq_mul_inv]
    _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) (by positivity)

end SourceRoughFourier
end OrdinaryCorrelations

end

end OAI
