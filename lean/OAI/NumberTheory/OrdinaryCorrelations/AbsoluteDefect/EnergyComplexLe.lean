import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.OneBounded
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.MeanC

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

namespace OrdinaryRoughWeighted
open OrdinaryCorrelations SourceRoughFourier Finset
variable {N : ℕ} [NeZero N] {ι : Type*}
lemma energy_complex_le (s : Finset ι) (w : ι → ℂ) (a : ι → ZMod N) :
    meanR (fun k => ‖poly s w a k‖^2) ≤
      ∑ i∈s,∑ j∈s, if a i=a j then ‖w i‖*‖w j‖ else 0 := by
  classical
  have he : (meanR (fun k => ‖poly s w a k‖^2):ℂ) =
      ∑i∈s,∑j∈s,if a i=a j then w i * star (w j) else 0 := by
    rw [meanR_cast]
    simp only [Complex.ofReal_pow, ← Complex.mul_conj']
    simp_rw [conjugate_poly]
    rw [mean_poly_mul]
    simp only [← sub_eq_add_neg,sub_eq_zero,starRingEnd_apply]
  have hre := congrArg Complex.re he
  simp only [Complex.ofReal_re,Complex.re_sum] at hre
  rw [hre]
  apply sum_le_sum
  intro i hi
  apply sum_le_sum
  intro j hj
  split_ifs <;> simp_all only [Complex.zero_re,le_refl]
  calc
    _ ≤ ‖w i * star (w j)‖ := Complex.re_le_norm _
    _ = _ := by simp only [norm_mul,norm_star]

lemma fourth_complex_le (s : Finset ι) (w : ι→ℂ) (a : ι→ZMod N)
    (W : ℝ) (hW : 0≤W) (hw : ∀i∈s,‖w i‖≤W) :
    meanR (fun k=>‖poly s w a k‖^4) ≤ additiveEnergy s a * W^4 := by
  classical
  have hp (k : ZMod N) : ‖poly s w a k‖^4 =
      ‖poly (s×ˢs) (fun ij => w ij.1*w ij.2) (fun ij=>a ij.1+a ij.2) k‖^2 := by
    rw [←poly_mul,norm_mul]; ring
  simp_rw [hp]
  apply (energy_complex_le _ _ _).trans
  simp only [norm_mul,sum_product]
  let E := ((s×ˢs)×ˢ(s×ˢs)).filter
    (fun ij=> a ij.1.1+a ij.1.2 = a ij.2.1+a ij.2.2)
  have heq : (∑i∈s,∑j∈s,∑u∈s,∑v∈s, if a i+a j=a u+a v then
      (‖w i‖*‖w j‖)*(‖w u‖*‖w v‖) else 0) =
      ∑ij∈E,(‖w ij.1.1‖*‖w ij.1.2‖)*(‖w ij.2.1‖*‖w ij.2.2‖) := by
    simp only [E,sum_filter,sum_product]
  rw [heq]
  calc
    _ ≤ ∑ _ij∈E,W^4 := by
      apply sum_le_sum
      intro ij hij
      obtain ⟨hij,_⟩ := mem_filter.mp hij
      obtain ⟨hij,huv⟩ := mem_product.mp hij
      obtain ⟨hi,hj⟩ := mem_product.mp hij
      obtain ⟨hu,hv⟩ := mem_product.mp huv
      calc
        _ ≤ (W*W)*(W*W) := by gcongr <;> exact hw _ (by assumption)
        _ = _ := by ring
    _ = _ := by simp [additiveEnergy,E,nsmul_eq_mul]

theorem weighted_short_convolution (Z : Finset ℕ) (h D v : ℕ) (f g w : ℕ → ℂ)
    (hZ : ∀ z ∈ Z, z < 2 * D) (hN : (2 * h + 1) * D < N) :
    meanC (fun k : ZMod N =>
      poly Z w (fun z => ((h * z : ℕ) : ZMod N)) k *
      poly (Icc 1 D) (fun m => f (v + m)) (fun m => (m : ZMod N)) k *
      poly (Icc 1 ((2 * h + 1) * D)) (fun a => g (v + a))
        (fun a => -(a : ZMod N)) k) =
      ∑ z ∈ Z, ∑ m ∈ Icc 1 D, w z * f (v + m) * g (v + m + h * z) := by
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
      natCast_inj_of_lt (by omega) (lt_of_le_of_lt (Finset.mem_Icc.mp ha).2 hN)]
    omega
  have heq : (∑ a ∈ Icc 1 ((2 * h + 1) * D),
      if ((h * z : ℕ) : ZMod N) + (m : ZMod N) + -(a : ZMod N) = 0 then
        w z * f (v + m) * g (v + a) else 0) =
      ∑ a ∈ Icc 1 ((2 * h + 1) * D),
        if a = m + h * z then w z * f (v + m) * g (v + a) else 0 := by
    apply sum_congr rfl
    intro a ha
    simp only [hid a ha]
  rw [heq, sum_ite_eq', ite_eq_left hmem]
  simp only [Nat.add_assoc]

theorem weighted_correlation_bound (Z : Finset ℕ) (h D U : ℕ) (f g w : ℕ → ℂ)
    (hh : 0 < h) (hD : 0 < D)
    (hZ : ∀ z ∈ Z, D ≤ z ∧ z < 2 * D)
    (hN₁ : (2 * h + 1) * D < N) (hN₂ : 4 * h * D ≤ N)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    (hw : ∀z∈Z, ‖w z‖ ≤ (z:ℝ)⁻¹)
    (S τ : ℝ) (hS0 : 0≤S) (hτ : 0 < τ)
    (hS : (∀k:ZMod N, ∑v∈Icc 1 U,
      ‖poly (Icc 1 D) (fun m=>f (v+m)) (fun m=>(m:ZMod N)) k‖≤S) ∨
      (∀k:ZMod N, ∑v∈Icc 1 U,
      ‖poly (Icc 1 ((2*h+1)*D)) (fun a=>g (v+a)) (fun a=> -(a:ZMod N)) k‖≤S)) :
    ‖∑ v ∈ Icc 1 U, ∑ z ∈ Z, w z * f v * g (v + h * z)‖ ≤
      2 * D * (∑ z ∈ Z, (z : ℝ)⁻¹) +
      ((U : ℝ) * τ * (Real.sqrt D * Real.sqrt ((2 * h + 1) * D)) +
        ((natAdditiveEnergy Z : ℝ) * (D : ℝ)⁻¹ ^ 4) / τ ^ 4 *
          (∑ z ∈ Z, (z : ℝ)⁻¹) * ((2 * h + 1) * D) *
            S) / D := by
  classical
  let M : ℝ := ∑ z ∈ Z, (z : ℝ)⁻¹
  let A : ℕ := (2 * h + 1) * D
  let B : ZMod N → ℂ := poly Z w
    (fun z => ((h * z : ℕ) : ZMod N))
  let F : ℕ → ZMod N → ℂ := fun v => poly (Icc 1 D) (fun m => f (v + m))
    (fun m => (m : ZMod N))
  let G : ℕ → ZMod N → ℂ := fun v => poly (Icc 1 A) (fun a => g (v + a))
    (fun a => -(a : ZMod N))
  let H : ℕ → ℂ := fun v => ∑ z ∈ Z, w z * f v * g (v + h * z)
  let R : ℝ := (U : ℝ) * τ * (Real.sqrt D * Real.sqrt A) +
    ((natAdditiveEnergy Z : ℝ) * (D : ℝ)⁻¹ ^ 4) / τ ^ 4 * M * A *
      S
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
  have hB (k : ZMod N) : ‖B k‖ ≤ M :=
    (norm_poly_le _ _ _ _).trans (sum_le_sum hw)
  have hB4 : meanR (fun k=>‖B k‖^4) ≤ (natAdditiveEnergy Z:ℝ)*(D:ℝ)⁻¹^4 := by
    have he := fourth_complex_le Z w (fun z=>((h*z:ℕ):ZMod N))
      (D:ℝ)⁻¹ (by positivity) (fun z hz=>(hw z hz).trans
        (inv_anti₀ hDr (by exact_mod_cast (hZ z hz).1)))
    rw [energy_natCast_eq Z h (2*D) hh (fun z hz=>(hZ z hz).2) (by nlinarith : 2*h*(2*D)≤N)] at he
    exact he
  have hG (v : ℕ) (k : ZMod N) : ‖G v k‖ ≤ A := by
    have hb := norm_poly_le_card (Icc 1 A) (fun a=>g (v+a))
      (fun a=> -(a:ZMod N)) (fun a _=>hg _) k
    simpa only [Nat.card_Icc,Nat.add_sub_cancel] using hb
  have hF (v : ℕ) (k : ZMod N) : ‖F v k‖ ≤ A := by
    have hb := norm_poly_le_card (Icc 1 D) (fun a=>f (v+a))
      (fun a=>(a:ZMod N)) (fun a _=>hf _) k
    have hDA : D≤A := by dsimp [A]; nlinarith
    apply le_trans (by simpa only [Nat.card_Icc,Nat.add_sub_cancel] using hb)
    exact_mod_cast hDA
  have hfreq : meanR (fun k => ∑ v ∈ Icc 1 U, ‖B k‖ * ‖F v k‖ * ‖G v k‖) ≤ R := by
    rcases hS with hs|hs
    · have he := low_high_mean_bound (Icc 1 U) B F G τ M A S
        (Real.sqrt D * Real.sqrt A) ((natAdditiveEnergy Z:ℝ)*(D:ℝ)⁻¹^4)
        hτ hM (by positivity) hS0 hB (fun v _ k=>hG v k) hs hFG hB4
      simpa only [Nat.card_Icc,Nat.add_sub_cancel] using he
    · have hGF (v : ℕ) (hv : v∈Finset.Icc 1 U) :
          meanR (fun k=>‖G v k‖*‖F v k‖) ≤ Real.sqrt D * Real.sqrt A := by
        simpa only [mul_comm] using hFG v hv
      have he := low_high_mean_bound (Icc 1 U) B G F τ M A S
        (Real.sqrt D * Real.sqrt A) ((natAdditiveEnergy Z:ℝ)*(D:ℝ)⁻¹^4)
        hτ hM (by positivity) hS0 hB (fun v _ k=>hF v k) hs hGF hB4
      have heq : (fun k=>∑v∈Icc 1 U,‖B k‖*‖F v k‖*‖G v k‖) =
          (fun k=>∑v∈Icc 1 U,‖B k‖*‖G v k‖*‖F v k‖) := by
        funext k; apply sum_congr rfl; intro v hv; ring
      rw [heq]
      simpa only [Nat.card_Icc,Nat.add_sub_cancel] using he
  have hconv : meanC (fun k => ∑ v ∈ Icc 1 U, B k * F v k * G v k) =
      ∑ m ∈ Icc 1 D, ∑ v ∈ Icc 1 U, H (v + m) := by
    rw [meanC_sum]
    simp only [B, F, G, A]
    simp_rw [weighted_short_convolution Z h D _ f g w (fun z hz => (hZ z hz).2) hN₁]
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
    simp only [norm_mul]
    calc
      _ ≤ (z : ℝ)⁻¹ * 1 * 1 := by
        exact mul_le_mul (mul_le_mul (hw z hz) (hf n) (norm_nonneg _) (by positivity))
          (hg _) (norm_nonneg _) (by positivity)
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

end OrdinaryRoughWeighted

end

end OAI
