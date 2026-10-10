import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.LogPhaseMulConj
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DivisorTriangleHighAtScale

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace OrdinarySelbergWeights
open Finset OrdinaryLogIntegral OrdinarySparseSieve

theorem sieveTriangleKernel_error_at_scale (t : ℝ) (u B P z : ℕ) (hP : Squarefree P)
    (hu : 1 ≤ u) (hBpos : 0 < B) (hBU : B ≤ u^8) (hz : 1 ≤ z) (hzB : z^2 ≤ B) (ht : |t| ≤ (u : ℝ)^10) :
    ‖sieveTriangleKernel t (B) P z hP -
      ((actualMass P z hP)⁻¹ : ℝ) • triangleMain t (B)‖ ≤
        (z : ℝ)^4 * (1600*(u : ℝ)^7) := by
  let w := actualWeights P z hP
  let E : ℝ := 1600*(u : ℝ)^7
  have hE : 0 ≤ E := by dsimp [E]; positivity
  rw [sieveTriangleKernel_expansion, ← sieveTriangleKernel_main t (B) P z hP hz,
    ← sum_sub_distrib]
  have heach (d : ℕ) (hd : d ∈ P.divisors) (e : ℕ) (he : e ∈ P.divisors) :
      ‖(w d*w e : ℝ) • divisorTriangle t (B) (Nat.lcm d e) -
        (w d*w e : ℝ) • (((Nat.lcm d e : ℝ)⁻¹ : ℝ) • triangleMain t (B))‖ ≤
          |w d| *|w e| *E := by
    by_cases hdz : d ≤ z
    · by_cases hez : e ≤ z
      · have hde : 0 < Nat.lcm d e := Nat.lcm_pos (Nat.pos_of_mem_divisors hd) (Nat.pos_of_mem_divisors he)
        have hB : Nat.lcm d e ≤ B := by
          apply (Nat.lcm_le_mul (Nat.pos_of_mem_divisors hd) (Nat.pos_of_mem_divisors he)).trans
          exact (Nat.mul_le_mul hdz hez).trans (by simpa [pow_two] using hzB)
        rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (divisorTriangle_uniform_at_scale t u B (Nat.lcm d e) hu hBpos hBU hde hB ht)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      · have hw : w e = 0 := actualWeights_zero_above hP (lt_of_not_ge hez) (Nat.dvd_of_mem_divisors he)
        simp [hw]
    · have hw : w d = 0 := actualWeights_zero_above hP (lt_of_not_ge hdz) (Nat.dvd_of_mem_divisors hd)
      simp [hw]
  calc
    _ ≤ ∑ d ∈ P.divisors, ∑ e ∈ P.divisors, |w d| *|w e| *E := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro d hd
      rw [← sum_sub_distrib]
      exact (norm_sum_le _ _).trans (sum_le_sum (fun e he => heach d hd e he))
    _ = (∑ d ∈ P.divisors, |w d|)^2*E := by
      rw [pow_two, sum_mul_sum]
      simp only [sum_mul]
    _ ≤ _ := by
      have hl := actualWeights_l1 (P := P) hP hz
      change (∑ d ∈ P.divisors, |w d|) ≤ (z : ℝ)^2 at hl
      have hh := mul_le_mul_of_nonneg_right (sq_le_sq₀ (sum_nonneg (fun _ _ => abs_nonneg _)) (sq_nonneg (z : ℝ)) |>.mpr hl) hE
      simpa [E, ← pow_mul] using hh

lemma sieveTriangleKernel_norm_at_scale (t : ℝ) (u B P z : ℕ) (hP : Squarefree P)
    (hu : 1 ≤ u) (hBpos : 0 < B) (hBU : B ≤ u^8) (hz : 1 ≤ z) (hzB : z^2 ≤ B) (ht : |t| ≤ (u : ℝ)^10) :
    ‖sieveTriangleKernel t (B) P z hP‖ ≤
      (22*(B : ℝ)*(actualMass P z hP)⁻¹)*(1+t^2)⁻¹ + (z : ℝ)^4*(1600*(u : ℝ)^7) := by
  have hG : 0 ≤ actualMass P z hP := (mass_pos (reciprocalSieve P hP) hz).le
  have hh := norm_le_norm_sub_add (sieveTriangleKernel t (B) P z hP)
    (((actualMass P z hP)⁻¹ : ℝ) • triangleMain t (B))
  have hm := triangleMain_bound t B hBpos
  have he := sieveTriangleKernel_error_at_scale t u B P z hP hu hBpos hBU hz hzB ht
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hG)] at hh
  have hx := mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hG)
  calc
    _ ≤ _ := hh.trans (add_le_add he hx)
    _ = _ := by ring

theorem sparse_rough_gram_row_at_scale (T : Finset ℝ) (u B P z : ℕ) (hP : Squarefree P)
    (hu : 1 ≤ u) (hBpos : 0 < B) (hBU : B ≤ u^8) (hz : 1 ≤ z) (hzB : z^2 ≤ B)
    (hsep : (T : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|))
    (hheight : ∀ t ∈ T, ∀ s ∈ T, |t-s| ≤ (u : ℝ)^10) (t : ℝ) (ht : t ∈ T) :
    (∑ s ∈ T, ‖weightedGram (range (6*B+1)) (triangleSieveMajorant (B) P z hP)
      (fun t n => logPhase t (max ((B : ℕ) : ℝ) n)) t s‖) ≤
      264*(B : ℝ)*(actualMass P z hP)⁻¹ +
        3200*(T.card : ℝ)*(z : ℝ)^4*(u : ℝ)^7 := by
  have hG : 0 ≤ actualMass P z hP := (mass_pos (reciprocalSieve P hP) hz).le
  calc
    _ = ∑ s ∈ T, 2*‖sieveTriangleKernel (t-s) (B) P z hP‖ := by
      simp only [triangleSieveGram, norm_mul, Complex.norm_ofNat]
    _ ≤ ∑ s ∈ T, 2*((22*(B : ℝ)*(actualMass P z hP)⁻¹)*(1+(t-s)^2)⁻¹ +
        (z : ℝ)^4*(1600*(u : ℝ)^7)) := by
      apply sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left (sieveTriangleKernel_norm_at_scale (t-s) u B P z hP hu hBpos hBU hz hzB
        (hheight t ht s hs)) (by norm_num)
    _ = 44*(B : ℝ)*(actualMass P z hP)⁻¹ * (∑ s ∈ T, (1+(s-t)^2)⁻¹) +
        3200*(T.card : ℝ)*(z : ℝ)^4*(u : ℝ)^7 := by
      simp_rw [mul_add, sum_add_distrib, mul_assoc, ← mul_sum]
      have he : (∑ s ∈ T, (1+(t-s)^2)⁻¹) = ∑ s ∈ T, (1+(s-t)^2)⁻¹ := by
        apply sum_congr rfl
        intro s hs
        congr 2
        ring
      rw [he]
      simp only [sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (OrdinarySparseRows.separated_row T t hsep)
        (show 0 ≤ 44*(B : ℝ)*(actualMass P z hP)⁻¹ by positivity)
      nlinarith

theorem rough_mellin_energy_at_scale (S : Finset ℕ) (T : Finset ℝ) (a : ℕ → ℂ)
    (u B P z : ℕ) (hP : Squarefree P) (hu : 1 ≤ u) (hBpos : 0 < B) (hBU : B ≤ u^8) (hz : 1 ≤ z)
    (hzB : z^2 ≤ B) (hS : S ⊆ Icc (2*B) (4*B))
    (hcop : ∀ n ∈ S, n.Coprime P)
    (hsep : (T : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|))
    (hheight : ∀ t ∈ T, ∀ s ∈ T, |t-s| ≤ (u : ℝ)^10) :
    (∑ t ∈ T, ‖∑ n ∈ S, a n * logPhase t n‖^2) ≤
      (264*(B : ℝ)*(actualMass P z hP)⁻¹ +
        3200*(T.card : ℝ)*(z : ℝ)^4*(u : ℝ)^7) * (∑ n ∈ S, ‖a n‖^2) := by
  have hG : 0 ≤ actualMass P z hP := (mass_pos (reciprocalSieve P hP) hz).le
  have hp : 0 < B := hBpos
  have hsA : S ⊆ range (6*B+1) := by
    intro n hn
    have hh := mem_Icc.mp (hS hn)
    simp only [mem_range]
    omega
  have hh := sparse_majorant_duality S (range (6*B+1)) T a
    (triangleSieveMajorant (B) P z hP)
    (fun t n => logPhase t (max ((B : ℕ) : ℝ) n)) hsA
    (fun n _ => triangleSieveMajorant_nonneg _ _ _ _ hP)
    (fun n hn => triangleSieveMajorant_one hP hz hp (hS hn) (hcop n hn))
    (show 0 ≤ 264*(B : ℝ)*(actualMass P z hP)⁻¹ +
        3200*(T.card : ℝ)*(z : ℝ)^4*(u : ℝ)^7 by positivity)
    (fun t ht => sparse_rough_gram_row_at_scale T u B P z hP hu hBpos hBU hz hzB hsep hheight t ht)
  have he : ∀ t, (∑ n ∈ S, a n * logPhase t (max ((B : ℕ) : ℝ) n)) =
      ∑ n ∈ S, a n * logPhase t n := by
    intro t
    apply sum_congr rfl
    intro n hn
    have hh := (mem_Icc.mp (hS hn)).1
    have hnB : B ≤ n := by omega
    rw [max_eq_right (by exact_mod_cast hnB)]
  simpa only [he] using hh

theorem rough_card_bound_at_scale (S : Finset ℕ) (u B P z : ℕ) (hP : Squarefree P)
    (hu : 1 ≤ u) (hBpos : 0 < B) (hBU : B ≤ u^8) (hz : 1 ≤ z) (hzB : z^2 ≤ B)
    (hS : S ⊆ Icc (2*B) (4*B)) (hcop : ∀ n ∈ S, n.Coprime P) :
    (S.card : ℝ) ≤ 44*(B : ℝ)*(actualMass P z hP)⁻¹ +
      3200*(z : ℝ)^4*(u : ℝ)^7 := by
  have hp : 0 < B := hBpos
  have hsA : S ⊆ range (6*B+1) := by
    intro n hn
    have hh := mem_Icc.mp (hS hn)
    simp only [mem_range]
    omega
  have hmajor : (S.card : ℝ) ≤ ∑ n ∈ range (6*B+1), triangleSieveMajorant (B) P z hP n := by
    calc
      _ = ∑ n ∈ S, (1 : ℝ) := by simp
      _ ≤ ∑ n ∈ S, triangleSieveMajorant (B) P z hP n := sum_le_sum (fun n hn =>
        triangleSieveMajorant_one hP hz hp (hS hn) (hcop n hn))
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsA (fun n _ _ =>
        triangleSieveMajorant_nonneg _ _ _ _ hP)
  have he : ((∑ n ∈ range (6*B+1), triangleSieveMajorant (B) P z hP n : ℝ) : ℂ) =
      2*sieveTriangleKernel 0 (B) P z hP := by
    have hg := triangleSieveGram (B) P z hP 0 0
    simp only [sub_self] at hg
    rw [← hg]
    simp [weightedGram, logPhase]
  have hn : 0 ≤ ∑ n ∈ range (6*B+1), triangleSieveMajorant (B) P z hP n :=
    sum_nonneg (fun n _ => triangleSieveMajorant_nonneg _ _ _ _ hP)
  have hnorm := congrArg norm he
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn, norm_mul, Complex.norm_ofNat] at hnorm
  have hb := sieveTriangleKernel_norm_at_scale 0 u B P z hP hu hBpos hBU hz hzB (by simp)
  norm_num only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, add_zero,
    inv_one, mul_one] at hb
  rw [hnorm] at hmajor
  nlinarith

theorem rough_harmonic_energy_at_scale (S : Finset ℕ) (T : Finset ℝ) (a : ℕ → ℂ)
    (u B P z : ℕ) (hP : Squarefree P) (hu : 1 ≤ u) (hBpos : 0 < B) (hBU : B ≤ u^8) (hz : 1 ≤ z)
    (hzB : z^2 ≤ B) (hS : S ⊆ Icc (2*B) (4*B))
    (hcop : ∀ n ∈ S, n.Coprime P) (ha : ∀ n ∈ S, ‖a n‖ ≤ 1)
    (hsep : (T : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|))
    (hheight : ∀ t ∈ T, ∀ s ∈ T, |t-s| ≤ (u : ℝ)^10) :
    (∑ t ∈ T, ‖∑ n ∈ S, (a n/(n:ℂ)) * logPhase t n‖^2) ≤
      (264*(actualMass P z hP)⁻¹ + 3200*(T.card:ℝ)*(z:ℝ)^4*(u:ℝ)^7/B) *
      (44*(actualMass P z hP)⁻¹ + 3200*(z:ℝ)^4*(u:ℝ)^7/B)/4 := by
  have hBr : (0:ℝ) < B := by exact_mod_cast hBpos
  have hG : 0 ≤ actualMass P z hP := (mass_pos (reciprocalSieve P hP) hz).le
  have hc := rough_card_bound_at_scale S u B P z hP hu hBpos hBU hz hzB hS hcop
  have hb : (∑ n ∈ S, ‖a n/(n:ℂ)‖^2) ≤
      (44*(B:ℝ)*(actualMass P z hP)⁻¹ + 3200*(z:ℝ)^4*(u:ℝ)^7) / (4*(B:ℝ)^2) := by
    calc
      _ ≤ ∑ n ∈ S, (1/(2*(B:ℝ)))^2 := by
        apply sum_le_sum
        intro n hn
        apply pow_le_pow_left₀ (norm_nonneg _)
        rw [norm_div, Complex.norm_natCast]
        have hnlo : 2*(B:ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp (hS hn)).1
        exact div_le_div₀ (by norm_num) (ha n hn) (by positivity) hnlo
      _ = (S.card:ℝ)*(1/(4*(B:ℝ)^2)) := by
        simp only [sum_const, nsmul_eq_mul]
        congr 1
        ring
      _ ≤ _ := by
        simpa only [div_eq_mul_inv, one_mul, one_div] using
          mul_le_mul_of_nonneg_right hc (show 0 ≤ (4*(B:ℝ)^2)⁻¹ by positivity)
  have he := rough_mellin_energy_at_scale S T (fun n => a n/(n:ℂ)) u B P z hP hu hBpos hBU hz hzB hS hcop hsep hheight
  apply he.trans
  apply (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq
  field_simp

theorem signed_product_energy_at_scale (S : Finset ℕ) (T : Finset ℝ) (a : ℕ → ℂ)
    (C : ℝ → ℂ) (u B P z : ℕ) (hP : Squarefree P) (hu : 1 ≤ u) (hBpos : 0 < B) (hBU : B ≤ u^8) (hz : 1 ≤ z)
    (hzB : z^2 ≤ B) (hS : S ⊆ Icc (2*B) (4*B))
    (hcop : ∀ n ∈ S, n.Coprime P) (ha : ∀ n ∈ S, ‖a n‖ ≤ 1)
    (hsep : (T : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|))
    (hheight : ∀ t ∈ T, ∀ s ∈ T, |t-s| ≤ (u : ℝ)^10)
    {ε : ℝ} (hε : 0 ≤ ε) (hC : ∀ t ∈ T, ‖C t‖ ≤ ε) :
    (∑ t ∈ T, ‖C t * ∑ n ∈ S, (a n/(n:ℂ))*logPhase t n‖^2) ≤
      ε^2 * ((264*(actualMass P z hP)⁻¹ + 3200*(T.card:ℝ)*(z:ℝ)^4*(u:ℝ)^7/B) *
      (44*(actualMass P z hP)⁻¹ + 3200*(z:ℝ)^4*(u:ℝ)^7/B)/4) := by
  calc
    _ ≤ ∑ t ∈ T, ε^2 * ‖∑ n ∈ S, (a n/(n:ℂ))*logPhase t n‖^2 := by
      apply sum_le_sum
      intro t ht
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) hε).mpr (hC t ht)) (sq_nonneg _)
    _ = _ := by rw [← mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (rough_harmonic_energy_at_scale S T a u B P z hP hu hBpos hBU hz hzB hS hcop ha hsep hheight) (sq_nonneg ε)

end OrdinarySelbergWeights

end

end OAI
