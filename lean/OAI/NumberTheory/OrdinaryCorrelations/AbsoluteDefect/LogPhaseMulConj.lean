import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SieveTriangleKernel
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.NatKernelSum
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.FiniteSchur

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace OrdinarySelbergWeights
open Finset OrdinaryLogIntegral OrdinarySparseSieve

lemma logPhase_mul_conj (t s x : ℝ) :
    logPhase t x * star (logPhase s x) = logPhase (t-s) x := by
  simp only [logPhase, Complex.star_def, ← Complex.exp_conj, map_mul,
    Complex.conj_I, Complex.conj_ofReal, ← Complex.exp_add]
  congr 1
  push_cast
  ring

noncomputable def triangleSieveMajorant (B P z : ℕ) (hP : Squarefree P) (n : ℕ) : ℝ :=
  2 * tent B (2*B) n * sieveWeight P z hP n

lemma triangleSieveMajorant_nonneg (B P z n : ℕ) (hP : Squarefree P) :
    0 ≤ triangleSieveMajorant B P z hP n := by
  exact mul_nonneg (mul_nonneg (by norm_num) (tent_nonneg _ _ _)) (sieveWeight_nonneg hP)

lemma triangleSieveMajorant_one {B P z n : ℕ} (hP : Squarefree P) (hz : 1 ≤ z)
    (hB : 0 < B) (hn : n ∈ Icc (2*B) (4*B)) (hcop : n.Coprime P) :
    1 ≤ triangleSieveMajorant B P z hP n := by
  rw [triangleSieveMajorant, sieveWeight_eq_one_of_coprime hP hz hcop, mul_one]
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hlo : (2 : ℝ)*B ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
  have hhi : (n : ℝ) ≤ 4*B := by exact_mod_cast (mem_Icc.mp hn).2
  have hab : |(n : ℝ)-((B : ℝ)+2*B)| ≤ B := abs_le.mpr ⟨by linarith, by linarith⟩
  have hh : |(n : ℝ)-((B : ℝ)+2*B)|/(2*B) ≤ 1/2 :=
    (div_le_iff₀ (by positivity)).mpr (by linarith)
  have he := le_max_right 0 (1-|(n : ℝ)-((B : ℝ)+2*B)|/(2*B))
  change 1 ≤ 2*max 0 (1-|(n : ℝ)-((B : ℝ)+2*B)|/(2*B))
  linarith

lemma triangleSieveGram (B P z : ℕ) (hP : Squarefree P) (t s : ℝ) :
    weightedGram (range (6*B+1)) (triangleSieveMajorant B P z hP)
      (fun t n => logPhase t (max (B : ℝ) n)) t s =
      2 * sieveTriangleKernel (t-s) B P z hP := by
  unfold weightedGram sieveTriangleKernel
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  rw [triangleSieveMajorant, tentPhase]
  push_cast
  rw [show (2*(tent B (2*B) n : ℂ)*(sieveWeight P z hP n : ℂ))*logPhase t (max (B : ℝ) n)*
      star (logPhase s (max (B : ℝ) n)) =
      2*(sieveWeight P z hP n : ℂ)*(tent B (2*B) n : ℂ)*
        (logPhase t (max (B : ℝ) n)*star (logPhase s (max (B : ℝ) n))) by ring,
    logPhase_mul_conj]
  ring

lemma sieveTriangleKernel_norm (t : ℝ) (u P z : ℕ) (hP : Squarefree P)
    (hu : 1 ≤ u) (hz : 1 ≤ z) (hzB : z^2 ≤ u^8) (ht : |t| ≤ (u : ℝ)^10) :
    ‖sieveTriangleKernel t (u^8) P z hP‖ ≤
      (22*(u : ℝ)^8*(actualMass P z hP)⁻¹)*(1+t^2)⁻¹ + (z : ℝ)^4*(1600*(u : ℝ)^7) := by
  have hG : 0 ≤ actualMass P z hP := (mass_pos (reciprocalSieve P hP) hz).le
  have hh := norm_le_norm_sub_add (sieveTriangleKernel t (u^8) P z hP)
    (((actualMass P z hP)⁻¹ : ℝ) • triangleMain t (u^8))
  have hm := triangleMain_bound t (u^8) (pow_pos (by omega) _)
  have he := sieveTriangleKernel_error t u P z hP hu hz hzB ht
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hG)] at hh
  have hx := mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hG)
  push_cast at hx
  calc
    _ ≤ _ := hh.trans (add_le_add he hx)
    _ = _ := by ring

theorem sparse_rough_gram_row (T : Finset ℝ) (u P z : ℕ) (hP : Squarefree P)
    (hu : 1 ≤ u) (hz : 1 ≤ z) (hzB : z^2 ≤ u^8)
    (hsep : (T : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|))
    (hheight : ∀ t ∈ T, ∀ s ∈ T, |t-s| ≤ (u : ℝ)^10) (t : ℝ) (ht : t ∈ T) :
    (∑ s ∈ T, ‖weightedGram (range (6*u^8+1)) (triangleSieveMajorant (u^8) P z hP)
      (fun t n => logPhase t (max ((u^8 : ℕ) : ℝ) n)) t s‖) ≤
      264*(u : ℝ)^8*(actualMass P z hP)⁻¹ +
        3200*(T.card : ℝ)*(z : ℝ)^4*(u : ℝ)^7 := by
  have hG : 0 ≤ actualMass P z hP := (mass_pos (reciprocalSieve P hP) hz).le
  calc
    _ = ∑ s ∈ T, 2*‖sieveTriangleKernel (t-s) (u^8) P z hP‖ := by
      simp only [triangleSieveGram, norm_mul, Complex.norm_ofNat]
    _ ≤ ∑ s ∈ T, 2*((22*(u : ℝ)^8*(actualMass P z hP)⁻¹)*(1+(t-s)^2)⁻¹ +
        (z : ℝ)^4*(1600*(u : ℝ)^7)) := by
      apply sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left (sieveTriangleKernel_norm (t-s) u P z hP hu hz hzB
        (hheight t ht s hs)) (by norm_num)
    _ = 44*(u : ℝ)^8*(actualMass P z hP)⁻¹ * (∑ s ∈ T, (1+(s-t)^2)⁻¹) +
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
        (show 0 ≤ 44*(u : ℝ)^8*(actualMass P z hP)⁻¹ by positivity)
      nlinarith

end OrdinarySelbergWeights

end

end OAI
