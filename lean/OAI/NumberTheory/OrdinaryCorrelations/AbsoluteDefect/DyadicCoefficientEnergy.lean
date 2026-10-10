import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ProductSupportBand
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SparseCardOfMoment

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

namespace OrdinarySparseLargeValues
open Finset OrdinaryDirichletMeanSquare OrdinaryPrimeDirichletMoments

lemma dyadic_coefficient_energy {N : ℕ} (hN : 0 < N) (P : Finset ℕ)
    (hband : P ⊆ Ioc N (2*N)) (a : ℕ → ℂ)
    (ha : ∀ p∈P, ‖a p‖ ≤ (p:ℝ)⁻¹) :
    ∑ p∈P, ‖a p‖^2 ≤ (N:ℝ)⁻¹ := by
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hN
  have hcard : P.card ≤ N := by
    have hh := Finset.card_le_card hband
    simp only [Nat.card_Ioc] at hh
    omega
  calc
    _ ≤ ∑ _p∈P, ((N:ℝ)⁻¹)^2 := by
      apply sum_le_sum
      intro p hp
      have hpn : (N:ℝ) ≤ p := by exact_mod_cast (mem_Ioc.mp (hband hp)).1.le
      exact pow_le_pow_left₀ (norm_nonneg _) ((ha p hp).trans (inv_anti₀ hNr hpn)) 2
    _ = (P.card:ℝ)*((N:ℝ)⁻¹)^2 := by simp
    _ ≤ (N:ℝ)*((N:ℝ)⁻¹)^2 := by gcongr
    _ = (N:ℝ)⁻¹ := by field_simp

lemma dyadic_prime_band {N : ℕ} (hN : 0 < N) (P : Finset ℕ)
    (hband : P ⊆ Ioc N (2*N)) :
    ∀ p∈P, |Real.log (p:ℝ)-Real.log (N:ℝ)| ≤ 1 := by
  intro p hp
  have hmem := mem_Ioc.mp (hband hp)
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hN
  have hpn : (N:ℝ) ≤ p := by exact_mod_cast hmem.1.le
  have hpp : 0 < (p:ℝ) := hNr.trans_le hpn
  have hl := Real.log_le_log hNr hpn
  have hu := Real.log_le_log hpp (show (p:ℝ) ≤ 2*(N:ℝ) by exact_mod_cast hmem.2)
  rw [Real.log_mul (by norm_num) hNr.ne'] at hu
  rw [abs_of_nonneg (by linarith)]
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  linarith

def momentBase (k : ℕ) : ℝ :=
  1 + 12*Real.exp (1+1/4)*gaussianConstant*(2+(k:ℝ)^2)*(k.factorial:ℝ)

lemma momentBase_one_le (k : ℕ) : 1 ≤ momentBase k := by
  unfold momentBase
  have hh : 0 ≤ 12*Real.exp (1+1/4)*gaussianConstant*(2+(k:ℝ)^2)*(k.factorial:ℝ) := by
    unfold gaussianConstant
    positivity
  linarith

lemma dyadic_prime_large_values {H V : ℝ} {N k : ℕ}
    (hN : 0 < N) (hH : 1 ≤ H) (hV : 0 < V) (hk : 0 < k)
    (hscale : (2*(N:ℝ))^k ≤ H)
    (P : Finset ℕ) (hP : ∀ p∈P, Nat.Prime p) (hband : P ⊆ Ioc N (2*N))
    (a : ℕ → ℂ) (ha : ∀ p∈P, ‖a p‖ ≤ (p:ℝ)⁻¹)
    (T : Finset ℝ) (hT : ∀ t∈T, |t| ≤ H)
    (hsep : (T : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|))
    (hlarge : ∀ t∈T, V ≤ ‖polynomial P a (fun p => Real.log p) t‖) :
    (T.card:ℝ) ≤ H*(momentBase k/(N:ℝ))^k/V^(2*k) := by
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hN
  have hQ : 0 < 2*(N:ℝ) := by positivity
  have hpos : 0 ≤ 4*Real.exp (1+1/4)*gaussianConstant := by unfold gaussianConstant; positivity
  have hh := prime_large_values_card P hP a k T hQ (by linarith : 0 ≤ H)
    (by norm_num : (0:ℝ) ≤ 1) hV
    (fun p hp => by exact_mod_cast (mem_Ioc.mp (hband hp)).2)
    (dyadic_prime_band hN P hband)
    (fun t ht => abs_le.mp (hT t ht))
    (fun t ht u hu htu => hsep ht hu htu) hlarge
  simp only [mul_one] at hh
  apply hh.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have henergy := dyadic_coefficient_energy hN P hband a ha
  have hsmall : (∑ p∈P, ‖a p‖^2)^k ≤ ((N:ℝ)⁻¹)^k :=
    pow_le_pow_left₀ (sum_nonneg (fun p hp => sq_nonneg _)) henergy k
  have hlength : H+1+(2*(N:ℝ))^k ≤ 3*H := by linarith
  have hconstant :
      12*Real.exp (1+1/4)*gaussianConstant*(2+(k:ℝ)^2)*(k.factorial:ℝ) ≤
      (momentBase k)^k := by
    apply (show _ ≤ momentBase k by unfold momentBase; linarith).trans
    exact le_self_pow₀ (momentBase_one_le k) (by omega)
  calc
    _ ≤ 4*Real.exp (1+1/4)*gaussianConstant*(3*H)*(2+(k:ℝ)^2)*
        (k.factorial:ℝ)*((N:ℝ)⁻¹)^k := by gcongr
    _ = H*(12*Real.exp (1+1/4)*gaussianConstant*(2+(k:ℝ)^2)*(k.factorial:ℝ))*
        ((N:ℝ)⁻¹)^k := by ring
    _ ≤ H*(momentBase k)^k*((N:ℝ)⁻¹)^k := by gcongr
    _ = H*(momentBase k/(N:ℝ))^k := by rw [div_eq_mul_inv,mul_pow]; ring

theorem dyadic_prime_large_values_sparse {H V : ℝ} {N r k : ℕ}
    (hN : 2 ≤ N) (hH : 1 ≤ H) (hV : 0 < V) (hr : 0 < r) (hk : 4*r ≤ k)
    (hlower : (2*(N:ℝ))^k ≤ H) (hupper : H ≤ (2*(N:ℝ))^(k+1))
    (hsize : (2*momentBase k)^(8*r) ≤ (N:ℝ))
    (hthreshold : 1 ≤ (N:ℝ)*V^(8*r))
    (P : Finset ℕ) (hP : ∀ p∈P, Nat.Prime p) (hband : P ⊆ Ioc N (2*N))
    (a : ℕ → ℂ) (ha : ∀ p∈P, ‖a p‖ ≤ (p:ℝ)⁻¹)
    (T : Finset ℝ) (hT : ∀ t∈T, |t| ≤ H)
    (hsep : (T : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|))
    (hlarge : ∀ t∈T, V ≤ ‖polynomial P a (fun p => Real.log p) t‖) :
    (T.card:ℝ)^r ≤ H := by
  apply sparse_card_of_moment (Nat.cast_nonneg _) hH (by exact_mod_cast hN)
    (momentBase_one_le k) hV hr hk
    (dyadic_prime_large_values (by omega) hH hV (by omega) hlower P hP hband a ha T hT hsep hlarge)
    hupper hsize hthreshold

end OrdinarySparseLargeValues

end

end OAI
