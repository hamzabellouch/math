import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.LocalSampling
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.TupleProduct

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

namespace OrdinaryPrimeDirichletMoments
open OrdinaryMellinSampling OrdinaryDirichletMeanSquare Finset

lemma product_support_band (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    (k : ℕ) {c B : ℝ} (hband : ∀p∈P,|Real.log (p:ℝ)-c|≤B) :
    ∀n∈productSupport P k, |Real.log (n:ℝ)-(k:ℝ)*c|≤(k:ℝ)*B := by
  intro n hn
  obtain ⟨v,hv,rfl⟩ := mem_image.mp hn
  have he : Real.log ((tupleProduct v:ℕ):ℝ)-(k:ℝ)*c =
      ∑i : Fin k, (Real.log ((v i:ℕ):ℝ)-c) := by
    rw [tupleProduct, Nat.cast_prod,
      Real.log_prod (fun i hi => by exact_mod_cast (hP _ (v i).property).ne_zero)]
    simp
  rw [he]
  calc
    _ ≤ ∑i : Fin k, |Real.log ((v i:ℕ):ℝ)-c| := abs_sum_le_sum_abs _ _
    _ ≤ ∑_i : Fin k, B := sum_le_sum (fun i hi => hband _ (v i).property)
    _ = _ := by simp

theorem prime_spaced_high_moment (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    (a : ℕ → ℂ) (k : ℕ) (R : Finset ℝ) {Q T c B : ℝ}
    (hQ : 0<Q) (hT : 0≤T) (hB : 0≤B)
    (hPQ : ∀p∈P,(p:ℝ)≤Q) (hband : ∀p∈P,|Real.log (p:ℝ)-c|≤B)
    (hR : ∀t∈R,t∈Set.Icc (-T) T)
    (hsep : ∀t∈R,∀u∈R,t≠u → 1≤|t-u|) :
    ∑t∈R, ‖polynomial P a (fun p => Real.log p) t‖^(2*k) ≤
      4*Real.exp (1+1/4)*gaussianConstant*(T+1+Q^k)*(2+((k:ℝ)*B)^2)*
        (k.factorial:ℝ)*(∑p∈P,‖a p‖^2)^k := by
  have he (t : ℝ) : ‖polynomial P a (fun p => Real.log p) t‖^(2*k) =
      ‖polynomial (productSupport P k) (coefficient P k a) (fun n => Real.log n) t‖^2 := by
    rw [←polynomial_power P hP a k t, norm_pow, ←pow_mul]
    congr 1
    omega
  simp_rw [he]
  have hm := band_spaced_mean_square (productSupport P k) (coefficient P k a) R
    (pow_pos hQ k) hT (mul_nonneg (Nat.cast_nonneg k) hB)
    (product_support_bounds P hP k hQ hPQ) (product_support_band P hP k hband) hR hsep
  refine hm.trans ?_
  have hK : 0≤4*Real.exp (1+1/4)*gaussianConstant*(T+1+Q^k)*(2+((k:ℝ)*B)^2) := by
    unfold gaussianConstant
    positivity
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (coefficient_energy P hP a k) hK

theorem prime_large_values_card (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    (a : ℕ → ℂ) (k : ℕ) (R : Finset ℝ) {Q T c B V : ℝ}
    (hQ : 0<Q) (hT : 0≤T) (hB : 0≤B) (hV : 0<V)
    (hPQ : ∀p∈P,(p:ℝ)≤Q) (hband : ∀p∈P,|Real.log (p:ℝ)-c|≤B)
    (hR : ∀t∈R,t∈Set.Icc (-T) T)
    (hsep : ∀t∈R,∀u∈R,t≠u → 1≤|t-u|)
    (hlarge : ∀t∈R,V≤‖polynomial P a (fun p => Real.log p) t‖) :
    (R.card:ℝ) ≤
      (4*Real.exp (1+1/4)*gaussianConstant*(T+1+Q^k)*(2+((k:ℝ)*B)^2)*
        (k.factorial:ℝ)*(∑p∈P,‖a p‖^2)^k)/V^(2*k) := by
  apply (le_div_iff₀ (pow_pos hV (2*k))).mpr
  have hm := prime_spaced_high_moment P hP a k R hQ hT hB hPQ hband hR hsep
  apply le_trans _ hm
  calc
    _ = ∑_t∈R,V^(2*k) := by simp
    _ ≤ _ := sum_le_sum (fun t ht => pow_le_pow_left₀ hV.le (hlarge t ht) _)

end OrdinaryPrimeDirichletMoments

end

end OAI
