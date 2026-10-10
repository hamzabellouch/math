import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ProductSupportBand
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Collect
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DyadicCofactorMellinEqPolynomial

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
open MeasureTheory
open MeasureTheory Complex
open Finset Filter

namespace OrdinaryRestrictedCofactor
open Finset OrdinaryDirichletMeanSquare OrdinaryPrimeDirichletMoments
open OrdinaryDirichletFiberMoments SourcePrimeFactor

def badFrequencies (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : Finset ℕ) (R : Finset ℝ) (V : ℝ) : Finset ℝ := by
  classical
  exact R.filter (fun t => V < ‖primeMellin f χ P t‖)

def restrictedEnergy (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : Finset ℕ) (M : ℕ) (R : Finset ℝ) (V : ℝ) : ℝ :=
  ∑ t ∈ badFrequencies f χ P R V, ‖dyadicCofactorMellin f χ P M t‖^2

def powersAndCofactors (P : Finset ℕ) (k M : ℕ) : Finset ((Fin k → P) × ℕ) :=
  univ ×ˢ Ioc M (2*M)

def productLocation {P : Finset ℕ} {k : ℕ} (z : (Fin k → P) × ℕ) : ℕ :=
  tupleProduct z.1 * z.2

def productWeight (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : Finset ℕ) {k : ℕ} (z : (Fin k → P) × ℕ) : ℂ :=
  tupleCoefficient (fun p => characterModulation f χ p/(p:ℂ)) z.1 *
    OrdinaryCofactorDyadicBound.coefficient P (characterModulation f χ) z.2

def productCoefficient (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : Finset ℕ) (k M n : ℕ) : ℂ :=
  collect (powersAndCofactors P k M) productLocation (productWeight f χ P) n

lemma phase_log_mul {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (t : ℝ) :
    phase (Real.log (n*m:ℕ)) t = phase (Real.log n) t * phase (Real.log m) t := by
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hn.ne') (by exact_mod_cast hm.ne')]
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma tupleProduct_pos {P : Finset ℕ} (hP : ∀p∈P,Nat.Prime p) {k : ℕ}
    (v : Fin k → P) : 0<tupleProduct v := by
  unfold tupleProduct
  exact prod_pos fun i hi => (hP _ (v i).property).pos

lemma primeMellin_pow_expansion (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p) (k : ℕ) (t : ℝ) :
    primeMellin f χ P t ^ k =
      ∑ v : Fin k → P, tupleCoefficient
        (fun p => characterModulation f χ p/(p:ℂ)) v * phase (Real.log (tupleProduct v)) t := by
  unfold primeMellin polynomial
  rw [← Finset.sum_coe_sort P]
  rw [Fintype.sum_pow]
  apply sum_congr rfl
  intro v hv
  rw [prod_mul_distrib]
  rw [← tuple_phase hP v t]
  rfl

lemma actual_product_polynomial (f : ℕ → ℂ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    (k M : ℕ) (t : ℝ) :
    polynomial ((powersAndCofactors P k M).image productLocation)
      (productCoefficient f χ P k M) (fun n => Real.log n) t =
      primeMellin f χ P t ^ k * dyadicCofactorMellin f χ P M t := by
  unfold productCoefficient
  rw [collect_polynomial, primeMellin_pow_expansion f χ P hP,
    dyadicCofactorMellin_eq_polynomial]
  unfold powersAndCofactors polynomial
  rw [sum_product, sum_mul]
  apply sum_congr rfl
  intro v hv
  rw [mul_sum]
  apply sum_congr rfl
  intro m hm
  have hm0 : 0 < m := by have := (mem_Ioc.mp hm).1; omega
  rw [productLocation, phase_log_mul (tupleProduct_pos hP v) hm0]
  unfold productWeight
  ring

lemma actual_support_bounds (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    (k M : ℕ) {Q : ℝ} (hQ : 0 < Q) (hPQ : ∀p∈P,(p:ℝ)≤Q) :
    ∀n∈(powersAndCofactors P k M).image productLocation,
      0 < (n:ℝ) ∧ (n:ℝ) ≤ Q^k*(2*M:ℝ) := by
  intro n hn
  obtain ⟨⟨v,m⟩, hvm, rfl⟩ := mem_image.mp hn
  have hm := (mem_product.mp hvm).2
  have hp := product_support_bounds P hP k hQ hPQ (tupleProduct v)
    (mem_image.mpr ⟨v, mem_univ _, rfl⟩)
  have hm0 : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by have := (mem_Ioc.mp hm).1; omega)
  have hmle : (m:ℝ) ≤ (2*M:ℝ) := by exact_mod_cast (mem_Ioc.mp hm).2
  change 0 < ((tupleProduct v * m:ℕ):ℝ) ∧ ((tupleProduct v * m:ℕ):ℝ) ≤ _
  rw [Nat.cast_mul]
  exact ⟨mul_pos hp.1 hm0, mul_le_mul hp.2 hmle hm0.le (pow_nonneg hQ.le _)⟩

lemma dyadic_log_band {M : ℕ} (hM : 0 < M) :
    ∀n∈Finset.Ioc M (2*M), |Real.log (n:ℝ)-Real.log (M:ℝ)|≤Real.log 2 := by
  intro n hn
  have hn' := Finset.mem_Ioc.mp hn
  have hM' : (0:ℝ)<M := by exact_mod_cast hM
  have hnpos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hmn : (M:ℝ)≤n := by exact_mod_cast hn'.1.le
  have hnM : (n:ℝ)≤2*(M:ℝ) := by exact_mod_cast hn'.2
  have hlower := Real.log_le_log hM' hmn
  have hupper := Real.log_le_log hnpos hnM
  rw [Real.log_mul (by norm_num) hM'.ne'] at hupper
  rw [abs_of_nonneg (sub_nonneg.mpr hlower)]
  linarith

lemma actual_support_band (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    (k : ℕ) {M : ℕ} (hM : 0 < M) {c B : ℝ}
    (hband : ∀p∈P, |Real.log (p:ℝ)-c| ≤ B) :
    ∀n∈(powersAndCofactors P k M).image productLocation,
      |Real.log (n:ℝ)-((k:ℝ)*c+Real.log M)| ≤ (k:ℝ)*B+Real.log 2 := by
  intro n hn
  obtain ⟨⟨v,m⟩, hvm, rfl⟩ := mem_image.mp hn
  have hm := (mem_product.mp hvm).2
  have hp := product_support_band P hP k hband (tupleProduct v)
    (mem_image.mpr ⟨v, mem_univ _, rfl⟩)
  have hmlog := dyadic_log_band hM m hm
  have hm0 : 0 < m := by have := (mem_Ioc.mp hm).1; omega
  change |Real.log ((tupleProduct v * m:ℕ):ℝ)-_| ≤ _
  rw [Nat.cast_mul, Real.log_mul
    (by exact_mod_cast (tupleProduct_pos hP v).ne') (by exact_mod_cast hm0.ne')]
  calc
    _ = |(Real.log (tupleProduct v:ℝ)-(k:ℝ)*c)+(Real.log (m:ℝ)-Real.log M)| := by congr 1; ring
    _ ≤ |Real.log (tupleProduct v:ℝ)-(k:ℝ)*c|+|Real.log (m:ℝ)-Real.log M| := abs_add_le _ _
    _ ≤ _ := add_le_add hp hmlog

def collectedEnergy (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : Finset ℕ) (k M : ℕ) : ℝ :=
  ∑ n ∈ (powersAndCofactors P k M).image productLocation,
    ‖productCoefficient f χ P k M n‖^2

theorem actual_mixed_spaced_energy (f : ℕ → ℂ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    (k : ℕ) {M : ℕ} (hM : 0 < M) (R : Finset ℝ) {Q T c B : ℝ}
    (hQ : 0 < Q) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hPQ : ∀p∈P,(p:ℝ)≤Q) (hband : ∀p∈P, |Real.log (p:ℝ)-c|≤B)
    (hR : ∀t∈R,t∈Set.Icc (-T) T)
    (hsep : ∀t∈R,∀u∈R,t≠u → 1≤|t-u|) :
    ∑ t ∈ R, ‖primeMellin f χ P t‖^(2*k) * ‖dyadicCofactorMellin f χ P M t‖^2 ≤
      4*Real.exp (1+1/4)*gaussianConstant*(T+1+Q^k*(2*M:ℝ))*
        (2+((k:ℝ)*B+Real.log 2)^2)*collectedEnergy f χ P k M := by
  have he (t : ℝ) :
      ‖polynomial ((powersAndCofactors P k M).image productLocation)
        (productCoefficient f χ P k M) (fun n => Real.log n) t‖^2 =
        ‖primeMellin f χ P t‖^(2*k) * ‖dyadicCofactorMellin f χ P M t‖^2 := by
    rw [actual_product_polynomial f χ P hP, norm_mul, mul_pow, norm_pow, ← pow_mul]
    congr 2
    omega
  simp_rw [← he]
  apply OrdinaryMellinSampling.band_spaced_mean_square _ _ R
    (mul_pos (pow_pos hQ k) (by exact_mod_cast (show 0<2*M by omega))) hT
    (add_nonneg (mul_nonneg (Nat.cast_nonneg k) hB) (Real.log_nonneg (by norm_num)))
    (actual_support_bounds P hP k M hQ hPQ)
    (actual_support_band P hP k hM hband) hR hsep

theorem actual_restricted_cofactor_energy (f : ℕ → ℂ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    (k : ℕ) {M : ℕ} (hM : 0 < M) (R : Finset ℝ) {Q T c B V : ℝ}
    (hQ : 0 < Q) (hT : 0 ≤ T) (hB : 0 ≤ B) (hV : 0 < V)
    (hPQ : ∀p∈P,(p:ℝ)≤Q) (hband : ∀p∈P, |Real.log (p:ℝ)-c|≤B)
    (hR : ∀t∈R,t∈Set.Icc (-T) T)
    (hsep : ∀t∈R,∀u∈R,t≠u → 1≤|t-u|) :
    restrictedEnergy f χ P M R V ≤
      (4*Real.exp (1+1/4)*gaussianConstant*(T+1+Q^k*(2*M:ℝ))*
        (2+((k:ℝ)*B+Real.log 2)^2)*collectedEnergy f χ P k M) / V^(2*k) := by
  classical
  apply (le_div_iff₀ (pow_pos hV _)).mpr
  unfold restrictedEnergy
  rw [sum_mul]
  calc
    _ ≤ ∑ t ∈ badFrequencies f χ P R V,
        ‖primeMellin f χ P t‖^(2*k) * ‖dyadicCofactorMellin f χ P M t‖^2 := by
      apply sum_le_sum
      intro t ht
      have hv : V ≤ ‖primeMellin f χ P t‖ := (mem_filter.mp ht).2.le
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hV.le hv (2*k)) (sq_nonneg ‖dyadicCofactorMellin f χ P M t‖)
    _ ≤ ∑ t ∈ R,
        ‖primeMellin f χ P t‖^(2*k) * ‖dyadicCofactorMellin f χ P M t‖^2 := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro t ht hnot
      positivity
    _ ≤ _ := actual_mixed_spaced_energy f χ P hP k hM R hQ hT hB hPQ hband hR hsep

end OrdinaryRestrictedCofactor

end

end OAI
