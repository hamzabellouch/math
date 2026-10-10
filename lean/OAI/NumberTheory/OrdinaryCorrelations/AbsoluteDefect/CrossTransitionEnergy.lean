import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ModulationNormLeOne

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

namespace OrdinaryTwoScaleCofactor
open Finset OrdinaryDirichletMeanSquare SourcePrimeFactor

def crossTransitionEnergy (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (A B P : Finset ℕ) (M : ℕ) (R : Finset ℝ) (V W : ℝ) : ℝ :=
  ∑ t ∈ transitionFrequencies f χ A B R V W,
    ‖primeMellin f χ B t‖^2 * ‖dyadicCofactorMellin f χ P M t‖^2

lemma cross_transition_amplification (f : ℕ → ℂ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (A B P : Finset ℕ) (k M : ℕ)
    (R : Finset ℝ) {V W : ℝ} (hV : 0 < V) (_hW : 0 ≤ W) :
    crossTransitionEnergy f χ A B P M R V W ≤
      (W^2/V^(2*k))*(∑ t∈R,
        ‖primeMellin f χ A t‖^(2*k)*‖dyadicCofactorMellin f χ P M t‖^2) := by
  classical
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (pow_pos hV _)).mpr
  unfold crossTransitionEnergy
  rw [sum_mul,mul_sum]
  calc
    _ ≤ ∑t∈transitionFrequencies f χ A B R V W,
        W^2*(‖primeMellin f χ A t‖^(2*k)*‖dyadicCofactorMellin f χ P M t‖^2) := by
      apply sum_le_sum
      intro t ht
      have ht' := (mem_filter.mp ht).2
      have h1 := pow_le_pow_left₀ hV.le ht'.1.le (2*k)
      have h2 := pow_le_pow_left₀ (norm_nonneg _) ht'.2 2
      have h3 := mul_le_mul h2 h1 (pow_nonneg hV.le _) (sq_nonneg W)
      have h4 := mul_le_mul_of_nonneg_right h3
        (sq_nonneg ‖dyadicCofactorMellin f χ P M t‖)
      nlinarith only [h4]
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro t ht hnot
      positivity

lemma cross_transition_bound (f : ℕ → ℂ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (A B P : Finset ℕ) (hA : ∀p∈A,Nat.Prime p)
    (k : ℕ) {M : ℕ} (hM : 0 < M) (R : Finset ℝ) {Q T c b V W : ℝ}
    (hQ : 0 < Q) (hT : 0 ≤ T) (hb : 0 ≤ b) (hV : 0 < V) (hW : 0 ≤ W)
    (hAQ : ∀p∈A,(p:ℝ)≤Q) (hband : ∀p∈A,|Real.log (p:ℝ)-c|≤b)
    (hR : ∀t∈R,t∈Set.Icc (-T) T)
    (hsep : ∀t∈R,∀u∈R,t≠u → 1≤|t-u|) :
    crossTransitionEnergy f χ A B P M R V W ≤
      (W^2/V^(2*k))*
      (4*Real.exp (1+1/4)*gaussianConstant*(T+1+Q^k*(2*M:ℝ))*
        (2+((k:ℝ)*b+Real.log 2)^2)*mixedEnergy f χ A P k M) := by
  exact (cross_transition_amplification f χ A B P k M R hV hW).trans
    (mul_le_mul_of_nonneg_left
      (mixed_spaced_energy f χ A P hA k hM R hQ hT hb hAQ hband hR hsep)
      (by positivity))

lemma dyadic_inverse_mass {N : ℕ} (hN : 0 < N) (A : Finset ℕ)
    (hA : A ⊆ Ioc N (2*N)) : (∑p∈A,(p:ℝ)⁻¹) ≤ 1 := by
  have hNp : 0 < (N:ℝ) := by exact_mod_cast hN
  have hcard : A.card ≤ N := by
    have hh := Finset.card_le_card hA
    simp only [Nat.card_Ioc] at hh
    omega
  calc
    _ ≤ ∑_p∈A,(N:ℝ)⁻¹ := by
      apply sum_le_sum
      intro p hp
      exact inv_anti₀ hNp (by exact_mod_cast (mem_Ioc.mp (hA hp)).1.le)
    _ = (A.card:ℝ)*(N:ℝ)⁻¹ := by simp
    _ ≤ (N:ℝ)*(N:ℝ)⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ hNp.ne'

lemma dyadic_inverse_squared_mass {N : ℕ} (hN : 0 < N) (A : Finset ℕ)
    (hA : A ⊆ Ioc N (2*N)) : (∑p∈A,((p:ℝ)⁻¹)^2) ≤ (N:ℝ)⁻¹ := by
  have hNp : 0 < (N:ℝ) := by exact_mod_cast hN
  calc
    _ ≤ ∑p∈A,(N:ℝ)⁻¹*(p:ℝ)⁻¹ := by
      apply sum_le_sum
      intro p hp
      rw [pow_two]
      apply mul_le_mul_of_nonneg_right
        (inv_anti₀ hNp (by exact_mod_cast (mem_Ioc.mp (hA hp)).1.le))
        (by positivity)
    _ = (N:ℝ)⁻¹*(∑p∈A,(p:ℝ)⁻¹) := by rw [mul_sum]
    _ ≤ (N:ℝ)⁻¹*1 := mul_le_mul_of_nonneg_left (dyadic_inverse_mass hN A hA) (by positivity)
    _ = (N:ℝ)⁻¹ := by ring

lemma dyadic_mixed_energy {f : ℕ → ℂ} (hf : ∀n,‖f n‖≤1)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A P : Finset ℕ)
    (hA : ∀p∈A,Nat.Prime p) (k : ℕ) {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hband : A ⊆ Ioc N (2*N)) :
    mixedEnergy f χ A P k M ≤
      (2/(M:ℝ))*((N:ℝ)⁻¹)^k*(k.factorial:ℝ)*Real.exp ((k:ℝ)+Real.exp 1-1) := by
  have hh := mixedEnergy_explicit hf χ A P hA k hM (by norm_num : (0:ℝ) < 1)
  simp only [one_mul,one_pow,div_one] at hh
  apply hh.trans
  have he : 0 ≤ Real.exp 1-1 := by have := Real.one_le_exp_iff.mpr (by norm_num : (0:ℝ) ≤ 1); linarith
  have harg : (k:ℝ)+(Real.exp 1-1)*(∑p∈A,(p:ℝ)⁻¹) ≤ (k:ℝ)+Real.exp 1-1 := by
    have hh := mul_le_mul_of_nonneg_left (dyadic_inverse_mass hN A hband) he
    linarith
  gcongr
  exact dyadic_inverse_squared_mass hN A hband

theorem dyadic_cross_transition {f : ℕ → ℂ} (hf : ∀n,‖f n‖≤1)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A B P : Finset ℕ)
    (hA : ∀p∈A,Nat.Prime p) (k : ℕ) {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hband : A ⊆ Ioc N (2*N)) (R : Finset ℝ) {T V W : ℝ}
    (hT : 0 ≤ T) (hV : 0 < V) (hW : 0 ≤ W)
    (hheight : T+1 ≤ (2*(N:ℝ))^k*(M:ℝ))
    (hR : ∀t∈R,t∈Set.Icc (-T) T)
    (hsep : ∀t∈R,∀u∈R,t≠u → 1≤|t-u|) :
    crossTransitionEnergy f χ A B P M R V W ≤
      (W^2/V^(2*k))*(24*Real.exp (1+1/4)*gaussianConstant*
        (2+((k:ℝ)+Real.log 2)^2)*(2:ℝ)^k*(k.factorial:ℝ)*
        Real.exp ((k:ℝ)+Real.exp 1-1)) := by
  have hNp : 0 < (N:ℝ) := by exact_mod_cast hN
  have hMp : 0 < (M:ℝ) := by exact_mod_cast hM
  have hb : ∀p∈A,|Real.log (p:ℝ)-Real.log (N:ℝ)|≤(1:ℝ) := by
    intro p hp
    have hpn : (N:ℝ) ≤ p := by exact_mod_cast (mem_Ioc.mp (hband hp)).1.le
    have hl := Real.log_le_log hNp hpn
    have hu := Real.log_le_log (hNp.trans_le hpn)
      (show (p:ℝ) ≤ 2*(N:ℝ) by exact_mod_cast (mem_Ioc.mp (hband hp)).2)
    rw [Real.log_mul (by norm_num) hNp.ne'] at hu
    rw [abs_of_nonneg (by linarith)]
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hh := cross_transition_bound f χ A B P hA k hM R
    (by positivity : 0 < 2*(N:ℝ)) hT (by norm_num : (0:ℝ) ≤ 1) hV hW
    (fun p hp => by exact_mod_cast (mem_Ioc.mp (hband hp)).2) hb hR hsep
  simp only [mul_one] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hlen : T+1+(2*(N:ℝ))^k*(2*M:ℝ) ≤ 3*(2*(N:ℝ))^k*(M:ℝ) := by nlinarith only [hheight]
  have henergy := dyadic_mixed_energy hf χ A P hA k hN hM hband
  have hK : 0 ≤ 4*Real.exp (1+1/4)*gaussianConstant := by unfold gaussianConstant; positivity
  calc
    _ ≤ 4*Real.exp (1+1/4)*gaussianConstant*(3*(2*(N:ℝ))^k*(M:ℝ))*
        (2+((k:ℝ)+Real.log 2)^2)*
        ((2/(M:ℝ))*((N:ℝ)⁻¹)^k*(k.factorial:ℝ)*Real.exp ((k:ℝ)+Real.exp 1-1)) := by
      gcongr
      exact mixedEnergy_nonneg f χ A P k M
    _ = _ := by
      rw [mul_pow,inv_pow]
      field_simp
      ring

end OrdinaryTwoScaleCofactor

end

end OAI
