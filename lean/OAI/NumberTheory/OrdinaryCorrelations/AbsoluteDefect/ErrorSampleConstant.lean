import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BinQ
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BinErrorWidth
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SampledBudget

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

namespace OrdinaryChainScales
open OrdinaryCorrelations SourcePrimeFactor OrdinaryNarrowGrid OrdinaryDirichletMeanSquare Finset
attribute [local irreducible] E F mesh binQ binStart binWidth binLog amplifier

noncomputable def errorSampleConstant : ℝ :=
  4*Real.exp (1+1/4)*gaussianConstant*(2+(Real.log 6)^2)

lemma errorSampleConstant_nonneg : 0≤errorSampleConstant := by
  unfold errorSampleConstant gaussianConstant
  positivity

lemma sampled_stage_error_normalized {f : ℕ→ℂ} (hf : OneBounded f) (hm : Multiplicative f)
    {d : ℕ} (χ : DirichletCharacter ℂ d) (q r R X : ℕ) (hq : 0<q) (hX : 0<X)
    (hE : 2*binErrorWidth q r R X≤X) (S : Finset ℝ)
    (hsep : (S : Set ℝ).Pairwise (fun t u=>1≤|t-u|)) (hheight : ∀t∈S,|t|≤(X:ℝ)) :
    (∑t∈S,‖binnedStage f χ q r R X t-dyadicCharacterPolynomial f χ X t‖^2) ≤
      512*errorSampleConstant*(Real.exp (-(∑p∈primeWindow q r R,(p:ℝ)⁻¹))+
        (∑p∈primeWindow q r R,(p:ℝ)⁻¹^2)+(binErrorWidth q r R X:ℝ)/(X:ℝ)+
        (4*((q*2^(r+R):ℕ):ℝ))^8/(X:ℝ)) := by
  have hh := binnedStage_sampled_error hf hm χ q r R X hq hX hE S (Nat.cast_nonneg X)
    (fun t ht=>abs_le.mp (hheight t ht)) (fun t ht u hu hne=>hsep ht hu hne)
  have he : binErrorWidth q r R X≤X := by omega
  rw [Nat.cast_sub he] at hh
  have hs := OrdinaryBinnedErrorBudget.sampled_budget (a:=Real.exp (-(∑p∈primeWindow q r R,(p:ℝ)⁻¹))) errorSampleConstant_nonneg le_rfl
    (show (1:ℝ)≤X by exact_mod_cast hX) (Nat.cast_nonneg (binErrorWidth q r R X))
    (by exact_mod_cast hE : 2*(binErrorWidth q r R X:ℝ)≤(X:ℝ))
    (Real.exp_pos _).le (by positivity : 0≤∑p∈primeWindow q r R,(p:ℝ)⁻¹^2)
    (by positivity : 0≤(4*((q*2^(r+R):ℕ):ℝ))^8)
  apply hh.trans
  convert hs using 1; try rfl
  unfold errorSampleConstant
  ring

lemma prime_window_square_sum (q r R : ℕ) (hq : 0<q) :
    (∑p∈primeWindow q r R,(p:ℝ)⁻¹^2)≤1/((q*2^r:ℕ):ℝ) := by
  have hP : 0<q*2^r := Nat.mul_pos hq (by positivity)
  have he : q*2^r≤q*2^(r+R) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  calc
    _ ≤ ∑n∈Ioc (q*2^r) (q*2^(r+R)),((n:ℝ)^2)⁻¹ := by
      simp only [inv_pow]
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _=>by positivity)
    _ ≤ ((q*2^r:ℕ):ℝ)⁻¹-((q*2^(r+R):ℕ):ℝ)⁻¹ := sum_Ioc_inv_sq_le_sub hP.ne' he
    _ ≤ _ := by rw [one_div]; exact sub_le_self _ (by positivity)

lemma chain_mesh_large {B H s j : ℕ} (hB : H+s+20≤B) :
    s+j+3≤ mesh B H s j := by
  have hb : s+10≤B-H-10 := by omega
  have hh : s+j+3≤B-H-10+j^2+(s+19)*j := by nlinarith only [hb,Nat.zero_le (j^2),Nat.zero_le (s*j)]
  unfold mesh
  exact hh.trans (Nat.le_of_lt (Nat.lt_two_pow_self))

lemma chain_window_error_width {q Q X : ℕ} (hq : 8≤q) (hQ : 2≤Q) (hX : Q^16≤X) :
    2*(X/q+2*Q)≤X := by
  have h1 := Nat.div_mul_le_self X q
  have h2 : 16*Q≤Q^16 := by
    have hp : 16≤Q^15 := (by norm_num : (16:ℕ)≤2^15).trans (Nat.pow_le_pow_left hQ 15)
    have hh := Nat.mul_le_mul_right Q hp
    simpa only [pow_succ] using hh
  have h3 : 8*(X/q)≤X := by nlinarith only [h1,hq,Nat.zero_le (X/q)]
  omega

lemma actual_error_width {B H s j X : ℕ} (hB : H+s+20≤B)
    (hX : (2^(F B s j))^16≤X) :
    2*binErrorWidth (binQ B H s j) (binStart B H s j) (binWidth B s j) X≤X := by
  have hq : 8≤binQ B H s j := by
    unfold binQ
    exact_mod_cast Nat.pow_le_pow_right (by omega : 1≤(2:ℕ)) (show 3≤ mesh B H s j from (by have := chain_mesh_large (j:=j) hB; omega))
  have hQ : 2≤2^(F B s j) := by
    simpa using Nat.pow_le_pow_right (by omega : 1≤(2:ℕ)) (show 1≤F B s j from F_pos B s j)
  unfold binErrorWidth
  rw [(window_endpoints B H s j (by omega)).2]
  exact chain_window_error_width hq hQ hX

lemma rational_error_budget {q P Q X : ℝ} (hq : 0<q) (hqP : q≤P) (hPQ : P≤Q)
    (hQ : 1≤Q) (hX : Q^16≤X) {e : ℝ} (he : e≤X/q+2*Q) :
    1/P+e/X+(4*Q)^8/X≤65540/q := by
  have hQ0 : 0<Q := by linarith
  have hP0 : 0<P := hq.trans_le hqP
  have hX0 : 0<X := (pow_pos hQ0 16).trans_le hX
  have hqQ := hqP.trans hPQ
  have hp : 1/P≤1/q := one_div_le_one_div_of_le hq hqP
  have hQsq : Q^2≤Q^16 := pow_le_pow_right₀ hQ (by omega)
  have hxq : q*Q≤X := (mul_le_mul_of_nonneg_right hqQ hQ0.le).trans (by nlinarith only [hQsq,hX])
  have hqx : Q/X≤1/q := (div_le_div_iff₀ hX0 hq).mpr (by nlinarith only [hxq])
  have he' : e/X≤3/q := by
    calc
      _ ≤ (X/q+2*Q)/X := div_le_div_of_nonneg_right he hX0.le
      _ = 1/q+2*(Q/X) := by field_simp
      _ ≤ 1/q+2*(1/q) := by linarith only [hqx]
      _ = _ := by ring
  have h9 : Q^9≤Q^16 := pow_le_pow_right₀ hQ (by omega)
  have hc : (4*Q)^8/X≤65536/q := by
    apply (div_le_div_iff₀ hX0 hq).mpr
    have hh := mul_le_mul_of_nonneg_left hqQ (show 0≤Q^8 by positivity)
    rw [mul_pow]
    norm_num
    change Q^8*Q≤Q^16 at h9
    nlinarith only [hh,h9,hX]
  calc
    _ ≤ 1/q+3/q+65536/q := by linarith only [hp,he',hc]
    _ = _ := by ring

end OrdinaryChainScales

end

end OAI
