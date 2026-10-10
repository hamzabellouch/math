import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ActualWindowMass
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ErrorSampleConstant

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

lemma inverse_binQ_geometric {B H s j : ℕ} (hB : H+s+20≤B) :
    1/(binQ B H s j:ℝ)≤(1/2:ℝ)^(s+j) := by
  have hh : s+j≤ mesh B H s j := by have := chain_mesh_large (j:=j) hB; omega
  have hpow : (2:ℝ)^(s+j)≤(binQ B H s j:ℝ) := by
    unfold binQ
    exact_mod_cast Nat.pow_le_pow_right (by omega : 1≤(2:ℕ)) hh
  have he : (1/2:ℝ)^(s+j)=1/(2:ℝ)^(s+j) := by rw [div_pow,one_pow]
  rw [he]
  exact one_div_le_one_div_of_le (by positivity) hpow

lemma exponential_mass_geometric {C M : ℝ} {n : ℕ}
    (hM : |M-(n:ℝ)*Real.log 2|≤C) :
    Real.exp (-M)≤Real.exp C*(1/2:ℝ)^n := by
  have hh : -M≤C-(n:ℝ)*Real.log 2 := by have := (abs_le.mp hM).1; linarith
  apply (Real.exp_le_exp.mpr hh).trans_eq
  rw [Real.exp_sub,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2),div_pow,one_pow]
  ring

noncomputable def actualErrorConstant (C : ℝ) : ℝ :=
  512*errorSampleConstant*(Real.exp C+65540)

theorem actual_stage_error :
    ∃C : ℝ,0≤C ∧ ∀ (f : ℕ→ℂ),OneBounded f → Multiplicative f →
      ∀{d : ℕ}(χ : DirichletCharacter ℂ d)(B H s j X : ℕ), H+s+20≤B →
        (2^(F B s j))^16≤X →
        ∀S : Finset ℝ,(S : Set ℝ).Pairwise (fun t u=>1≤|t-u|) →
          (∀t∈S,|t|≤(X:ℝ)) →
          (∑t∈S,‖binnedStage f χ (binQ B H s j) (binStart B H s j) (binWidth B s j) X t-
            dyadicCharacterPolynomial f χ X t‖^2)≤C*(1/2:ℝ)^(s+j) := by
  classical
  obtain ⟨C,hC,hMass⟩ := actual_window_mass
  refine ⟨actualErrorConstant C,?_,?_⟩
  · unfold actualErrorConstant
    exact mul_nonneg (mul_nonneg (by norm_num) errorSampleConstant_nonneg) (by positivity)
  intro f hf hm d χ B H s j X hB hX S hsep hheight
  have hB0 : H+10≤B := by omega
  have hq : 0<binQ B H s j := by unfold binQ; positivity
  have hXp : 0<X := (by positivity : 0<(2^(F B s j))^16).trans_le hX
  have hnorm := sampled_stage_error_normalized hf hm χ _ _ _ X hq hXp (actual_error_width hB hX) S hsep hheight
  have hmass := exponential_mass_geometric (hMass B H s j hB0)
  have hsquare := prime_window_square_sum (binQ B H s j) (binStart B H s j) (binWidth B s j) hq
  rw [(window_endpoints B H s j hB0).1] at hsquare
  have hqP : (binQ B H s j:ℝ)≤(2^(E B s j):ℕ) := by
    have hh := mesh_le_E B H s j hB0
    have hh' : binQ B H s j≤2^(E B s j) := by unfold binQ; exact Nat.pow_le_pow_right (by omega) hh
    exact_mod_cast hh'
  have hPQ : ((2^(E B s j):ℕ):ℝ)≤(2^(F B s j):ℕ) := by
    exact_mod_cast Nat.pow_le_pow_right (by omega : 1≤(2:ℕ)) (E_le_F B s j)
  have hQ1 : (1:ℝ)≤(2^(F B s j):ℕ) := by exact_mod_cast (Nat.one_le_pow (F B s j) 2 (by omega))
  have he : (binErrorWidth (binQ B H s j) (binStart B H s j) (binWidth B s j) X:ℝ)≤
      (X:ℝ)/(binQ B H s j:ℝ)+2*((2^(F B s j):ℕ):ℝ) := by
    unfold binErrorWidth
    rw [(window_endpoints B H s j hB0).2]
    push_cast
    exact add_le_add Nat.cast_div_le le_rfl
  have hr := rational_error_budget (by exact_mod_cast hq) hqP hPQ hQ1 (by exact_mod_cast hX) he
  rw [(window_endpoints B H s j hB0).2] at hnorm
  have hi := inverse_binQ_geometric hB (j:=j)
  apply hnorm.trans
  have hsum : Real.exp (-(∑p∈primeWindow (binQ B H s j) (binStart B H s j) (binWidth B s j),(p:ℝ)⁻¹))+
      (∑p∈primeWindow (binQ B H s j) (binStart B H s j) (binWidth B s j),(p:ℝ)⁻¹^2)+
      (binErrorWidth (binQ B H s j) (binStart B H s j) (binWidth B s j) X:ℝ)/(X:ℝ)+
      (4*((2^(F B s j):ℕ):ℝ))^8/(X:ℝ)≤(Real.exp C+65540)*(1/2:ℝ)^(s+j) := by
    have hir : 65540/(binQ B H s j:ℝ)≤65540*(1/2:ℝ)^(s+j) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hi (by norm_num)
    nlinarith only [hmass,hsquare,hr,hir]
  have hh := mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num : (0:ℝ)≤512) errorSampleConstant_nonneg)
  simpa only [actualErrorConstant,mul_assoc] using hh

end OrdinaryChainScales

end

end OAI
