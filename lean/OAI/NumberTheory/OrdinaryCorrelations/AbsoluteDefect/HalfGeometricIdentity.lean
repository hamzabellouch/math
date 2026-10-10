import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.FirstSampleConstant

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
open OrdinaryCorrelations SourcePrimeFactor OrdinaryNarrowGrid OrdinaryDirichletMeanSquare
open OrdinaryFrequencyChain Finset Filter
attribute [local irreducible] E F mesh binQ binStart binWidth binLog amplifier

lemma half_geometric_identity (J : ℕ) :
    (∑j∈range J,(1/2:ℝ)^j)+2*(1/2:ℝ)^J=2 := by
  induction J with
  | zero => simp
  | succ J ih => rw [sum_range_succ,pow_succ]; linarith only [ih]

lemma half_geometric_le (J : ℕ) : (∑j∈range J,(1/2:ℝ)^j)≤2 := by
  have hh := half_geometric_identity J
  have hp : 0≤(1/2:ℝ)^J := by positivity
  linarith only [hh,hp]

lemma geometric_error_sum {C : ℝ} (hC : 0≤C) (s J : ℕ) :
    (∑j∈range J,C*(1/2:ℝ)^(s+j))≤2*C*(1/2:ℝ)^s := by
  simp_rw [pow_add,←mul_assoc]
  rw [←mul_sum]
  have hh := mul_le_mul_of_nonneg_left (half_geometric_le J) (show 0≤C*(1/2:ℝ)^s by positivity)
  nlinarith only [hh]

lemma mesh_strict (B H s : ℕ) : StrictMono (mesh B H s) := by
  intro i j hij
  unfold mesh
  apply Nat.pow_lt_pow_right (by omega)
  have hs := Nat.pow_le_pow_left hij.le 2
  nlinarith

lemma mesh_linear_growth (B H s j : ℕ) : mesh B H s 0+j≤ mesh B H s j := by
  induction j with
  | zero => omega
  | succ j ih => have hh := mesh_strict B H s (show j<j+1 by omega); omega

lemma exp_mesh_geometric {B H s j : ℕ} {a : ℝ} (ha : 1≤a) :
    Real.exp (-a*(mesh B H s j:ℝ))≤Real.exp (-(mesh B H s 0:ℝ))*(1/2:ℝ)^j := by
  have hm : (mesh B H s 0:ℝ)+(j:ℝ)≤(mesh B H s j:ℝ) := by exact_mod_cast mesh_linear_growth B H s j
  have hl : Real.log 2≤1 := by have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith only [hh]
  have hj := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg j)
  have hh : -a*(mesh B H s j:ℝ)≤ -(mesh B H s 0:ℝ)-(j:ℝ)*Real.log 2 := by
    have hma := mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg (mesh B H s j))
    nlinarith only [hm,hj,hma]
  apply (Real.exp_le_exp.mpr hh).trans_eq
  rw [Real.exp_sub,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2),div_pow,one_pow]
  ring

lemma mesh_zero_exp {B H s M : ℕ} (hB : H+10+M≤B) :
    Real.exp (-(mesh B H s 0:ℝ))≤(1/2:ℝ)^M := by
  have hm : M≤ mesh B H s 0 := by
    have hh : M≤B-H-10 := by omega
    unfold mesh
    simp only [Nat.pow_two,Nat.mul_zero,Nat.add_zero]
    exact hh.trans (Nat.le_of_lt Nat.lt_two_pow_self)
  have hm' : (M:ℝ)≤(mesh B H s 0:ℝ) := by exact_mod_cast hm
  have hl : Real.log 2≤1 := by have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith only [hh]
  have hh := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg M)
  have he : -(mesh B H s 0:ℝ)≤ -(M:ℝ)*Real.log 2 := by nlinarith only [hh,hm']
  apply (Real.exp_le_exp.mpr he).trans_eq
  rw [neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
  rw [div_pow,one_pow,one_div]

lemma dyadic_cutoff_of_power {B s j X : ℕ} (hX : (2^(F B s j))^16≤X) :
    2*2^(F B s j)≤X := by
  have hQ : 2≤(2:ℕ)^(F B s j) := by simpa using Nat.pow_le_pow_right (by omega : 1≤(2:ℕ)) (F_pos B s j)
  have hh : 2*2^(F B s j)≤(2^(F B s j))^2 := by nlinarith
  exact (hh.trans (Nat.pow_le_pow_right (by omega) (by omega : 2≤16))).trans hX

lemma all_previous_power_cutoffs {B s j X R : ℕ} (hR : 1≤R)
    (hX : (2^(F B s j))^(64*R)≤X) :
    ∀i≤j,(2^(F B s i))^16≤X := by
  intro i hij
  have hf := (F_mono B s).monotone hij
  have hQ := Nat.pow_le_pow_right (by omega : 1≤(2:ℕ)) hf
  apply (Nat.pow_le_pow_left hQ 16).trans
  exact (Nat.pow_le_pow_right (by positivity) (by omega : 16≤64*R)).trans hX

lemma all_good_energy {f : ℕ→ℂ} (hf : OneBounded f) {d : ℕ} (χ : DirichletCharacter ℂ d)
    {B H s K D X J : ℕ} (hA : transitionConstant+Real.exp 1+10≤(2:ℝ)^K)
    (hB : H+4*s+K+70≤B) (hB' : 2*H+s+30≤B)
    (hD : 4*2^(F B s 0)≤D) (hX : ∀i≤J,2*2^(F B s i)≤X)
    (S : Finset ℝ) (hsep : (S : Set ℝ).Pairwise (fun t u=>1≤|t-u|))
    (hheight : ∀t∈S,|t|≤(X:ℝ)/(D:ℝ)) :
    (∑j∈range (J+1),∑t∈firstGood S
      (allBinsGood (fun j=>grid (binQ B H s j) (binStart B H s j) (binWidth B s j))
        (fun _stage i=>primeMellin f χ (primeBin i))
        (fun j i=>threshold H j (binLog B H s j i))) j,
      ‖binnedStage f χ (binQ B H s j) (binStart B H s j) (binWidth B s j) X t‖^2)
      ≤(firstSampleConstant+2)*Real.exp (-(mesh B H s 0:ℝ)) := by
  classical
  have hDp : 0<D := (by positivity : 0<4*2^(F B s 0)).trans_le hD
  have hheightX : ∀t∈S,|t|≤(X:ℝ) := fun t ht => (hheight t ht).trans
    (div_le_self (Nat.cast_nonneg X) (by exact_mod_cast hDp))
  have hfirst := actual_first_stage hf χ hB' hD (hX 0 (by omega)) S hsep hheight
  have he0 := exp_mesh_geometric (B:=B) (H:=H) (s:=s) (j:=0) (by norm_num : (1:ℝ)≤1020)
  simp only [pow_zero,mul_one] at he0
  have hf0 := hfirst.trans (mul_le_mul_of_nonneg_left he0 firstSampleConstant_nonneg)
  rw [sum_range_succ']
  have hsum : (∑j∈range J,∑t∈firstGood S
      (allBinsGood (fun j=>grid (binQ B H s j) (binStart B H s j) (binWidth B s j))
        (fun j i=>primeMellin f χ (primeBin i))
        (fun j i=>threshold H j (binLog B H s j i))) (j+1),
      ‖binnedStage f χ (binQ B H s (j+1)) (binStart B H s (j+1)) (binWidth B s (j+1)) X t‖^2)
      ≤2*Real.exp (-(mesh B H s 0:ℝ)) := by
    calc
      _ ≤ ∑j∈range J,Real.exp (-(mesh B H s 0:ℝ))*(1/2:ℝ)^j := by
        apply sum_le_sum
        intro j hj
        apply (actual_next_stage hf χ hA hB hB' (hX (j+1) (by have := mem_range.mp hj; omega)) S hsep hheightX).trans
        apply (exp_mesh_geometric (B:=B) (H:=H) (s:=s) (j:=j+1) (by norm_num : (1:ℝ)≤993)).trans
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        rw [pow_succ]
        nlinarith only [pow_nonneg (by norm_num : (0:ℝ)≤1/2) j]
      _ ≤ 2*Real.exp (-(mesh B H s 0:ℝ)) := by
        rw [←mul_sum]
        have hh := mul_le_mul_of_nonneg_left (half_geometric_le J) (Real.exp_pos (-(mesh B H s 0:ℝ))).le
        nlinarith only [hh]
  nlinarith only [hf0,hsum]

end OrdinaryChainScales

end

end OAI
