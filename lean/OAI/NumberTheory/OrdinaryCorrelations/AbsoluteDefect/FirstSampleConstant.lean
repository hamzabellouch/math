import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.FirstThresholdGain
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.TransitionConstant

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

namespace OrdinaryChainScales
open OrdinaryCorrelations SourcePrimeFactor OrdinaryNarrowGrid OrdinaryDirichletMeanSquare
open OrdinaryTwoScaleCofactor OrdinaryFrequencyChain Finset
attribute [local irreducible] E F mesh binQ binStart binWidth binLog amplifier

noncomputable def firstSampleConstant : ℝ :=
  transitionConstant*(2+(Real.log 2)^2)*Real.exp (Real.exp 1-1)

lemma firstSampleConstant_nonneg : 0≤ firstSampleConstant := by
  unfold firstSampleConstant
  exact mul_nonneg (mul_nonneg transitionConstant_nonneg (by positivity)) (Real.exp_pos _).le

lemma cofactor_sampled_small_height {f : ℕ→ℂ} (hf : OneBounded f)
    {d : ℕ} (χ : DirichletCharacter ℂ d) (P : Finset ℕ) {M : ℕ} (hM : 0<M)
    {T : ℝ} (hT : 0≤T) (hTM : T+1≤M)
    (S : Finset ℝ) (hsep : (S : Set ℝ).Pairwise (fun t u=>1≤|t-u|))
    (hheight : ∀t∈S,|t|≤T) :
    (∑t∈S,‖dyadicCofactorMellin f χ P M t‖^2)≤firstSampleConstant := by
  have hs := mixed_spaced_energy f χ ∅ P (by simp) 0 hM S
    (Q:=1) (c:=0) (B:=0) (by norm_num) hT (by norm_num) (by simp) (by simp)
    (fun t ht => abs_le.mp (hheight t ht)) (fun t ht u hu hne=>hsep ht hu hne)
  simp only [mul_zero,pow_zero,one_mul,Nat.cast_zero,zero_add] at hs
  have hm := dyadic_mixed_energy hf χ ∅ P (by simp) 0 (N:=1) (by norm_num) hM (by simp)
  simp only [pow_zero,mul_one,Nat.factorial_zero,Nat.cast_one,Nat.cast_zero,zero_add] at hm
  have hM' : 0<(M:ℝ) := by exact_mod_cast hM
  have hc : 0≤4*Real.exp (1+1/4)*gaussianConstant := by unfold gaussianConstant; positivity
  have hl : T+1+2*(M:ℝ)≤3*M := by linarith only [hTM]
  apply hs.trans
  calc
    _ ≤ 4*Real.exp (1+1/4)*gaussianConstant*(3*(M:ℝ))*(2+(Real.log 2)^2)*
        (2/(M:ℝ)*Real.exp (Real.exp 1-1)) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl hc) (by positivity)) hm
        (mixedEnergy_nonneg f χ ∅ P 0 M) (by positivity)
    _ = firstSampleConstant := by
      unfold firstSampleConstant transitionConstant
      field_simp
      ring

lemma binned_good_bound {ι : Type*} (I : Finset ι) (S : Finset ℝ)
    (Q C : ι→ℝ→ℂ) (V : ι→ℝ) {A : ℝ} (hA : 0≤A)
    (hV : ∀i∈I,0≤V i) (hQ : ∀i∈I,∀t∈S,‖Q i t‖≤V i)
    (hC : ∀i∈I,(∑t∈S,‖C i t‖^2)≤A) :
    (∑t∈S,‖∑i∈I,Q i t*C i t‖^2)≤A*((I.card:ℝ)*∑i∈I,(V i)^2) := by
  classical
  apply (binned_energy I S Q C).trans
  calc
    _ ≤ (I.card:ℝ)*∑i∈I,(V i)^2*A := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply sum_le_sum
      intro i hi
      apply le_trans ?_ (by
        simpa only [mul_comm] using
          mul_le_mul (hC i hi) (le_refl ((V i)^2)) (sq_nonneg _) hA)
      rw [mul_sum]
      exact sum_le_sum (fun t ht => mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ (norm_nonneg _) (hV i hi)).mpr (hQ i hi t ht)) (sq_nonneg _))
    _ = _ := by rw [←sum_mul]; ring

theorem actual_first_stage {f : ℕ→ℂ} (hf : OneBounded f)
    {d : ℕ} (χ : DirichletCharacter ℂ d) {B H s D X : ℕ}
    (hB : 2*H+s+30≤B) (hD : 4*2^(F B s 0)≤D) (hX : 2*2^(F B s 0)≤X)
    (S : Finset ℝ) (hsep : (S : Set ℝ).Pairwise (fun t u=>1≤|t-u|))
    (hheight : ∀t∈S,|t|≤(X:ℝ)/(D:ℝ)) :
    (∑t∈firstGood S
      (allBinsGood (fun j=>grid (binQ B H s j) (binStart B H s j) (binWidth B s j))
        (fun _ i=>primeMellin f χ (primeBin i))
        (fun j i=>threshold H j (binLog B H s j i))) 0,
      ‖binnedStage f χ (binQ B H s 0) (binStart B H s 0) (binWidth B s 0) X t‖^2)
      ≤firstSampleConstant*Real.exp (-1020*(mesh B H s 0:ℝ)) := by
  classical
  have hB0 : H+10≤B := by omega
  let I := grid (binQ B H s 0) (binStart B H s 0) (binWidth B s 0)
  let good := allBinsGood (fun j=>grid (binQ B H s j) (binStart B H s j) (binWidth B s j))
    (fun j i=>primeMellin f χ (primeBin i)) (fun j i=>threshold H j (binLog B H s j i))
  let T := firstGood S good 0
  have hsub : T⊆S := (filter_subset _ _).trans (filter_subset _ _)
  have hDpos : 0<D := lt_of_lt_of_le (by positivity : 0<4*2^(F B s 0)) hD
  have hc (i : ℕ×ℕ) (hi : i∈I) :
      (∑t∈T,‖dyadicCofactorMellin f χ (primeWindow (binQ B H s 0) (binStart B H s 0) (binWidth B s 0)) (evenBinLength X i) t‖^2)≤firstSampleConstant := by
    have hM := even_bin_length_pos (binQ B H s 0) (binStart B H s 0) (binWidth B s 0) X
      (by unfold binQ; positivity) (by rwa [(window_endpoints B H s 0 hB0).2]) hi
    have hu : 0<upper i := (grid_lower_pos _ _ _ (by unfold binQ; positivity) hi).trans_le (lower_le_upper i)
    have hiU := upper_le_endpoint _ _ _ hi
    rw [(window_endpoints B H s 0 hB0).2] at hiU
    have hXM := even_length_lower X hu ((Nat.mul_le_mul_left _ hiU).trans hX)
    have hXM' : (X:ℝ)≤2*(upper i:ℝ)*(evenBinLength X i:ℝ) := by exact_mod_cast hXM
    have huD : 4*(upper i:ℝ)≤D := by exact_mod_cast (Nat.le_trans (Nat.mul_le_mul_left 4 hiU) hD)
    have hD' : 0<(D:ℝ) := by exact_mod_cast hDpos
    have hdiv : (X:ℝ)/(D:ℝ)≤(evenBinLength X i:ℝ)/2 := by
      apply (div_le_iff₀ hD').mpr
      have hh := mul_le_mul_of_nonneg_right huD (Nat.cast_nonneg (evenBinLength X i))
      nlinarith only [hh,hXM']
    have hMtwo : 2≤evenBinLength X i := by
      unfold evenBinLength at hM ⊢
      omega
    apply cofactor_sampled_small_height hf χ _ hM (by positivity) _ T
      (hsep.mono (by exact_mod_cast hsub)) (fun t ht=>(hheight t (hsub ht)))
    have hMtwo' : (2:ℝ)≤evenBinLength X i := by exact_mod_cast hMtwo
    linarith only [hdiv,hMtwo']
  have hh := binned_good_bound I T
    (fun i=>primeMellin f χ (primeBin i))
    (fun i=>dyadicCofactorMellin f χ (primeWindow (binQ B H s 0) (binStart B H s 0) (binWidth B s 0)) (evenBinLength X i))
    (fun i=>threshold H 0 (binLog B H s 0 i)) firstSampleConstant_nonneg
    (fun i hi=>(threshold_pos _ _ _).le)
    (fun i hi t ht=>(mem_filter.mp ht).2 i hi) hc
  exact hh.trans (mul_le_mul_of_nonneg_left (first_threshold_sum hB) firstSampleConstant_nonneg)

end OrdinaryChainScales

end

end OAI
