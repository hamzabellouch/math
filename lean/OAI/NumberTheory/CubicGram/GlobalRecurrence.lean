import Mathlib
import OAI.NumberTheory.CubicGram.CommonRows

namespace OAI

/-! Summed dual norms and full smoothed sieve recurrences. -/

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def dualDyadicNorm (S : Finset Eisenstein) (c : ℝ) (A : ℕ) : ℝ :=
  ∑' j : ℕ, finiteCubicBound S (frequencyDyad j) / (1+c*2^j)^A

lemma summable_dualDyadicNorm (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) {c : ℝ} (hc : 0 < c) {A : ℕ} (hA : 2 ≤ A) :
    Summable (fun j : ℕ => finiteCubicBound S (frequencyDyad j) / (1+c*2^j)^A) := by
  have hs := (dyadic_decay_summable hc).mul_left (36*(S.card : ℝ))
  apply hs.of_nonneg_of_le
  · intro j
    exact div_nonneg (finiteCubicBound_nonneg _ _) (by positivity)
  · intro j
    have hd : 0 < (1+c*(2 : ℝ)^j)^2 := by positivity
    have hp : (1+c*(2 : ℝ)^j)^2 ≤ (1+c*2^j)^A :=
      pow_le_pow_right₀ (by linarith [show 0 ≤ c*(2 : ℝ)^j by positivity]) hA
    calc
      _ ≤ finiteCubicBound S (frequencyDyad j)/(1+c*2^j)^2 :=
        div_le_div_of_nonneg_left (finiteCubicBound_nonneg _ _) hd hp
      _ ≤ (36*S.card*2^j)/(1+c*2^j)^2 := by
        apply div_le_div_of_nonneg_right _ hd.le
        exact (finiteCubicBound_le_card_mul S _ hS).trans
          ((mul_le_mul_of_nonneg_left (frequencyDyad_card_le j) (by positivity)).trans_eq (by ring))
      _ = _ := by ring

lemma dualDyadicNorm_nonneg (S : Finset Eisenstein) {c : ℝ} (hc : 0 ≤ c) (A : ℕ) :
    0 ≤ dualDyadicNorm S c A :=
  tsum_nonneg (fun j => div_nonneg (finiteCubicBound_nonneg _ _) (by positivity))

theorem coprimeGramForm_norm_recurrence (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (A : ℕ) (hA : 2 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein),
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ ¬ IsUnit a) →
      ∀ (u : Eisenstein → ℂ) (Z N : ℝ), 0 < Z → 0 < N →
      (∀ a ∈ S, N ≤ norm a ∧ norm a ≤ Real.sqrt 2*N) →
      ‖coprimeGramForm S u W Z‖ ≤ C*(Z/N)*
        dualDyadicNorm S (Z/(27*N^2)) A *
          ∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖u a‖^2 := by
  obtain ⟨C,hC,hbound⟩ := coprimePoissonDyad_norm_recurrence W hW hW' A
  refine ⟨C,hC,?_⟩
  intro S hS u Z N hZ hN hSN
  let E : ℝ := ∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖u a‖^2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun a _ => by positivity)
  let c : ℝ := Z/(27*N^2)
  have hc : 0 < c := by dsimp [c]; positivity
  have hterm (j : ℕ) : ‖coprimePoissonDyad S (frequencyDyad j) u W Z‖ ≤
      (C*(Z/N)*E)*(finiteCubicBound S (frequencyDyad j)/(1+c*2^j)^A) := by
    have hrec := hbound S (frequencyDyad j) (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩)
      u Z ((2 : ℝ)^j) N hZ.le (by positivity) hN hSN (fun h hh => frequencyDyad_norm hh)
    have he : Z*2^j/(27*N^2) = c*2^j := by dsimp [c]; ring
    rw [he] at hrec
    calc
      _ ≤ C*(Z/N)*finiteCubicBound S (frequencyDyad j)*E/(1+c*2^j)^A := by
        apply (le_div_iff₀ (by positivity : 0 < (1+c*(2 : ℝ)^j)^A)).mpr
        simpa only [mul_comm,E] using hrec
      _ = _ := by ring
  have hs := summable_dualDyadicNorm S (fun a ha => (hS a ha).1) hc hA
  have hd := hasSum_coprimePoissonDyad S hS u W hW hW' hZ
  calc
    _ = ‖∑' j : ℕ, coprimePoissonDyad S (frequencyDyad j) u W Z‖ := by rw [hd.tsum_eq]
    _ ≤ ∑' j : ℕ, ‖coprimePoissonDyad S (frequencyDyad j) u W Z‖ :=
      norm_tsum_le_tsum_norm hd.summable.norm
    _ ≤ ∑' j : ℕ, (C*(Z/N)*E)*(finiteCubicBound S (frequencyDyad j)/(1+c*2^j)^A) :=
      Summable.tsum_le_tsum hterm hd.summable.norm (hs.mul_left _)
    _ = _ := by rw [tsum_mul_left]; dsimp [dualDyadicNorm,c,E]; ring

lemma residualRows_norm {S : Finset Eisenstein} {k : Eisenstein} (hk : primary k)
    {N : ℝ} (hS : ∀ p ∈ S, N ≤ norm p ∧ norm p ≤ Real.sqrt 2*N) :
    ∀ a ∈ residualRows S k, N/norm k ≤ norm a ∧ norm a ≤ Real.sqrt 2*(N/norm k) := by
  have hn : 0 < norm k := norm_pos_of_ne_zero (primary_ne_zero hk)
  intro a ha
  have hh := hS (k*a) ((mem_residualRows (primary_ne_zero hk)).mp ha)
  rw [show norm (k*a) = norm k*norm a from Complex.normSq_mul _ _] at hh
  constructor
  · exact (div_le_iff₀ hn).mpr (by nlinarith [hh.1])
  · rw [← mul_div_assoc]
    apply (le_div_iff₀ hn).mpr
    nlinarith [hh.2]

lemma residualRows_nonunit {S : Finset Eisenstein} {k : Eisenstein} (hk : primary k)
    {N : ℝ} (hNk : norm k < N) (hS : ∀ p ∈ S, N ≤ norm p) :
    ∀ a ∈ residualRows S k, ¬ IsUnit a := by
  intro a ha hu
  have hh := hS (k*a) ((mem_residualRows (primary_ne_zero hk)).mp ha)
  rw [show norm (k*a) = norm k*norm a from Complex.normSq_mul _ _,norm_of_isUnit hu,mul_one] at hh
  exact (not_lt_of_ge hh) hNk

lemma residualRows_subset_one {S : Finset Eisenstein} {k : Eisenstein} (hk : primary k)
    (hS : ∀ p ∈ S, primary p) {N : ℝ} (hNk : N ≤ norm k)
    (hSN : ∀ p ∈ S, norm p ≤ Real.sqrt 2*N) :
    residualRows S k ⊆ {1} := by
  intro a ha
  have hp := hS (k*a) ((mem_residualRows (primary_ne_zero hk)).mp ha)
  have hpa := primary_of_mul hk hp
  have hpos : 0 < norm k := norm_pos_of_ne_zero (primary_ne_zero hk)
  have hna : norm a ≤ Real.sqrt 2 := by
    have hh := hSN (k*a) ((mem_residualRows (primary_ne_zero hk)).mp ha)
    rw [show norm (k*a) = norm k*norm a from Complex.normSq_mul _ _] at hh
    have hh' := hh.trans (mul_le_mul_of_nonneg_left hNk (Real.sqrt_nonneg _))
    nlinarith
  have hna' : norm a < 2 := hna.trans_lt (by norm_num : Real.sqrt (2 : ℝ) < 2)
  have hone : norm a = 1 := by
    have hltreal : (normNat a : ℝ) < (2 : ℝ) := by rw [normNat_cast]; exact hna'
    have hlt : normNat a < 2 := by exact_mod_cast hltreal
    have hnz := normNat_ne_zero_of_ne_zero (primary_ne_zero hpa)
    rw [← normNat_cast,show normNat a = 1 by omega,Nat.cast_one]
  exact Finset.mem_singleton.mpr (primary_unit_eq_one (isUnit_of_norm_eq_one hone) hpa)

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma coprimeGramForm_subset_singleton (R : Finset Eisenstein) (hR : R ⊆ {1})
    (v : Eisenstein → ℂ) (W : ℝ → ℂ) (Z : ℝ) :
    ‖coprimeGramForm R v W Z‖ ≤
      ‖primaryCharacterGram 1 1 W Z‖ * ∑ a ∈ R, ‖v a‖^2 := by
  by_cases h1 : (1 : Eisenstein) ∈ R
  · have he : R = {1} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨h1,fun a ha => Finset.mem_singleton.mp (hR ha)⟩
    simp only [coprimeGramForm,he,Finset.sum_singleton,isCoprime_one_left,ite_true,
      norm_mul,norm_star]
    exact le_of_eq (by ring)
  · have he : R = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun a ha =>
      h1 ((Finset.mem_singleton.mp (hR ha)) ▸ ha))
    simp [coprimeGramForm,he]

def commonBlockEnergy (S : Finset Eisenstein) (u : Eisenstein → ℂ) (k : Eisenstein) : ℝ :=
  ∑ a ∈ residualRows S k, (2 : ℝ)^(primaryPrimeFactors a).card * ‖u (k*a)‖^2

lemma commonBlockEnergy_nonneg (S : Finset Eisenstein) (u : Eisenstein → ℂ) (k : Eisenstein) :
    0 ≤ commonBlockEnergy S u k := Finset.sum_nonneg (fun a _ => by positivity)

lemma commonBlockCoefficient_energy_le (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (u : Eisenstein → ℂ)
    {k : Eisenstein} (hk : primary k) (m : Eisenstein) :
    (∑ a ∈ residualRows S k, (2 : ℝ)^(primaryPrimeFactors a).card *
      ‖commonBlockCoefficient u k m a‖^2) ≤ commonBlockEnergy S u k := by
  apply Finset.sum_le_sum
  intro a ha
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ (_root_.norm_nonneg _)
    (commonBlockCoefficient_norm_le u k m (residualRows_primary hk hS a ha).1) 2

lemma commonBlockCoefficient_unweighted_energy_le (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (u : Eisenstein → ℂ)
    {k : Eisenstein} (hk : primary k) (m : Eisenstein) :
    (∑ a ∈ residualRows S k, ‖commonBlockCoefficient u k m a‖^2) ≤ commonBlockEnergy S u k := by
  apply le_trans _ (commonBlockCoefficient_energy_le S hS u hk m)
  apply Finset.sum_le_sum
  intro a ha
  exact le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ (by norm_num))

def commonBlockCost (S : Finset Eisenstein) (W : ℝ → ℂ) (Z N : ℝ) (A : ℕ)
    (k m : Eisenstein) : ℝ :=
  if norm k < N then
    ((Z/norm m)/(N/norm k)) *
      dualDyadicNorm (residualRows S k) ((Z/norm m)/(27*(N/norm k)^2)) A
  else ‖primaryCharacterGram 1 1 W (Z/norm m)‖

lemma commonBlockCost_nonneg (S : Finset Eisenstein) (W : ℝ → ℂ)
    {Z N : ℝ} (hZ : 0 ≤ Z) (hN : 0 ≤ N) (A : ℕ) (k m : Eisenstein) :
    0 ≤ commonBlockCost S W Z N A k m := by
  have hnk := norm_nonneg k
  have hnm := norm_nonneg m
  unfold commonBlockCost
  split_ifs
  · exact mul_nonneg (by positivity)
      (dualDyadicNorm_nonneg _ (by positivity) _)
  · exact _root_.norm_nonneg _

theorem primarySmoothedSieveMass_norm_recurrence (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (A : ℕ) (hA : 2 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein),
      (∀ a ∈ S, primary a ∧ Squarefree a) →
      ∀ (u : Eisenstein → ℂ) (Z N : ℝ), 0 < Z → 0 < N →
      (∀ a ∈ S, N ≤ norm a ∧ norm a ≤ Real.sqrt 2*N) →
      ‖primarySmoothedSieveMass S u W Z‖ ≤ C *
        ∑ k ∈ commonRowFactors S,
          (∑ s ∈ (primaryPrimeFactors k).powerset,
            commonBlockCost S W Z N A k (∏ p ∈ s, p)) * commonBlockEnergy S u k := by
  obtain ⟨C₀,hC₀,hrec⟩ := coprimeGramForm_norm_recurrence W hW hW' A hA
  let C := max C₀ 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have h1C : 1 ≤ C := le_max_right _ _
  have hC₀C : C₀ ≤ C := le_max_left _ _
  refine ⟨C,hC,?_⟩
  intro S hS u Z N hZ hN hSN
  have hblock (k : Eisenstein) (hkS : k ∈ commonRowFactors S)
      (s : Finset Eisenstein) (hs : s ∈ (primaryPrimeFactors k).powerset) :
      let m := ∏ p ∈ s, p
      ‖(idealMoebius m : ℂ) * coprimeGramForm (residualRows S k)
        (commonBlockCoefficient u k m) W (Z/norm m)‖ ≤
        C * commonBlockCost S W Z N A k m * commonBlockEnergy S u k := by
    dsimp only
    let m := ∏ p ∈ s, p
    have hk := commonRowFactors_spec hS hkS
    have hm : primary m := primary_finset_prod _ _
      (fun p hp => (primaryPrimeFactor_spec hk.1 (Finset.mem_powerset.mp hs hp)).1.1)
    have hmk : 0 < norm k := norm_pos_of_ne_zero (primary_ne_zero hk.1)
    have hmm : 0 < norm m := norm_pos_of_ne_zero (primary_ne_zero hm)
    have hre := residualRows_primary hk.1 hS
    have hbound : ‖coprimeGramForm (residualRows S k) (commonBlockCoefficient u k m) W (Z/norm m)‖ ≤
        C * commonBlockCost S W Z N A k m * commonBlockEnergy S u k := by
      by_cases hkN : norm k < N
      · have hd := dualDyadicNorm_nonneg (residualRows S k)
          (by positivity : 0 ≤ (Z/norm m)/(27*(N/norm k)^2)) A
        have hh := hrec (residualRows S k)
          (fun a ha => ⟨(hre a ha).1,(hre a ha).2,
            residualRows_nonunit hk.1 hkN (fun p hp => (hSN p hp).1) a ha⟩)
          (commonBlockCoefficient u k m) (Z/norm m) (N/norm k)
          (div_pos hZ hmm) (div_pos hN hmk) (residualRows_norm hk.1 hSN)
        rw [commonBlockCost,ite_eq_left hkN]
        calc
          _ ≤ C₀*((Z/norm m)/(N/norm k))*
              dualDyadicNorm (residualRows S k) ((Z/norm m)/(27*(N/norm k)^2)) A *
              commonBlockEnergy S u k := hh.trans (mul_le_mul_of_nonneg_left
                (commonBlockCoefficient_energy_le S hS u hk.1 m)
                (mul_nonneg (mul_nonneg hC₀.le (by positivity)) hd))
          _ = C₀ * (((Z/norm m)/(N/norm k))*
              dualDyadicNorm (residualRows S k) ((Z/norm m)/(27*(N/norm k)^2)) A) *
              commonBlockEnergy S u k := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hC₀C (mul_nonneg (by positivity) hd))
            (commonBlockEnergy_nonneg S u k)
      · rw [commonBlockCost,ite_eq_right hkN]
        calc
          _ ≤ ‖primaryCharacterGram 1 1 W (Z/norm m)‖ *
              ∑ a ∈ residualRows S k, ‖commonBlockCoefficient u k m a‖^2 :=
            coprimeGramForm_subset_singleton _
              (residualRows_subset_one hk.1 (fun p hp => (hS p hp).1) (le_of_not_gt hkN)
                (fun p hp => (hSN p hp).2)) _ _ _
          _ ≤ ‖primaryCharacterGram 1 1 W (Z/norm m)‖ * commonBlockEnergy S u k :=
            mul_le_mul_of_nonneg_left (commonBlockCoefficient_unweighted_energy_le S hS u hk.1 m)
              (_root_.norm_nonneg _)
          _ ≤ _ := by
            have he : 0 ≤ ‖primaryCharacterGram 1 1 W (Z/norm m)‖ * commonBlockEnergy S u k :=
              mul_nonneg (_root_.norm_nonneg _) (commonBlockEnergy_nonneg S u k)
            nlinarith [mul_le_mul_of_nonneg_right h1C he]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_idealMoebius_le_one m)).trans hbound
  rw [primarySmoothedSieveMass_common_blocks S hS u W hW hW' hZ]
  calc
    _ ≤ ∑ k ∈ commonRowFactors S, ∑ s ∈ (primaryPrimeFactors k).powerset,
        ‖(idealMoebius (∏ p ∈ s, p) : ℂ) * coprimeGramForm (residualRows S k)
          (commonBlockCoefficient u k (∏ p ∈ s, p)) W (Z/norm (∏ p ∈ s, p))‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k hk => norm_sum_le _ _))
    _ ≤ ∑ k ∈ commonRowFactors S, ∑ s ∈ (primaryPrimeFactors k).powerset,
        C * commonBlockCost S W Z N A k (∏ p ∈ s, p) * commonBlockEnergy S u k :=
      Finset.sum_le_sum (fun k hk => Finset.sum_le_sum (fun s hs => hblock k hk s hs))
    _ = _ := by
      simp_rw [← Finset.sum_mul,← Finset.mul_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

end CubicFirstMoment
end
end

end OAI
