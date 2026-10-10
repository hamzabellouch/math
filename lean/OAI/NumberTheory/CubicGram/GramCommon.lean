import Mathlib
import OAI.NumberTheory.CubicGram.GramNormalize

namespace OAI

/-! Squared common-factor blocks of the character Gram matrix. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryCharacterGram_common_sq {k a b : Eisenstein} (hk : primary k)
    (hsk : Squarefree k) (ha : primary a) (hb : primary b)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {Z : ℝ} (hZ : 0 < Z) :
    ‖primaryCharacterGram (k*a) (k*b) W Z‖^2 ≤
      (2 : ℝ)^(primaryPrimeFactors k).card *
      ∑ s ∈ (primaryPrimeFactors k).powerset,
        ‖primaryCharacterGram a b W (Z/norm (∏ p ∈ s, p))‖^2 := by
  rw [primaryCharacterGram_common_factor hk hsk ha hb W hW hW' hZ]
  have h := norm_sum_sq_weighted (primaryPrimeFactors k).powerset
    (fun s => (idealMoebius (∏ p ∈ s, p) : ℂ)*mixedSymbol a b (∏ p ∈ s,p)*
      primaryCharacterGram a b W (Z/norm (∏ p ∈ s,p))) (fun _ => 1) (by simp)
  simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,mul_one,Nat.cast_pow,
    Nat.cast_ofNat,div_one] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro s hs
  apply pow_le_pow_left₀ (_root_.norm_nonneg _)
  simp only [norm_mul,mixedSymbol,norm_star]
  calc
    _ ≤ 1*1*1*‖primaryCharacterGram a b W (Z/norm (∏ p ∈ s,p))‖ := by
      gcongr
      · simpa only [one_mul] using norm_idealMoebius_le_one (∏ p ∈ s,p)
      · simpa only [one_mul] using mul_le_mul (norm_cubicSymbol_le_one ha (∏ p ∈ s,p))
          (norm_cubicSymbol_le_one hb (∏ p ∈ s,p)) (_root_.norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    _ = _ := by ring

theorem primaryCharacterGram_common_block (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : Finset Eisenstein) (P Z : ℝ) (p k : Eisenstein),
      1 ≤ P → 1 ≤ Z → gramDyad P p →
      (∀ q ∈ Q, gramDyad P q ∧ q ≠ p ∧ primaryCommonFactor p q = k) →
      primary k → Squarefree k → k ∣ p →
      (∑ q ∈ Q, ‖primaryCharacterGram p q W Z‖^2) ≤
        ((2 : ℝ)^(primaryPrimeFactors k).card)^2 *
          (C*(2 : ℝ)^ε*P^(4*ε)*(Z*P+P^2+P^2*Z^(1/3 : ℝ))) := by
  obtain ⟨C,hC,hc⟩ := primaryCharacterGram_coprime_normalized W hW hW' hε hε1
  refine ⟨C,hC,?_⟩
  intro Q P Z p k hP hZ hp hQ hk hsk hkp
  obtain ⟨a,hpa⟩ := hkp
  have hak : primary a := primary_of_mul hk (hpa ▸ hp.1)
  have hasa : Squarefree a := (hpa ▸ hp.2.1).of_mul_right
  have han : 0 < norm a := norm_pos_of_ne_zero (primary_ne_zero hak)
  have hk1 := one_le_norm (primary_ne_zero hk)
  have hk0 : 0 < norm k := by linarith
  have hnorm : norm p = norm k*norm a := by rw [hpa]; exact Complex.normSq_mul _ _
  have hkP : norm k ≤ 2*P := (norm_le_of_dvd (primary_ne_zero hp.1) ⟨a,hpa⟩).trans hp.2.2.2.le
  have hN : 1 ≤ 2*(P/norm k) := by rw [← mul_div_assoc]; apply (le_div_iff₀ hk0).mpr; nlinarith
  have haN : norm a ≤ 2*(P/norm k) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hk0).mpr
    nlinarith [hp.2.2.2]
  let B := residualRows Q k
  have hbmem b (hb : b ∈ B) : k*b ∈ Q := (mem_residualRows (primary_ne_zero hk)).mp hb
  have hB b (hb : b ∈ B) : primary b ∧ Squarefree b ∧ P/norm k ≤ norm b ∧ norm b ≤ 2*(P/norm k) := by
    have hq := (hQ (k*b) (hbmem b hb)).1
    have hn : norm (k*b) = norm k*norm b := Complex.normSq_mul _ _
    refine ⟨primary_of_mul hk hq.1,hq.2.1.of_mul_right,?_,?_⟩
    · apply (div_le_iff₀ hk0).mpr
      nlinarith [hq.2.2.1]
    · rw [← mul_div_assoc]
      apply (le_div_iff₀ hk0).mpr
      nlinarith [hq.2.2.2]
  have hab b (hb : b ∈ B) : IsCoprime a b ∧ a ≠ b := by
    have hh := hQ (k*b) (hbmem b hb)
    constructor
    · apply (commonFactor_eq_iff_coprime hk hsk hak (hB b hb).1
        (hpa ▸ hp.2.1) hh.1.2.1).mp
      simpa only [← hpa] using hh.2.2
    · intro he
      exact hh.2.1 (by rw [← he,← hpa])
  have hreindex : (∑ q ∈ Q, ‖primaryCharacterGram p q W Z‖^2) =
      ∑ b ∈ B, ‖primaryCharacterGram (k*a) (k*b) W Z‖^2 := by
    rw [← hpa]
    change _ = ∑ b ∈ residualRows Q k, _
    rw [residualRows_sum_image Q (primary_ne_zero hk) (fun q => ‖primaryCharacterGram p q W Z‖^2)]
    apply Finset.sum_congr rfl
    intro q hq
    have hdiv := (primaryCommonFactor_spec hp.1 (hQ q hq).1.1 hp.2.1 (hQ q hq).1.2.1).2.2.2
    rw [(hQ q hq).2.2] at hdiv
    simp only [ite_eq_left hdiv]
  rw [hreindex]
  have hsum := Finset.sum_le_sum (s := B) (fun b hb =>
    primaryCharacterGram_common_sq hk hsk hak (hB b hb).1 W hW hW' (by linarith : 0 < Z))
  rw [← Finset.mul_sum,Finset.sum_comm] at hsum
  have hrow s (hs : s ∈ (primaryPrimeFactors k).powerset) :
      (∑ b ∈ B, ‖primaryCharacterGram a b W (Z/norm (∏ p ∈ s,p))‖^2) ≤
        C*(2 : ℝ)^ε*P^(4*ε)*(Z*P+P^2+P^2*Z^(1/3 : ℝ)) := by
    let m := ∏ p ∈ s,p
    have hm : primary m := primary_finset_prod _ _
      (fun p hp => (primaryPrimeFactor_spec hk (Finset.mem_powerset.mp hs hp)).1.1)
    have hmk : m ∣ k := (primary_subsets_prod_dvd hk (Finset.mem_powerset.mp hs) k).mpr
      (fun p hp => (primaryPrimeFactor_spec hk (Finset.mem_powerset.mp hs hp)).2)
    have hm1 := one_le_norm (primary_ne_zero hm)
    have hmP : norm m ≤ 2*P := (norm_le_of_dvd (primary_ne_zero hk) hmk).trans hkP
    have hh := hc B (P/norm k) hN hB a hak hasa haN hab (Z/norm m) (by positivity)
    have hh' := mul_le_mul_of_nonneg_left (gram_scaled_loss hP hZ hk1 hm1 hmP hε) hC.le
    exact hh.trans (by convert hh' using 1 <;> ring)
  apply hsum.trans
  calc
    _ ≤ (2 : ℝ)^(primaryPrimeFactors k).card *
        ∑ s ∈ (primaryPrimeFactors k).powerset,
          C*(2 : ℝ)^ε*P^(4*ε)*(Z*P+P^2+P^2*Z^(1/3 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum hrow) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      ring

end CubicFirstMoment
end
end

end OAI
