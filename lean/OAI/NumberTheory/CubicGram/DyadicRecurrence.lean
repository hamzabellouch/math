import Mathlib
import OAI.NumberTheory.CubicGram.NormRecurrence
import OAI.NumberTheory.CubicGram.LatticeCounts

namespace OAI

/-! Frequency dyads and summable base Gram recurrences. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma normNat_ne_zero_of_ne_zero {h : Eisenstein} (hh : h ≠ 0) : normNat h ≠ 0 := by
  intro hz
  apply hh
  apply norm_eq_zero_iff.mp
  rw [← normNat_cast,hz,Nat.cast_zero]

def frequencyDyad (j : ℕ) : Finset Eisenstein :=
  (nonzeroNormBall ((2 : ℝ)^(j+1))).filter (fun h => Nat.log 2 (normNat h) = j)

lemma mem_frequencyDyad {j : ℕ} {h : Eisenstein} :
    h ∈ frequencyDyad j ↔ h ≠ 0 ∧ Nat.log 2 (normNat h) = j := by
  simp only [frequencyDyad, Finset.mem_filter, mem_nonzeroNormBall]
  refine ⟨fun h => ⟨h.1.2,h.2⟩,fun hh => ⟨⟨?_,hh.1⟩,hh.2⟩⟩
  have ht := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (normNat h)
  rw [hh.2] at ht
  rw [← normNat_cast]
  exact_mod_cast ht.le

lemma frequencyDyad_norm {j : ℕ} {h : Eisenstein} (hh : h ∈ frequencyDyad j) :
    (2 : ℝ)^j ≤ norm h ∧ norm h ≤ 2*(2 : ℝ)^j := by
  rw [mem_frequencyDyad] at hh
  have hl := Nat.pow_log_le_self 2 (normNat_ne_zero_of_ne_zero hh.1)
  have ht := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (normNat h)
  rw [hh.2] at hl ht
  rw [← normNat_cast]
  constructor
  · exact_mod_cast hl
  · have ht' : (normNat h : ℝ) ≤ (2 : ℝ)^(j+1) := by exact_mod_cast ht.le
    simpa [pow_succ,mul_comm] using ht'

lemma summable_gramDualTerm {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {Z : ℝ} (hZ : 0 < Z) : Summable (gramDualTerm a b W Z) := by
  let q : ℂ := (Real.sqrt Z : ℂ)/(3*((a*b : Eisenstein) : ℂ)*traceLambda)
  have hq : q ≠ 0 := by
    apply div_ne_zero
    · exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hZ)
    · exact mul_ne_zero (mul_ne_zero (by norm_num)
        (fun hz => mul_ne_zero (primary_ne_zero ha) (primary_ne_zero hb) (Subtype.ext hz)))
        traceLambda_ne_zero
  have hs := (schwartz_summable_eisenstein_coset
    (normProfileFourierSchwartz W hW hW') q hq 0).norm
  apply Summable.of_norm_bounded hs
  intro h
  rw [zero_add,normProfileFourierSchwartz_apply]
  dsimp only [q]
  have he : ((Real.sqrt Z : ℂ)/(3*((a*b : Eisenstein) : ℂ)*traceLambda))*(h : ℂ) =
      (Real.sqrt Z : ℂ)*((h : ℂ)/(3*((a*b : Eisenstein) : ℂ)*traceLambda)) := by ring
  rw [he]
  simp only [gramDualTerm,norm_mul,norm_star,Circle.norm_coe,mul_one]
  apply mul_le_of_le_one_left (_root_.norm_nonneg _)
  exact (mul_le_mul (norm_cubicSymbol_le_one ha h) (norm_cubicSymbol_le_one hb h)
    (_root_.norm_nonneg _) (by norm_num)).trans (by norm_num)

lemma hasSum_frequencyDyad (F : Eisenstein → ℂ) (hF : Summable F) (h0 : F 0 = 0) :
    HasSum (fun j : ℕ => ∑ h ∈ frequencyDyad j, F h) (∑' h : Eisenstein, F h) := by
  have he := hF.hasSum.tsum_fiberwise (fun h : Eisenstein => Nat.log 2 (normNat h))
  have hf (j : ℕ) : (∑' h : ((fun h : Eisenstein => Nat.log 2 (normNat h)) ⁻¹' {j}), F h) =
      ∑ h ∈ frequencyDyad j, F h := by
    rw [tsum_subtype]
    calc
      _ = ∑ h ∈ frequencyDyad j,
          Set.indicator ((fun h : Eisenstein => Nat.log 2 (normNat h)) ⁻¹' {j}) F h := by
        apply tsum_eq_sum
        intro h hh
        by_cases hz : h = 0
        · subst h; simp [h0]
        · have hj : Nat.log 2 (normNat h) ≠ j := fun hj => hh (mem_frequencyDyad.mpr ⟨hz,hj⟩)
          simp [hj]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro h hh
        have hm : h ∈ ((fun h : Eisenstein => Nat.log 2 (normNat h)) ⁻¹' {j}) :=
          (mem_frequencyDyad.mp hh).2
        exact Set.indicator_of_mem hm F

  simpa only [hf] using he

end CubicFirstMoment

namespace CubicFirstMoment

lemma finiteCubicBound_le_card_mul (S H : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) :
    finiteCubicBound S H ≤ (S.card : ℝ)*H.card := by
  apply (finiteCubicBound_le_iff S H (by positivity)).mpr
  intro u
  have hrow (h : Eisenstein) :
      ‖∑ a ∈ S, u a*cubicSymbol a h‖^2 ≤ (S.card : ℝ)*∑ a ∈ S, ‖u a‖^2 := by
    have ht : ‖∑ a ∈ S, u a*cubicSymbol a h‖ ≤ ∑ a ∈ S, ‖u a‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a ha
      rw [norm_mul]
      exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hS a ha) h)
    have hc := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun a => ‖u a‖)
    simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hc
    exact (pow_le_pow_left₀ (_root_.norm_nonneg _) ht 2).trans hc
  calc
    _ ≤ ∑ _h ∈ H, (S.card : ℝ)*∑ a ∈ S, ‖u a‖^2 := Finset.sum_le_sum (fun h _ => hrow h)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

lemma dyadic_decay_step {c : ℝ} (hc : 0 < c) (j : ℕ) :
    (2 : ℝ)^j / (1+c*2^j)^2 ≤
      (2/c)*(1/(1+c*2^j)-1/(1+c*2^(j+1))) := by
  have hJ : 0 < (2 : ℝ)^j := by positivity
  have h1 : 0 < 1+c*2^j := by positivity
  have h2 : 0 < 1+2*c*2^j := by positivity
  calc
    _ ≤ 2*2^j / ((1+c*2^j)*(1+2*c*2^j)) := by
      apply (div_le_div_iff₀ (sq_pos_of_pos h1) (mul_pos h1 h2)).mpr
      nlinarith [sq_nonneg (c*2^j),sq_nonneg ((2 : ℝ)^j), mul_pos hc hJ]
    _ = _ := by
      rw [pow_succ]
      have h2' : 1+c*((2 : ℝ)^j*2) ≠ 0 := by positivity
      field_simp
      ring

lemma dyadic_decay_partial_sum {c : ℝ} (hc : 0 < c) (n : ℕ) :
    (∑ j ∈ Finset.range n, (2 : ℝ)^j/(1+c*2^j)^2) ≤ 2/c := by
  have h := Finset.sum_le_sum (s := Finset.range n) (fun j _ => dyadic_decay_step hc j)
  rw [← Finset.mul_sum] at h
  have ht : (∑ j ∈ Finset.range n, (1/(1+c*2^j)-1/(1+c*2^(j+1)))) =
      1/(1+c) - 1/(1+c*2^n) := by
    have hh := Finset.sum_range_sub (fun j => (1 : ℝ)/(1+c*2^j)) n
    rw [Finset.sum_sub_distrib] at hh ⊢
    simp only [pow_zero,mul_one] at hh
    linarith
  rw [ht] at h
  have hc0 : 0 ≤ 2/c := by positivity
  have hfirst : 1/(1+c) ≤ (1 : ℝ) := (div_le_one (by positivity)).mpr (by linarith)
  have hlast : (0 : ℝ) ≤ 1/(1+c*2^n) := by positivity
  exact h.trans ((mul_le_mul_of_nonneg_left (by linarith : 1/(1+c)-1/(1+c*2^n) ≤ 1) hc0).trans_eq (mul_one _))

lemma dyadic_decay_summable {c : ℝ} (hc : 0 < c) :
    Summable (fun j : ℕ => (2 : ℝ)^j/(1+c*2^j)^2) :=
  summable_of_sum_range_le (fun _ => by positivity) (dyadic_decay_partial_sum hc)

lemma dyadic_decay_tsum {c : ℝ} (hc : 0 < c) :
    (∑' j : ℕ, (2 : ℝ)^j/(1+c*2^j)^2) ≤ 2/c := by
  exact (dyadic_decay_summable hc).tsum_le_of_sum_range_le (dyadic_decay_partial_sum hc)

end CubicFirstMoment

namespace CubicFirstMoment

def coprimeGramForm (S : Finset Eisenstein) (u : Eisenstein → ℂ)
    (W : ℝ → ℂ) (Z : ℝ) : ℂ :=
  ∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then
    u a * star (u b) * primaryCharacterGram a b W Z else 0

lemma hasSum_coprimePoissonDyad (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a ∧ ¬ IsUnit a)
    (u : Eisenstein → ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {Z : ℝ} (hZ : 0 < Z) :
    HasSum (fun j : ℕ => coprimePoissonDyad S (frequencyDyad j) u W Z)
      (coprimeGramForm S u W Z) := by
  unfold coprimePoissonDyad coprimeGramForm
  apply hasSum_sum
  intro a ha
  apply hasSum_sum
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab]
    have hne : a ≠ b := by
      intro he
      exact (hS a ha).2.2 (isCoprime_self.mp (he ▸ hab))
    have hf := (hasSum_frequencyDyad (gramDualTerm a b W Z)
      (summable_gramDualTerm (hS a ha).1 (hS b hb).1 W hW hW' hZ)
      (gramDualTerm_zero (hS a ha).1 (hS b hb).1 (hS a ha).2.1 (hS b hb).2.1 hab hne W Z)).mul_left
      (u a*star (u b)*((Z/(9*Real.sqrt (norm (a*b))) : ℝ) : ℂ)*(gauss a*star (gauss b)))
    convert hf using 1; try rfl
    rw [primaryCharacterGram_poisson_normalized (hS a ha).1 (hS b hb).1
      (hS a ha).2.1 (hS b hb).2.1 hab W hW hW' hZ]
    ring
  · simp only [ite_eq_right hab]
    exact hasSum_zero

lemma frequencyDyad_card_le (j : ℕ) :
    ((frequencyDyad j).card : ℝ) ≤ 36*(2 : ℝ)^j := by
  have hs : frequencyDyad j ⊆ nonzeroNormBall ((2 : ℝ)^(j+1)) := Finset.filter_subset _ _
  have hh : ((frequencyDyad j).card : ℝ) ≤ (nonzeroNormBall ((2 : ℝ)^(j+1))).card := by
    exact_mod_cast Finset.card_le_card hs
  exact hh.trans ((nonzeroNormBall_card_le (by positivity)).trans_eq (by rw [pow_succ]; ring))

theorem coprimeGramForm_base_bound (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein),
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ ¬ IsUnit a) →
      ∀ (u : Eisenstein → ℂ) (Z N : ℝ), 0 < Z → 0 < N →
      (∀ a ∈ S, N ≤ norm a ∧ norm a ≤ Real.sqrt 2*N) →
      ‖coprimeGramForm S u W Z‖ ≤ C*N*S.card*
        ∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖u a‖^2 := by
  obtain ⟨C,hC,hbound⟩ := coprimePoissonDyad_norm_recurrence W hW hW' 2
  refine ⟨1944*C,by positivity,?_⟩
  intro S hS u Z N hZ hN hSN
  let E : ℝ := ∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖u a‖^2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun a _ => by positivity)
  let c : ℝ := Z/(27*N^2)
  have hc : 0 < c := by dsimp [c]; positivity
  let D : ℝ := 36*C*(Z/N)*S.card*E
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hterm (j : ℕ) : ‖coprimePoissonDyad S (frequencyDyad j) u W Z‖ ≤
      D*((2 : ℝ)^j/(1+c*2^j)^2) := by
    have hj : 0 < (2 : ℝ)^j := by positivity
    have hd : 0 < (1+c*2^j)^2 := by positivity
    have hrec := hbound S (frequencyDyad j) (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩)
      u Z ((2 : ℝ)^j) N hZ.le hj hN hSN (fun h hh => frequencyDyad_norm hh)
    have he : Z*2^j/(27*N^2) = c*2^j := by dsimp [c]; ring
    rw [he] at hrec
    have hb : finiteCubicBound S (frequencyDyad j) ≤ 36*S.card*(2 : ℝ)^j := by
      exact (finiteCubicBound_le_card_mul S _ (fun a ha => (hS a ha).1)).trans
        ((mul_le_mul_of_nonneg_left (frequencyDyad_card_le j) (by positivity)).trans_eq (by ring))
    calc
      _ ≤ C*(Z/N)*finiteCubicBound S (frequencyDyad j)*E/(1+c*2^j)^2 := by
        apply (le_div_iff₀ hd).mpr
        simpa only [mul_comm, E] using hrec
      _ ≤ C*(Z/N)*(36*S.card*2^j)*E/(1+c*2^j)^2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hb (by positivity)) hE) hd.le
      _ = _ := by dsimp [D]; ring
  have hmajor := (dyadic_decay_summable hc).mul_left D
  have hsum := hasSum_coprimePoissonDyad S hS u W hW hW' hZ
  calc
    _ = ‖∑' j : ℕ, coprimePoissonDyad S (frequencyDyad j) u W Z‖ := by rw [hsum.tsum_eq]
    _ ≤ ∑' j : ℕ, ‖coprimePoissonDyad S (frequencyDyad j) u W Z‖ := norm_tsum_le_tsum_norm hsum.summable.norm
    _ ≤ ∑' j : ℕ, D*((2 : ℝ)^j/(1+c*2^j)^2) :=
      Summable.tsum_le_tsum (fun j => hterm j) hsum.summable.norm hmajor
    _ = D*(∑' j : ℕ, (2 : ℝ)^j/(1+c*2^j)^2) := tsum_mul_left
    _ ≤ D*(2/c) := mul_le_mul_of_nonneg_left (dyadic_decay_tsum hc) hD
    _ = _ := by
      dsimp [D,c,E]
      field_simp
      ring

end CubicFirstMoment
end
end

end OAI
