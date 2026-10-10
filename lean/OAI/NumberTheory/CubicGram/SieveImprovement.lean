import Mathlib
import OAI.NumberTheory.CubicGram.QuantitativeRecurrence

namespace OAI

/-! Amplification, iteration to exponent four-thirds and the cubic large sieve. -/

section

noncomputable section
namespace CubicFirstMoment

def sieveImprove (ξ : ℝ) : ℝ := (6*ξ-4)/(3*ξ-1)
def sieveAmplify (ξ : ℝ) : ℝ := (6*ξ-5)/(3*ξ-1)

lemma sieveImprove_properties {ξ : ℝ} (hξ : 4/3 ≤ ξ) (_hξ2 : ξ ≤ 2) :
    1 ≤ sieveAmplify ξ ∧ sieveAmplify ξ ≤ 2 ∧
    4/3 ≤ sieveImprove ξ ∧ sieveImprove ξ ≤ ξ ∧
    sieveAmplify ξ ≤ sieveImprove ξ ∧
    (2/3 : ℝ)*(sieveAmplify ξ+1) = sieveImprove ξ ∧
    sieveAmplify ξ*(1-ξ)+2*ξ-1 = sieveImprove ξ ∧
    sieveImprove ξ ≤ 4/3+(2/3 : ℝ)*(ξ-4/3) := by
  have hd : 0 < 3*ξ-1 := by linarith
  unfold sieveAmplify sieveImprove
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · apply (le_div_iff₀ hd).mpr; linarith
  · apply (div_le_iff₀ hd).mpr; linarith
  · apply (le_div_iff₀ hd).mpr; linarith
  · apply (div_le_iff₀ hd).mpr; nlinarith [sq_nonneg (3*ξ-4)]
  · apply div_le_div_of_nonneg_right _ hd.le; linarith
  · field_simp [ne_of_gt hd]; ring
  · apply (eq_div_iff (ne_of_gt hd)).mpr
    have he := div_mul_cancel₀ (6*ξ-5) (ne_of_gt hd)
    nlinarith [congrArg (fun x : ℝ => x*(ξ-1)) he]
  · apply (div_le_iff₀ hd).mpr; nlinarith [sq_nonneg (3*ξ-4)]

lemma sieve_amplification_numerical {ξ M N : ℝ} (hξ : 4/3 ≤ ξ) (hξ2 : ξ ≤ 2)
    (hN : 1 ≤ N) (hNM : N ≤ M) :
    sieveRecurrenceShape ξ (max M (N^sieveAmplify ξ)) N ≤
      4*(M+(M*N)^(2/3 : ℝ)+N^sieveImprove ξ) := by
  obtain ⟨ha,ha2,hf,hfξ,haf,hafid,herrid,hcon⟩ := sieveImprove_properties hξ hξ2
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hM0 : 0 < M := hN0.trans_le hNM
  have hP : 0 < max M (N^sieveAmplify ξ) := hM0.trans_le (le_max_left _ _)
  have hfirst : max M (N^sieveAmplify ξ) ≤ M+N^sieveImprove ξ := by
    apply max_le
    · exact le_add_of_nonneg_right (by positivity)
    · exact (Real.rpow_le_rpow_of_exponent_le hN haf).trans (le_add_of_nonneg_left hM0.le)
  have hmixed : (max M (N^sieveAmplify ξ)*N)^(2/3 : ℝ) ≤ (M*N)^(2/3 : ℝ)+N^sieveImprove ξ := by
    rw [max_mul_of_nonneg _ _ hN0.le,Real.rpow_max (by positivity) (by positivity) (by norm_num)]
    have he : (N^sieveAmplify ξ*N)^(2/3 : ℝ) = N^sieveImprove ξ := by
      rw [← Real.rpow_add_one hN0.ne',← Real.rpow_mul hN0.le]
      congr 1
      nlinarith [hafid]
    rw [he]
    exact max_le_add_of_nonneg (by positivity) (by positivity)
  have herr : (max M (N^sieveAmplify ξ))^(1-ξ)*N^(2*ξ-1) ≤ N^sieveImprove ξ := by
    calc
      _ ≤ (N^sieveAmplify ξ)^(1-ξ)*N^(2*ξ-1) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos (by positivity)
          (le_max_right _ _) (by linarith)) (by positivity)
      _ = N^sieveImprove ξ := by
        rw [← Real.rpow_mul hN0.le,← Real.rpow_add hN0]
        congr 1
        linarith
  have hNf : N ≤ N^sieveImprove ξ := by
    calc
      _ = N^(1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hmix0 : 0 ≤ (M*N)^(2/3 : ℝ) := by positivity
  unfold sieveRecurrenceShape
  linarith

lemma sieve_amplification_size {ξ M N : ℝ} (hξ : 4/3 ≤ ξ) (hξ2 : ξ ≤ 2)
    (hN : 1 ≤ N) (hNM : N ≤ M) :
    max M (N^sieveAmplify ξ)*N ≤ (M*N)^2 := by
  have hM1 : 1 ≤ M := hN.trans hNM
  have hN0 : 0 ≤ N := (zero_lt_one.trans_le hN).le
  have hM0 : 0 ≤ M := (zero_lt_one.trans_le hM1).le
  have ha2 := (sieveImprove_properties hξ hξ2).2.1
  have hp : max M (N^sieveAmplify ξ) ≤ M^2 := by
    apply max_le
    · nlinarith
    · calc
        _ ≤ N^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN ha2
        _ = N^2 := Real.rpow_two _
        _ ≤ M^2 := by gcongr
  calc
    _ ≤ M^2*N := mul_le_mul_of_nonneg_right hp hN0
    _ ≤ (M*N)^2 := by nlinarith [mul_nonneg (sq_nonneg M) (show 0 ≤ N^2-N by nlinarith)]

end CubicFirstMoment
end
end

section

noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma SieveExponent.improve {ξ : ℝ} (hξ : 4/3 ≤ ξ) (hξ2 : ξ ≤ 2)
    (hExp : SieveExponent ξ) : SieveExponent (sieveImprove ξ) := by
  intro ε hε
  obtain ⟨C,hC,hrec⟩ := hExp.recurrence (by linarith : 1 ≤ ξ) hξ2 (half_pos hε)
  have hf : 1 ≤ sieveImprove ξ := by have := (sieveImprove_properties hξ hξ2).2.2.1; linarith
  have hordered : ∀ S H : Finset Eisenstein, ∀ M N : ℝ, 1 ≤ N → N ≤ M →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ b ∈ H, primary b ∧ Squarefree b ∧ norm b ≤ M) →
      finiteCubicBound S H ≤ (4*C)*(M*N)^ε*(M+(M*N)^(2/3 : ℝ)+N^sieveImprove ξ) := by
    intro S H M N hN hNM hS hH
    let P : ℝ := max M (N^sieveAmplify ξ)
    have hMP : M ≤ P := le_max_left _ _
    have hNP : N ≤ P := hNM.trans hMP
    have hM0 : 0 < M := (zero_lt_one.trans_le hN).trans_le hNM
    have hN0 : 0 < N := zero_lt_one.trans_le hN
    have hP0 : 0 < P := hM0.trans_le hMP
    have hb := hrec S H P N hN hNP hS (fun b hb => ⟨(hH b hb).1,(hH b hb).2.2.trans hMP⟩)
    have hp : (P*N)^(ε/2) ≤ (M*N)^ε := by
      calc
        _ ≤ ((M*N)^2)^(ε/2) := Real.rpow_le_rpow (by positivity)
          (sieve_amplification_size hξ hξ2 hN hNM) (half_pos hε).le
        _ = (M*N)^ε := by
          rw [← Real.rpow_natCast_mul (by positivity)]
          congr 1
          ring
    have hs := sieve_amplification_numerical hξ hξ2 hN hNM
    exact hb.trans ((mul_le_mul (mul_le_mul_of_nonneg_left hp hC.le) hs
      (sieveRecurrenceShape_nonneg hP0.le hN0.le) (by positivity)).trans_eq (by ring))
  refine ⟨8*C,by positivity,?_⟩
  intro S H M N hM hN hS hH
  have hM0 : 0 ≤ M := (zero_lt_one.trans_le hM).le
  have hN0 : 0 ≤ N := (zero_lt_one.trans_le hN).le
  by_cases hNM : N ≤ M
  · exact (hordered S H M N hN hNM hS hH).trans (by gcongr; linarith)
  · have hMN : M ≤ N := le_of_not_ge hNM
    rw [finiteCubicBound_symm S H (fun a ha => (hS a ha).1) (fun b hb => (hH b hb).1)]
    have hb := hordered H S N M hM hMN hH hS
    have hNpow : N ≤ N^sieveImprove ξ := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN hf
    have hMpow : M^sieveImprove ξ ≤ N^sieveImprove ξ := Real.rpow_le_rpow hM0 hMN (by linarith)
    have hs : N+(M*N)^(2/3 : ℝ)+M^sieveImprove ξ ≤
        2*(M+(M*N)^(2/3 : ℝ)+N^sieveImprove ξ) := by
      have hp : 0 ≤ (M*N)^(2/3 : ℝ) := by positivity
      linarith
    rw [mul_comm N M] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by ring))

lemma SieveExponent.contract {ξ : ℝ} (hξ : 4/3 ≤ ξ) (hξ2 : ξ ≤ 2)
    (hExp : SieveExponent ξ) : SieveExponent (4/3+(2/3 : ℝ)*(ξ-4/3)) :=
  (hExp.improve hξ hξ2).mono (sieveImprove_properties hξ hξ2).2.2.2.2.2.2.2

end CubicFirstMoment
end
end

section

noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma sieveExponent_approach (n : ℕ) : SieveExponent (4/3+(2/3 : ℝ)^(n+1)) := by
  induction n with
  | zero => convert sieveExponent_two using 1; norm_num
  | succ n ih =>
    have hl : (4/3 : ℝ) ≤ 4/3+(2/3 : ℝ)^(n+1) := le_add_of_nonneg_right (by positivity)
    have hu : 4/3+(2/3 : ℝ)^(n+1) ≤ 2 := by
      have hh' : (2/3 : ℝ)^(n+1) ≤ 2/3 := by
        rw [pow_succ]
        exact mul_le_of_le_one_left (by norm_num) (pow_le_one₀ (n := n) (by norm_num) (by norm_num))
      linarith
    convert ih.contract hl hu using 1
    simp only [pow_succ]
    ring

theorem sieveExponent_four_thirds : SieveExponent (4/3) := by
  intro ε hε
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (2/3 : ℝ) < 1)
  have hn' : (2/3 : ℝ)^(n+1) ≤ ε/2 := by
    rw [pow_succ]
    exact (mul_le_of_le_one_right (by positivity) (by norm_num : (2/3 : ℝ) ≤ 1)).trans hn.le
  obtain ⟨C,hC,hbound⟩ := sieveExponent_approach n (ε/2) (half_pos hε)
  refine ⟨C,hC,?_⟩
  intro S H M N hM hN hS hH
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hMN : 1 ≤ M*N := one_le_mul_of_one_le_of_one_le hM hN
  have hNmn : N ≤ M*N := le_mul_of_one_le_left hN0.le hM
  have hpow1 : 1 ≤ (M*N)^(ε/2) := Real.one_le_rpow hMN (half_pos hε).le
  have hnpow : N^(4/3+(2/3 : ℝ)^(n+1)) ≤ (M*N)^(ε/2)*N^(4/3 : ℝ) := by
    calc
      _ ≤ N^(4/3+ε/2) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
      _ = N^(ε/2)*N^(4/3 : ℝ) := by rw [Real.rpow_add hN0]; ring
      _ ≤ _ := by gcongr
  have hm : M ≤ (M*N)^(ε/2)*M := le_mul_of_one_le_left hM0.le hpow1
  have hmix : (M*N)^(2/3 : ℝ) ≤ (M*N)^(ε/2)*(M*N)^(2/3 : ℝ) := le_mul_of_one_le_left (by positivity) hpow1
  have hs : M+(M*N)^(2/3 : ℝ)+N^(4/3+(2/3 : ℝ)^(n+1)) ≤
      (M*N)^(ε/2)*(M+(M*N)^(2/3 : ℝ)+N^(4/3 : ℝ)) := by nlinarith
  calc
    _ ≤ C*(M*N)^(ε/2)*(M+(M*N)^(2/3 : ℝ)+N^(4/3+(2/3 : ℝ)^(n+1))) := hbound S H M N hM hN hS hH
    _ ≤ C*(M*N)^(ε/2)*((M*N)^(ε/2)*(M+(M*N)^(2/3 : ℝ)+N^(4/3 : ℝ))) := by gcongr
    _ = C*(M*N)^ε*(M+(M*N)^(2/3 : ℝ)+N^(4/3 : ℝ)) := by
      have he : (M*N)^(ε/2)*(M*N)^(ε/2) = (M*N)^ε := by
        rw [← Real.rpow_add (by positivity),show ε/2+ε/2 = ε by ring]
      calc
        _ = C*((M*N)^(ε/2)*(M*N)^(ε/2))*(M+(M*N)^(2/3 : ℝ)+N^(4/3 : ℝ)) := by ring
        _ = _ := by rw [he]

lemma small_four_thirds_le_mixed {M N : ℝ} (hN : 0 ≤ N) (hNM : N ≤ M) :
    N^(4/3 : ℝ) ≤ (M*N)^(2/3 : ℝ) := by
  calc
    _ = (N*N)^(2/3 : ℝ) := by
      rw [← pow_two,← Real.rpow_natCast_mul hN]
      norm_num
    _ ≤ _ := by gcongr

theorem finiteCubicBound_sharp :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (S H : Finset Eisenstein) (M N : ℝ), 1 ≤ M → 1 ≤ N →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ b ∈ H, primary b ∧ Squarefree b ∧ norm b ≤ M) →
      finiteCubicBound S H ≤ C*(M*N)^ε*(M+N+(M*N)^(2/3 : ℝ)) := by
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := sieveExponent_four_thirds ε hε
  refine ⟨2*C,by positivity,?_⟩
  intro S H M N hM hN hS hH
  have hM0 : 0 ≤ M := (zero_lt_one.trans_le hM).le
  have hN0 : 0 ≤ N := (zero_lt_one.trans_le hN).le
  have hmixed : 0 ≤ (M*N)^(2/3 : ℝ) := by positivity
  rcases le_total N M with hNM | hMN
  · have hs := small_four_thirds_le_mixed hN0 hNM
    have hh : M+(M*N)^(2/3 : ℝ)+N^(4/3 : ℝ) ≤ 2*(M+N+(M*N)^(2/3 : ℝ)) := by linarith
    exact (hbound S H M N hM hN hS hH).trans ((mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring))
  · rw [finiteCubicBound_symm S H (fun a ha => (hS a ha).1) (fun b hb => (hH b hb).1)]
    have hs := small_four_thirds_le_mixed hM0 hMN
    rw [mul_comm N M] at hs
    have hh : N+(M*N)^(2/3 : ℝ)+M^(4/3 : ℝ) ≤ 2*(M+N+(M*N)^(2/3 : ℝ)) := by linarith
    have hb := hbound H S N M hN hM hH hS
    rw [mul_comm N M] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring))

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def squarefreePrimaryBall (X : ℝ) : Finset Eisenstein :=
  (nonzeroNormBall X).filter (fun a => primary a ∧ Squarefree a)

lemma mem_squarefreePrimaryBall {a : Eisenstein} {X : ℝ} :
    a ∈ squarefreePrimaryBall X ↔ primary a ∧ Squarefree a ∧ norm a ≤ X := by
  simp only [squarefreePrimaryBall, Finset.mem_filter, mem_nonzeroNormBall]
  constructor
  · rintro ⟨⟨hn,h0⟩,hp,hs⟩; exact ⟨hp,hs,hn⟩
  · rintro ⟨hp,hs,hn⟩; exact ⟨⟨hn,primary_ne_zero hp⟩,hp,hs⟩

def cubicSieveMass (A B : ℝ) (u : Eisenstein → ℂ) : ℝ :=
  ∑ a ∈ squarefreePrimaryBall A,
    ‖∑ b ∈ squarefreePrimaryBall B, u b * cubicSymbol a b‖^2

def CubicLargeSieveStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (A B : ℝ) (u : Eisenstein → ℂ),
    1 ≤ A → 1 ≤ B →
    cubicSieveMass A B u ≤ C * (A*B)^ε * (A+B+(A*B)^(2/3 : ℝ)) *
      ∑ b ∈ squarefreePrimaryBall B, ‖u b‖^2

theorem cubicLargeSieve : CubicLargeSieveStatement := by
  intro ε hε
  obtain ⟨C,hC,hsharp⟩ := finiteCubicBound_sharp ε hε
  refine ⟨C,hC,?_⟩
  intro A B u hA hB
  have hb := hsharp (squarefreePrimaryBall B) (squarefreePrimaryBall A) A B hA hB
    (fun b hb => mem_squarefreePrimaryBall.mp hb) (fun a ha => mem_squarefreePrimaryBall.mp ha)
  have hm := finiteCubicBound_controls_mass (squarefreePrimaryBall B) (squarefreePrimaryBall A) u
  have he : cubicSieveMass A B u = ∑ a ∈ squarefreePrimaryBall A,
      ‖∑ b ∈ squarefreePrimaryBall B, u b*cubicSymbol b a‖^2 := by
    unfold cubicSieveMass
    apply Finset.sum_congr rfl
    intro a ha
    congr 2
    apply Finset.sum_congr rfl
    intro b hb
    rw [cubic_reciprocity (mem_squarefreePrimaryBall.mp ha).1 (mem_squarefreePrimaryBall.mp hb).1]
  rw [he]
  exact hm.trans (mul_le_mul_of_nonneg_right hb (by positivity))

end CubicFirstMoment
end
end

end OAI
