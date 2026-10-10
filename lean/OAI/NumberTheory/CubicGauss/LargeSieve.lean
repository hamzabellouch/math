import Mathlib
import OAI.NumberTheory.CubicGauss.Recurrence

namespace OAI

/-! Bootstrap to the sharp upper-cutoff cubic large-sieve inequality. -/

noncomputable section
open scoped BigOperators
open Module Complex UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma squarefreePrimaryBall_mono {M N : ℝ} (hMN : M≤ N) :
    squarefreePrimaryBall M ⊆ squarefreePrimaryBall N := by
  intro a ha
  obtain ⟨hp,hs,hn⟩ := mem_squarefreePrimaryBall.mp ha
  exact mem_squarefreePrimaryBall.mpr ⟨hp,hs,hn.trans hMN⟩

lemma cubic_power_bound_mono {α β : ℝ} (hαβ : α≤β) (hB : CubicPowerBound α) :
    CubicPowerBound β := by
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := hB ε hε
  refine ⟨C,hC,?_⟩
  intro M N S u hM hN hS
  apply (hbound M N S u hM hN hS).trans
  have hn := Real.rpow_le_rpow_of_exponent_le hN hαβ
  gcongr

 
theorem cubic_power_bound_step {α : ℝ} (hα : (4/3:ℝ)≤α) (hB : CubicPowerBound α) :
    CubicPowerBound (sieveStep α) := by
  intro ε hε
  obtain ⟨C,hC,hrec⟩ := cubic_recurrence (by linarith) hB ε hε
  refine ⟨4*C,by positivity,?_⟩
  intro M N S u hM hN hS
  have hM0 : 0≤ M := by linarith
  have hN0 : 0≤ N := by linarith
  have hE : 0≤∑ b ∈ S,‖u b‖^2 := Finset.sum_nonneg fun b _ => sq_nonneg _
  have hεN : N^ε≤(M*N)^ε :=
    Real.rpow_le_rpow hN0 (le_mul_of_one_le_left hN0 hM) hε.le
  have hstepN : 0≤ N^(sieveStep α) := Real.rpow_nonneg hN0 _
  have hmixed : 0≤(M*N)^(2/3:ℝ) := by positivity
  by_cases hlarge : N^(sieveThreshold α)≤ M
  · apply (hrec M N S u hM hN hS).trans
    have henv := recurrenceEnvelope_large hM hN hα hlarge
    calc
      _ ≤ C*(M*N)^ε*(M+3*(M*N)^(2/3:ℝ))*∑ b ∈ S,‖u b‖^2 := by
        gcongr
        exact recurrenceEnvelope_nonneg hM0 hN0
      _ ≤ _ := by
        have hh : M+3*(M*N)^(2/3:ℝ) ≤ 4*(M+N^(sieveStep α)+(M*N)^(2/3:ℝ)) := by linarith
        have hb := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hh (show 0≤ C*(M*N)^ε by positivity)) hE
        nlinarith only [hb]
  · have hsmall : M≤ N^(sieveThreshold α) := (lt_of_not_ge hlarge).le
    have hR : 1≤ N^(sieveThreshold α) := hM.trans hsmall
    apply (Finset.sum_le_sum_of_subset_of_nonneg (squarefreePrimaryBall_mono hsmall)
      (f := cubicRowEnergy S u) (fun m _ _ => cubicRowEnergy_nonneg S u m)).trans
    apply (hrec (N^(sieveThreshold α)) N S u hR hN hS).trans
    have henv := recurrenceEnvelope_threshold hN hα
    calc
      _ ≤ C*(M*N)^ε*(4*N^(sieveStep α))*∑ b ∈ S,‖u b‖^2 := by
        gcongr
        exact recurrenceEnvelope_nonneg (by positivity) hN0
      _ ≤ _ := by
        have hh : N^(sieveStep α) ≤ M+N^(sieveStep α)+(M*N)^(2/3:ℝ) := by linarith
        have hb := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hh (show 0≤4*C*(M*N)^ε by positivity)) hE
        nlinarith only [hb]

 

def sieveExponent (n : ℕ) : ℝ := (4/3:ℝ)+(2/3:ℝ)^(n+1)

lemma sieveExponent_ge (n : ℕ) : (4/3:ℝ)≤ sieveExponent n := by
  unfold sieveExponent
  exact le_add_of_nonneg_right (pow_nonneg (by norm_num) _)

lemma sieveExponent_succ (n : ℕ) : sieveStep (sieveExponent n)≤ sieveExponent (n+1) := by
  have hb := (sieveStep_algebra (sieveExponent_ge n)).2.2.2.2.2
  dsimp [sieveExponent] at hb ⊢
  rw [pow_succ (2/3:ℝ) (n+1)]
  linarith

 

theorem cubic_power_bound_exponent (n : ℕ) : CubicPowerBound (sieveExponent n) := by
  induction n with
  | zero => norm_num [sieveExponent]; exact cubic_power_bound_two
  | succ n hn =>
    exact cubic_power_bound_mono (sieveExponent_succ n)
      (cubic_power_bound_step (sieveExponent_ge n) hn)



 

theorem cubic_power_bound_four_thirds : CubicPowerBound (4/3:ℝ) := by
  intro ε hε
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one (show 0<ε/2 by positivity) (by norm_num : (2/3:ℝ)<1)
  have hδ : (2/3:ℝ)^(n+1)≤ε/2 := by
    rw [pow_succ]
    exact (mul_le_of_le_one_right (pow_nonneg (by norm_num : (0:ℝ)≤2/3) n) (by norm_num)).trans hn.le
  obtain ⟨C,hC,hbound⟩ := cubic_power_bound_exponent n (ε/2) (by positivity)
  refine ⟨C,hC,?_⟩
  intro M N S u hM hN hS
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hMN : 1≤M*N := one_le_mul_of_one_le_of_one_le hM hN
  have hMN0 : 0<M*N := mul_pos hM0 hN0
  have hE : 0≤∑ b ∈ S,‖u b‖^2 := Finset.sum_nonneg fun b _ => sq_nonneg _
  have hpow : 1≤(M*N)^(ε/2) := Real.one_le_rpow hMN (by positivity)
  have hNpow : N^((2/3:ℝ)^(n+1))≤(M*N)^(ε/2) := by
    apply (Real.rpow_le_rpow_of_exponent_le hN hδ).trans
    exact Real.rpow_le_rpow hN0.le (le_mul_of_one_le_left hN0.le hM) (by positivity)
  have hp : N^(sieveExponent n) ≤ (M*N)^(ε/2)*N^(4/3:ℝ) := by
    dsimp [sieveExponent]
    rw [Real.rpow_add hN0]
    simpa only [mul_comm _ (N^(4/3:ℝ))] using
      mul_le_mul_of_nonneg_left hNpow (Real.rpow_nonneg hN0.le (4/3))
  have he : M+N^(sieveExponent n)+(M*N)^(2/3:ℝ) ≤
      (M*N)^(ε/2)*(M+N^(4/3:ℝ)+(M*N)^(2/3:ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_right hpow hM0.le
    have h2 := mul_le_mul_of_nonneg_right hpow (show 0≤(M*N)^(2/3:ℝ) by positivity)
    nlinarith
  apply (hbound M N S u hM hN hS).trans
  calc
    _ ≤ C*(M*N)^(ε/2)*((M*N)^(ε/2)*(M+N^(4/3:ℝ)+(M*N)^(2/3:ℝ)))*∑ b ∈ S,‖u b‖^2 := by
      apply mul_le_mul_of_nonneg_right _ hE
      exact mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by
      rw [←mul_assoc (C*(M*N)^(ε/2)),mul_assoc C,←Real.rpow_add hMN0,show ε/2+ε/2=ε by ring]

lemma short_four_thirds {M N : ℝ} (_ : 1≤M) (hN : 1≤N) (hNM : N≤M) :
    N^(4/3:ℝ) ≤ (M*N)^(2/3:ℝ) := by
  have hN0 : 0≤N := by linarith
  calc
    _ = (N^2)^(2/3:ℝ) := by rw [←Real.rpow_natCast_mul hN0]; norm_num
    _ ≤ _ := Real.rpow_le_rpow (sq_nonneg _) (by nlinarith) (by norm_num)

 

theorem sharp_cubic_sieve_operator (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (M N : ℝ) (S : Finset Eisenstein) (u : Eisenstein → ℂ),
      1≤M → 1≤N → S ⊆ squarefreePrimaryBall N →
      ∑ m ∈ squarefreePrimaryBall M,cubicRowEnergy S u m ≤
        C*(M*N)^ε*(M+N+(M*N)^(2/3:ℝ))*∑ b ∈ S,‖u b‖^2 := by
  obtain ⟨C,hC,hbound⟩ := cubic_power_bound_four_thirds ε hε
  refine ⟨2*C,by positivity,?_⟩
  intro M N S u hM hN hS
  have hM0 : 0≤M := by linarith
  have hN0 : 0≤N := by linarith
  have hE : 0≤∑ b ∈ S,‖u b‖^2 := Finset.sum_nonneg fun b _ => sq_nonneg _
  have hmix : 0≤(M*N)^(2/3:ℝ) := by positivity
  by_cases hNM : N≤M
  · have hp := short_four_thirds hM hN hNM
    have he : M+N^(4/3:ℝ)+(M*N)^(2/3:ℝ) ≤ 2*(M+N+(M*N)^(2/3:ℝ)) := by linarith
    apply (hbound M N S u hM hN hS).trans
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (show 0≤C*(M*N)^ε by positivity)) hE
    convert hh using 1
    ring
  · have hp := short_four_thirds hN hM (lt_of_not_ge hNM).le
    rw [mul_comm N M] at hp
    have he : N+M^(4/3:ℝ)+(M*N)^(2/3:ℝ) ≤ 2*(M+N+(M*N)^(2/3:ℝ)) := by linarith
    apply (cubic_power_bound_transposed hC.le hbound hM hN S hS u).trans
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (show 0≤C*(M*N)^ε by positivity)) hE
    convert hh using 1
    ring

 

theorem cubic_large_sieve : CubicLargeSieveStatement := by
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := sharp_cubic_sieve_operator ε hε
  refine ⟨C,hC,?_⟩
  intro A B u hA hB
  have hb := hbound A B (squarefreePrimaryBall B) u hA hB (Finset.Subset.refl _)
  have he : cubicSieveMass A B u = ∑ a ∈ squarefreePrimaryBall A,cubicRowEnergy (squarefreePrimaryBall B) u a := by
    unfold cubicSieveMass cubicRowEnergy
    apply Finset.sum_congr rfl
    intro a ha
    congr 2
    apply Finset.sum_congr rfl
    intro b hb
    rw [cubic_reciprocity (mem_squarefreePrimaryBall.mp ha).1 (mem_squarefreePrimaryBall.mp hb).1]
  rw [he]
  exact hb

end CubicFirstMoment
end

end OAI
