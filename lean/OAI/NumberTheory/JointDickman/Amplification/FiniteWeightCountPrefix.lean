import OAI.NumberTheory.JointDickman.Arithmetic.FixedDivisorLogScale
import OAI.NumberTheory.JointDickman.Amplification.FiniteWeightPhase

namespace OAI

/-! # Reciprocal-count cancellation after fixed finite-prime weighting -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Topology Classical

theorem finite_weight_count_prefix {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ᶠ N : ℕ in atTop,
      ∀ f : ArithmeticFunction ℂ, f.IsMultiplicative → (∀ n, ‖f n‖ ≤ 1) →
      (∀ p k : ℕ, p.Prime → (p:ℝ) ≤ (N:ℝ)^c → p^k ≤ N → f (p^k) = 1) →
      (∀ D ∈ E.powerset, ∀ n : ℕ, 0 < n → f ((∏ p ∈ D, p)*n) = f n) →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ (N:ℝ)^c < (p:ℝ)) → Disjoint E P →
      ∀ w : ℕ → ℝ, (∀ p ∈ E, 0 ≤ w p ∧ w p ≤ 1) →
      ∀ t : ℝ, T ≤ |t| → |t| ≤ 3*(Real.log N)^8 →
      ‖∑ n ∈ Icc 1 N, (f n*(finitePrimeWeight E w n:ℂ)*halaszPowerPhase t n)/
        ((finitePrimeDivisorCount P n:ℂ)+1)‖/(N:ℝ) ≤ ε := by
  let C : ℝ := E.powerset.card
  have hC : 0 < C := by dsimp [C]; exact_mod_cast (card_pos.mpr ⟨∅,empty_mem_powerset E⟩)
  let δ := ε/C
  have hδ : 0 < δ := div_pos hε hC
  obtain ⟨T,hT,hprefix⟩ := rough_count_prefix_unrestricted hc hc1 hδ
  refine ⟨T,hT,?_⟩
  have hlocals : ∀ D ∈ E.powerset, ∀ᶠ N : ℕ in atTop,
      (1 ≤ N/(∏ p ∈ D,p) ∧ 3*(Real.log N)^8 ≤ 4*(Real.log (N/(∏ p ∈ D,p):ℕ))^8) ∧
      ∀ (f : ArithmeticFunction ℂ) (P : Finset ℕ),
      f.IsMultiplicative → (∀ n, ‖f n‖ ≤ 1) →
      (∀ p k : ℕ, p.Prime → (p:ℝ) ≤ (N/(∏ p ∈ D,p):ℕ)^c →
        p^k ≤ N/(∏ p ∈ D,p) → f (p^k) = 1) →
      (∀ p ∈ P, p.Prime ∧ (N/(∏ p ∈ D,p):ℕ)^c < (p:ℝ)) →
      ∀ t : ℝ, T ≤ |t| → |t| ≤ 4*(Real.log (N/(∏ p ∈ D,p):ℕ))^8 →
        ‖∑ n ∈ Icc 1 (N/(∏ p ∈ D,p)), (f n*halaszPowerPhase t n)/
          ((finitePrimeDivisorCount P n:ℂ)+1)‖/(N/(∏ p ∈ D,p):ℕ) ≤ δ := by
    intro D hD
    have hd : 0 < ∏ p ∈ D,p := prod_pos (fun p hp => (hE p (mem_powerset.mp hD hp)).pos)
    exact (fixed_divisor_logarithmic_window hd).and
      ((Nat.tendsto_div_const_atTop hd.ne').eventually hprefix)
  filter_upwards [(eventually_all_finset E.powerset).mpr hlocals,eventually_ge_atTop 1]
    with N hN hN1
  intro f hf hfb hsmall hinv P hP hdis w hw t htlo hthi
  have hNr : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  rw [finite_weight_count_phase_expansion E P hE (fun p hp => (hP p hp).1)
    hdis w f hinv]
  apply (div_le_iff₀ hNr).mpr
  calc
    _ ≤ ∑ D ∈ E.powerset, ‖((∏ p ∈ D, (w p-1):ℝ):ℂ)*
        halaszPowerPhase t (∏ p ∈ D, (p:ℝ))*
        ∑ n ∈ Icc 1 (N/(∏ p ∈ D,p)), (f n*halaszPowerPhase t n)/
          ((finitePrimeDivisorCount P n:ℂ)+1)‖ := norm_sum_le _ _
    _ ≤ ∑ _D ∈ E.powerset, δ*(N:ℝ) := by
      apply sum_le_sum
      intro D hD
      let k := N/(∏ p ∈ D,p)
      obtain ⟨⟨hk1,hkt⟩,hk⟩ := hN D hD
      have hkN : k ≤ N := Nat.div_le_self _ _
      have hkr : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
      have hkc : (k:ℝ)^c ≤ (N:ℝ)^c :=
        Real.rpow_le_rpow hkr.le (by exact_mod_cast hkN) hc.le
      have hb := hk f P hf hfb
        (fun p j hp hpc hpj => hsmall p j hp (hpc.trans hkc) (hpj.trans hkN))
        (fun p hp => ⟨(hP p hp).1,hkc.trans_lt (hP p hp).2⟩) t htlo (hthi.trans hkt)
      have hb' : ‖∑ n ∈ Icc 1 k, (f n*halaszPowerPhase t n)/
          ((finitePrimeDivisorCount P n:ℂ)+1)‖ ≤ δ*(N:ℝ) :=
        ((div_le_iff₀ hkr).mp hb).trans
          (mul_le_mul_of_nonneg_left (by exact_mod_cast hkN) hδ.le)
      have hwD : ‖((∏ p ∈ D, (w p-1):ℝ):ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real,Real.norm_eq_abs,abs_prod]
        apply prod_le_one₀ (fun _ _ => abs_nonneg _)
        intro p hp
        have hwP := hw p (mem_powerset.mp hD hp)
        apply abs_le.mpr
        constructor <;> linarith
      rw [norm_mul,norm_mul,halasz_power_phase_norm,mul_one]
      exact (mul_le_mul_of_nonneg_right hwD (norm_nonneg _)).trans (by simpa using hb')
    _ = ε*(N:ℝ) := by
      simp only [sum_const,nsmul_eq_mul]
      change C*(ε/C*N)=ε*N
      field_simp

end JointDickman

end OAI
