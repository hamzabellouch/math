import OAI.NumberTheory.JointDickman.Amplification.AuxiliaryRangeScales
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeBandExtractionCost

namespace OAI

/-! # Exceptional energy on an actual power-scale auxiliary band -/
namespace JointDickman
open Finset Filter MeasureTheory TwoPointCorrelations
open scoped Classical Topology

noncomputable def auxiliarySquareError (α X : ℝ) : ℝ :=
  11264*Real.exp 1*(2/X^α+(2/X^α)^2)

lemma auxiliarySquareError_tendsto {α : ℝ} (hα : 0 < α) :
    Tendsto (auxiliarySquareError α) atTop (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop hα)).const_mul 2
  have hh := (h.add (h.pow 2)).const_mul (11264*Real.exp 1)
  unfold auxiliarySquareError
  simpa only [Function.comp_apply,div_eq_mul_inv,mul_zero,
    zero_pow (by omega : (2:ℕ)≠0),add_zero] using hh

theorem auxiliary_power_energy (P₀ Q₀ H : ℝ)
    (hP₀ : 2*Real.exp 1 ≤ P₀) (hPQ : P₀ ≤ Q₀)
    (hlogP : 1 ≤ Real.log P₀) (hQ₀ : 1 ≤ Real.log Q₀)
    (hH₀ : 2 ≤ mrtBaseResolution P₀ Q₀ (1/12)) (hH : 2 ≤ H)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβ : β < 1/12) :
    ∃ D : ℝ, 0 < D ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      let P := mrtPrimeBand ((N:ℝ)^α) ((N:ℝ)^β)
      let K := auxiliaryLogBins H α β N
      let J := mellinBandCount Q₀ (Real.sqrt (Real.log (N:ℝ))) hQ₀
      let B := canonicalMellinBands P₀ Q₀ (1/12)
      ∀ (F : ℕ → ℂ), Multiplicative F → (∀ n, ‖F n‖ ≤ 1) →
      ∀ (E : Set ℝ) (T b : ℝ), MeasurableSet E → 0 < T → T ≤ N →
      E ⊆ Set.Ioc (-T) T → E ⊆ mrtNoSmallBand B.bins (B.polynomial F) B.threshold J →
      (∀ k ∈ K, ∀ t ∈ E, ‖mrtCofactorPolynomial P F N (mrtPrimeLogLower H k) t‖ ≤ b) →
      (∫ t in E, ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2) ≤
        ε+22528*Real.exp 1/H+D*b^2+
        48*Real.exp 1*(((Ioc N (2*N)).filter (mrtPrimeAvoids P)).card:ℝ)/N := by
  have hB : 1 ≤ 4/α := (le_div_iff₀ hα).mpr (by linarith)
  obtain ⟨C,A,hC,hA,henergy⟩ := auxiliary_exceptional_energy P₀ Q₀ (4/α)
    hP₀ hPQ hlogP hQ₀ hH₀ hB
  let L := H*β+1
  have hL : 0 < L := by dsimp [L]; nlinarith
  let D := 8*L^2*C/(α/2)^2
  refine ⟨D,by dsimp [D]; positivity,?_⟩
  intro ε hε
  have herr := (auxiliarySquareError_tendsto hα).add
    ((auxiliaryVanishingCost_tendsto (mrtBaseResolution P₀ Q₀ (1/12)) L (α/2) hβ).const_mul 8)
  simp only [mul_zero,add_zero] at herr
  have hevent := henergy.filter_mono tendsto_natCast_atTop_atTop
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop 1)
  have hprime := ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop 2)
  have hsmall := (herr.eventually (eventually_lt_nhds hε)).filter_mono tendsto_natCast_atTop_atTop
  filter_upwards [hevent,auxiliary_range_scales A hα (show β<1 by linarith),
    auxiliary_cost_sum_bound C (mrtBaseResolution P₀ Q₀ (1/12)) L hC.le
      (mrtBaseResolution_pos _ _ _).le hα,hlog,hprime,hsmall,
    eventually_ge_atTop (2:ℕ)] with N hevent hrange hcost hlog hprime hsmall hN
  dsimp only at hevent ⊢
  intro F hF hFb E T b hEm hT hTN hET hEres hb
  let P := mrtPrimeBand ((N:ℝ)^α) ((N:ℝ)^β)
  let K := auxiliaryLogBins H α β N
  have hn : (0:ℝ)<N := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0<2) hN
  have hn1 : (1:ℝ)≤N := by exact_mod_cast le_trans (by norm_num : 1≤2) hN
  have heps := mrt_prime_log_width hH
  have hend k (hk : k∈K) := auxiliary_log_bins_endpoints (show 1≤H by linarith)
    (show 0≤β by linarith) hn1 hk
  have hr k (hk : k∈K) := hrange (mrtPrimeLogLower H k) (hend k hk).1 (hend k hk).2
  have hbound := hevent N P K (mrtPrimeLogBin H) (mrtPrimeLogLower H) (Real.exp (1/H))
    (by omega) (fun _ hp => mrtPrimeBand_prime hp)
    (fun _ hp => auxiliary_log_bins_mem (by linarith) hn hp) heps.1 heps.2.1
    (fun p hp => mrt_prime_log_bin_bounds (by linarith) (mrtPrimeBand_prime hp).one_le)
    (fun k hk => ⟨(hr k hk).1,(hr k hk).2.2.1⟩) F hF hFb E T b hEm hT hTN hET hEres
    (fun k hk => (show 2*T≤2*(N:ℝ) by linarith).trans (hr k hk).2.2.2) hb
  have hc := hcost K (mrtPrimeLogLower H) T b
    (auxiliary_log_bins_card (by linarith) (show 0≤β by linarith) hn hlog) hT.le hTN hend
  have hpq : (N:ℝ)^α ≤ (N:ℝ)^β := Real.rpow_le_rpow_of_exponent_le hn1 hαβ
  have hs := primeBand_square_mass_le hprime hpq
  change (∑ p ∈ P,1/(p:ℝ)^2) ≤ 2/(N:ℝ)^α at hs
  have hs0 : 0 ≤ ∑ p ∈ P,1/(p:ℝ)^2 := sum_nonneg (fun _ _ => by positivity)
  have hratio : T/(N:ℝ) ≤ 1 := (div_le_one hn).mpr hTN
  have hbase : 5632*Real.exp 1*(T/N+1)*
      ((∑ p ∈ P,1/(p:ℝ)^2)+(∑ p ∈ P,1/(p:ℝ)^2)^2+(Real.exp (1/H)-1)) ≤
      auxiliarySquareError α N+22528*Real.exp 1/H := by
    calc
      _ ≤ 11264*Real.exp 1*(2/(N:ℝ)^α+(2/(N:ℝ)^α)^2+2/H) := by
        apply mul_le_mul
        · calc
            _ ≤ 5632*Real.exp 1*2 := mul_le_mul_of_nonneg_left
              (by linarith only [hratio]) (by positivity)
            _ = _ := by ring
        · exact add_le_add (add_le_add hs (pow_le_pow_left₀ hs0 hs 2)) heps.2.2
        · exact add_nonneg (add_nonneg hs0 (sq_nonneg _)) (sub_nonneg.mpr heps.1)
        · positivity
      _ = _ := by dsimp [auxiliarySquareError]; ring
  have hbad : 16*Real.exp 1*(T/N+2)*
      (((Ioc N (2*N)).filter (mrtPrimeAvoids P)).card:ℝ)/N ≤
      48*Real.exp 1*(((Ioc N (2*N)).filter (mrtPrimeAvoids P)).card:ℝ)/N := by
    have hcoef : 16*Real.exp 1*(T/N+2) ≤ 48*Real.exp 1 := by
      calc
        _ ≤ 16*Real.exp 1*3 := mul_le_mul_of_nonneg_left
          (by linarith only [hratio]) (by positivity)
        _ = _ := by ring
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)) hn.le
  have hmul := mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ)≤8)
  change (∫ t in E, ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2) ≤
    ε+22528*Real.exp 1/H+D*b^2+
      48*Real.exp 1*(((Ioc N (2*N)).filter (mrtPrimeAvoids P)).card:ℝ)/N
  change auxiliarySquareError α N+
    8*auxiliaryVanishingCost (mrtBaseResolution P₀ Q₀ (1/12)) L (α/2) β N<ε at hsmall
  calc
    _ ≤ _ := hbound
    _ ≤ (auxiliarySquareError α N+22528*Real.exp 1/H)+
        8*(auxiliaryVanishingCost (mrtBaseResolution P₀ Q₀ (1/12)) L (α/2) β N+
          L^2*b^2*C/(α/2)^2)+
        48*Real.exp 1*(((Ioc N (2*N)).filter (mrtPrimeAvoids P)).card:ℝ)/N :=
      add_le_add (add_le_add hbase (by simpa only [mul_assoc] using hmul)) hbad
    _ = (auxiliarySquareError α N+
        8*auxiliaryVanishingCost (mrtBaseResolution P₀ Q₀ (1/12)) L (α/2) β N)+
        22528*Real.exp 1/H+D*b^2+
        48*Real.exp 1*(((Ioc N (2*N)).filter (mrtPrimeAvoids P)).card:ℝ)/N := by
      dsimp only [D]
      ring
    _ ≤ _ := by gcongr

end JointDickman

end OAI
