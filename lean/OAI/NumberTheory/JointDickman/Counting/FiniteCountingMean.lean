import OAI.NumberTheory.JointDickman.Counting.CountingSamplingScale
import OAI.NumberTheory.JointDickman.Counting.CountingPrefixMean
import OAI.NumberTheory.JointDickman.Counting.FiniteCountingComparison
import OAI.NumberTheory.JointDickman.Amplification.FiniteGraphFluctuation

namespace OAI

/-! # Cancellation of the original finite graph on its counting range -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem finite_graph_centered_mean
    (hMR : RealShortIntervalInput) (hMRT : ComplexShortIntervalInput)
    (hKMT : CharacterDistanceDivergence) (hFord : FordUpperSieveInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hM : PrimeReciprocalMertensInput) (hMP : PrimeProductMertensInput)
    (hMC : ∀ B M : ℕ, FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    {A L : ℕ} {cap : ℝ} (hA : 0 < A) (hL : 10000 ≤ L) (hcap : 0 < cap) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ cap ∧ τ ≤ samplingTau ∧
    ∀ ε : ℝ, 0 < ε → ∃ Cmin : ℝ, 0 ≤ Cmin ∧ ∀ C : ℝ, Cmin ≤ C →
    ∀ᶠ B : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
      let T := amplificationMultiplier B
      let z := fun n => binLabel (fun j : Fin (J-1) => primeBin (N : ℝ) J (j.val+1)) ζ n-μ
      (∑ u ∈ range (4*T*N), |(complexEnergy
        (finiteGraphKernel B L T (T/A) (A*T) N u τ C) (fun i => z (u+(i.val+1)))).re|/(A*T : ℕ)) /
          ((T : ℝ)*N) < ε := by
  obtain ⟨τ,hτ,hτcap,hτsmall,hsample⟩ := counting_sampling_actual_scale hFord hSD hSW hM hMP hMC hL hA hcap
  obtain ⟨E,hE,hfluct⟩ := finite_graph_arithmetic_fluctuation hFord hM (by omega : 1 ≤ L) hτ.le hτsmall
  obtain ⟨a,ha,hramp⟩ := finite_ramp_approximation hFord hM (by omega : 1 ≤ L) hτ.le hτsmall
  refine ⟨τ,hτ,hτcap,hτsmall,?_⟩
  intro ε hε
  let d := ε/1024
  have hd : 0 < d := by dsimp [d]; positivity
  let w := d/(a+1)
  have hw : 0 < w := by dsimp [w]; positivity
  have haw : a*w ≤ d := by
    apply (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one : a ≤ a+1) hw.le).trans_eq
    dsimp [w]
    field_simp
  obtain ⟨P,c,hc,D,m,hm,Cmin,Kerror,hCmin,hKerror,hs⟩ := hsample w d hw hd
  refine ⟨Cmin,hCmin,?_⟩
  intro C hC
  have hvalid : ∀ᶠ B : ℕ in atTop, 0 < amplificationMultiplier B ∧
      Real.log (amplificationMultiplier B : ℝ) ≤ (B : ℝ)/10 ∧
      (1/(2*(A : ℝ)))*amplificationMultiplier B ≤ ((amplificationMultiplier B/A : ℕ) : ℝ) := by
    filter_upwards [amplification_sampling_scale,counting_block_scale hA] with B ht hb
    exact ⟨ht.1,ht.2.2.2.2.1,hb.1⟩
  have hMp : ∀ᶠ B : ℕ in atTop, 0 < A*amplificationMultiplier B :=
    (amplification_sampling_scale).mono fun _ h => Nat.mul_pos hA h.1
  have hmodel := counting_model_prefix_mean hMR hMRT hKMT hM hSD hSW hMP hJ ζ hζ μ hμ hmean
    P m hm c (fun d => (hc d).1) D (by positivity : 0 < 1/(2*(A : ℝ))) (by norm_num : (0 : ℝ) < 4)
    (fun N : ℕ => (N : ℝ)) amplificationMultiplier (fun B => amplificationMultiplier B/A)
    countingSmoothingLength (fun B => A*amplificationMultiplier B) L τ C
    tendsto_natCast_atTop_atTop countingSmoothingLength_tendsto countingSmoothingLength_div_tendsto
    hvalid hMp d hd
  have hKlim := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) Kerror
  filter_upwards [hs,hfluct,hramp,hmodel,amplification_sampling_scale,
    amplification_block_size_le_square A,hMp,
    hE.eventually (Iio_mem_nhds hd),hKlim.eventually (Iio_mem_nhds hd),
    (show ∀ᶠ B : ℕ in atTop, (B : ℝ)^2 ≤ Real.exp B from by
      have hh := ((isLittleO_rpow_exp_pos_mul_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop
      filter_upwards [hh.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))] with B hb
      have hb' : (B : ℝ)^2/Real.exp B ≤ 1 := by simpa only [Function.comp_apply,one_mul,Real.rpow_two] using hb
      exact (div_le_one (Real.exp_pos (B : ℝ))).mp hb')] with B hs hf hr hmod ht hM2 hM0 he hk hMexp
  let T := amplificationMultiplier B
  have hT : 0 < T := ht.1
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hMb : ((A*T : ℕ) : ℝ) ≤ Real.exp B := (by exact_mod_cast hM2 : ((A*T : ℕ) : ℝ) ≤ (B : ℝ)^2).trans hMexp
  have hfl := hf C T (T/A) (A*T) hT ht.2.1 ht.2.2.1 hM0 hM2 hMb d hd
  have hfl' := (tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N (by omega : 0 < 4*T)) tendsto_id).eventually hfl
  filter_upwards [hs C hC (4*T) d hd,hr T (T/A) (A*T) C w hT ht.2.1 hM0 hM2 hw (4*T) d hd,
    hmod,hfl',eventually_gt_atTop 0] with N hsampleN hrampN hmodelN hflN hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hTN : 0 < (T : ℝ)*N := mul_pos hTr hNr
  let z := fun n => binLabel (fun j : Fin (J-1) => primeBin (N : ℝ) J (j.val+1)) ζ n-μ
  let S := range (4*T*N)
  let f := fun u => finiteGraphLatentError B L T (T/A) (A*T) N u τ C
  let r := fun u => finiteRampCutError B L T (T/A) (A*T) N u τ C w
  let s := fun u => countingArithmeticCutError P m B L T (T/A) (A*T) τ C w c D
    (countingOriginParameter T N u) u
  let q := fun u => |(complexEnergy (countingArithmeticKernel singularSeries P m B L T (T/A) (A*T) u τ C c D
    (countingOriginParameter T N u)) (fun i => z (u+(i.val+1)))).re|/((A*T : ℕ) : ℝ)
  have hfmean : (∑ u ∈ S, f u)/((T : ℝ)*N) < 8*d := by
    have hh := hflN N
    have heq : (∑ u ∈ S, f u)/((T : ℝ)*N) = 4*((∑ u ∈ S, f u)/((4*T*N : ℕ) : ℝ)) := by
      push_cast
      field_simp
    rw [heq]
    exact (mul_lt_mul_of_pos_left hh (by norm_num : (0 : ℝ) < 4)).trans_le (by linarith)
  have hrmean : (∑ u ∈ S, r u)/((T : ℝ)*N) < 2*d := by
    have hh := hrampN (4*T*N) le_rfl
    rw [show (∑ u ∈ S, r u)/((T : ℝ)*N) = ((∑ u ∈ S, r u)/(N : ℝ))/(T : ℝ) by ring]
    apply (div_lt_iff₀ hTr).mpr
    have hawT := mul_le_mul_of_nonneg_right haw hTr.le
    have hdT := mul_le_mul_of_nonneg_left hT1 hd.le
    change (∑ u ∈ S, r u)/(N : ℝ) < a*(T : ℝ)*w+d at hh
    nlinarith
  have hsmean : (∑ u ∈ S, s u)/((T : ℝ)*N) < 9*d := by
    rw [show (∑ u ∈ S, s u)/((T : ℝ)*N) = ((∑ u ∈ S, s u)/(N : ℝ))/(T : ℝ) by ring]
    apply (div_lt_iff₀ hTr).mpr
    have hh := mul_lt_mul_of_pos_left hk (mul_pos (by norm_num : (0 : ℝ) < 4) hTr)
    have hdT := mul_le_mul_of_nonneg_left hT1 hd.le
    change (∑ u ∈ S, s u)/(N : ℝ) < ((4*T : ℕ) : ℝ)*(d+Kerror/(B : ℝ))+d at hsampleN
    push_cast at hsampleN
    nlinarith
  have hqmean : (∑ u ∈ S, q u)/((T : ℝ)*N) < d := by
    have hh := hmodelN (countingOriginParameter T N) (countingOriginParameter_bound T N)
    have hfloor : ⌊(4 : ℝ)*T*N⌋₊ = 4*T*N := by
      have heq : (4 : ℝ)*T*N = ((4*T*N : ℕ) : ℝ) := by push_cast; ring
      rw [heq,Nat.floor_natCast]
    change (∑ u ∈ range ⌊(4 : ℝ)*T*N⌋₊, q u)/((T : ℝ)*N) < d at hh
    rwa [hfloor] at hh
  have hpoint (u : ℕ) := finite_graph_counting_energy_compare P m B L T (T/A) (A*T) N u τ C w c D
    hT hM0 hw (fun i => z (u+(i.val+1))) (fun i => norm_centered_binLabel_le_two _ ζ hζ μ hμ _)
  have hsum := div_le_div_of_nonneg_right (sum_le_sum (fun u (_ : u ∈ S) => hpoint u)) hTN.le
  have hsum' : (∑ u ∈ S, |(complexEnergy (finiteGraphKernel B L T (T/A) (A*T) N u τ C)
      (fun i => z (u+(i.val+1)))).re|/((A*T : ℕ) : ℝ))/((T : ℝ)*N) ≤
      (∑ u ∈ S, q u)/((T : ℝ)*N)+16*((∑ u ∈ S, f u)/((T : ℝ)*N)+
        (∑ u ∈ S, r u)/((T : ℝ)*N)+(∑ u ∈ S, s u)/((T : ℝ)*N)) := by
    change (∑ u ∈ S, |(complexEnergy (finiteGraphKernel B L T (T/A) (A*T) N u τ C)
      (fun i => z (u+(i.val+1)))).re|/((A*T : ℕ) : ℝ))/((T : ℝ)*N) ≤
      (∑ u ∈ S, (q u+16*(f u+r u+s u)))/((T : ℝ)*N) at hsum
    apply hsum.trans_eq
    rw [sum_add_distrib,← mul_sum,sum_add_distrib,sum_add_distrib]
    ring
  change _ < ε
  have hdε : 305*d < ε := by dsimp [d]; linarith
  linarith

end JointDickman

end OAI
