import OAI.NumberTheory.TwoPoint.Walks.CanonicalRawSelection
import OAI.NumberTheory.TwoPoint.Walks.SelectedRawBinsLower
import OAI.NumberTheory.TwoPoint.Walks.CanonicalComplexLimits
import OAI.NumberTheory.TwoPoint.Bounds.QualitativeCenteringTotal
import OAI.NumberTheory.TwoPoint.Bounds.PrimeDefectBias
import OAI.NumberTheory.TwoPoint.Bounds.QuantitativeFinalWindows

namespace OAI

/-! Conditional ordinary two-point cancellation. The only hypotheses beyond
the original multiplicative functions are the four cited published inputs. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical Topology

theorem conditional_complex_positive_core (hP : ModFiveThetaInput)
    (hBr : BravermanDepth22Input) (hM : PrimeReciprocalInput)
    (hMRT : MRTShortExponentialInput) {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    (hnp : UniformlyNonpretentious f ∨ UniformlyNonpretentious g)
    (h : ℕ) (hh : 0 < h) :
    Tendsto (fun N : ℕ => positivePrefix (fun n => f n * g (n + h)) N / (N : ℂ))
      atTop (𝓝 0) := by
  have hfb : OneBounded f := fun n _ => hf n
  have hgb : OneBounded g := fun n _ => hg n
  by_contra hn
  have hfail : ¬∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ‖positivePrefix (fun n => f n * g (n + h)) N / (N : ℂ)‖ < ε := by
    intro hall
    apply hn
    rw [Metric.tendsto_nhds]
    simpa only [dist_zero_right] using hall
  push Not at hfail
  obtain ⟨γ, hγ, hfreq⟩ := hfail
  obtain ⟨hsf, hsg⟩ := persistent_correlation_prime_defects hfm hgm hfb hgb h hn
  obtain ⟨hf1, hg1⟩ := persistent_correlation_one_values hfm hgm h hn
  obtain ⟨Ag, W, hAg, hW, hgraph⟩ := complex_graph_fixed_scale hP hBr
  have hWone : 1 ≤ W := by linarith
  have hWp : 0 < W := by linarith
  obtain ⟨E, hE, hselect⟩ := canonical_raw_pair_selection hP hfm hgm hf1 hg1 hfb hgb
    hsf hsg h hh W γ hWone hγ
  obtain ⟨Cg, hCg, hgraph⟩ := hgraph h hh E hE
  obtain ⟨Cc, hCc, hcenter⟩ := qualitative_canonical_nonraw_total hP hM hMRT
    hfm hgm hfb hgb hnp h hh E W hWone
  have hηsmall := (canonical_eta_tendsto_zero W hWp).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < γ / 128))
  have herrors := (canonical_complex_error_tendsto_zero W Cg Cc hWp).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < γ / 16))
  obtain ⟨L, hgraphL, hcenterL, hselectL, hmassL, hηL, herrL, hLlarge⟩ :=
    (hgraph.and (hcenter.and (hselect.and
      ((hP.eventually_canonical_retained_mass E W hWone).and
        (hηsmall.and (herrors.and (eventually_ge_atTop (2 : ℝ)))))))).exists
  have hL : 1 ≤ L := by linarith
  let J := primeSupplyCount W L
  let η := Real.exp (-(J : ℝ))
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Q := paddingPrimeSupply E L
  let R := boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊
  let D := primeTupleDivisors P
  let S₀ := totalPaddingBinMass D Q L η
  let M := paddingTiltNormalizer Q * ∏ j, primeHarmonicMass (P j)
  let bins := paddingBinIndices L η
  have hη : 0 < η := Real.exp_pos _
  obtain ⟨hS₀, A, hA, hphase, hweight, hcost⟩ := hselectL hL η hη
  have hp : ∀ j, ∀ p ∈ P j, p.Prime := centeredPrimeBands_prime _ _ _ _
  have hd : ∀ j k, k ≠ j → Disjoint (P j) (P k) := centeredPrimeBands_disjoint _ _ _ _
    (Real.rpow_nonneg (zero_le_one.trans hL) _) (zero_le_one.trans hWone)
  have hq : ∀ p ∈ Q, p.Prime := fun _ hp => paddingPrimeSupply_prime hp
  have hD : ∀ d ∈ D, 0 < d := by
    intro d hd'
    exact Nat.pos_of_ne_zero (primeTupleDivisors_arithmetic P hp hd hd').1.ne_zero
  have hR : ∀ q ∈ R, 0 < q := fun q hq' => retainedPrimeDivisor_pos Q hq (mem_filter.mp hq').1
  let b := fun dq : ℕ × ℕ => paddingBin η 0 (Real.log (dq.1 * dq.2 : ℕ))
  let eligible := selectedPairBin η A
  have hAb : A ⊆ D ×ˢ R := selected_pairs_bounded_padding D Q A L η hL hA
  have hb : ∀ dq ∈ A, b dq ∈ bins := fun _ hdq => selectedPairBin_index D Q A L η hA hdq
  have hprop (j : ℤ) (d q : ℕ) (he : eligible j d q) :=
    selectedPairBin_properties D Q hD hq A L η hη hA he
  have he : ∀ j ∈ bins, ∀ d q, eligible j d q → PaddingPairEligible L η d q :=
    fun j _ d q he => (hprop j d q he).2.2.1
  have hpos : ∀ j ∈ bins, ∀ d q, eligible j d q → 0 < d ∧ 0 < q :=
    fun j _ d q he => ⟨(hprop j d q he).1, (hprop j d q he).2.1⟩
  have hbin : ∀ j ∈ bins, ∀ d q, eligible j d q → actualPaddingBin η (Real.log d) j q :=
    fun j _ d q he => (hprop j d q he).2.2.2
  have hlower := selected_raw_bins_lower hfm hgm hfb hgb D Q hD hq L η γ hη hγ
    A hA h hS₀ hphase hcost hηL.le
  have hcent := hcenterL R (filter_subset _ _)
  have hlarge : ∀ᶠ X : ℝ in atTop, Real.exp (L ^ Ag) ≤ X := eventually_ge_atTop _
  have hevent : ∀ᶠ X : ℝ in atTop,
      γ ≤ ‖positivePrefix (fun n => f n * g (n + h)) ⌊X⌋₊ / (X : ℂ)‖ → False := by
    filter_upwards [hlower, hcent, hlarge] with X hlower hcent hX
    intro hbiased
    have hXp : 0 < X := (Real.exp_pos _).trans_le hX
    let T := fun j : ℤ => X * Real.exp ((j : ℝ) * η)
    let N := fun j : ℤ => ⌊T j⌋₊
    let v := fun j : ℤ => (N j : ℂ) / (T j : ℂ)
    let raw := ∑ j ∈ bins, v j * canonicalComplexUncutPrefix h E W L (eligible j)
      (fun n => f n.toNat) (fun n => g n.toNat) (N j)
    let full := selectedRawMean A (fun dq => T (b dq)) f g h
    have hv : ∀ j ∈ bins, ‖v j‖ ≤ 1 := fun j _ =>
      floor_cutoff_weight_norm_le (T j) (mul_pos hXp (Real.exp_pos _))
    have hN : ∀ j ∈ bins, Real.exp (L ^ Ag / 2) ≤ (N j : ℝ) := fun j hj =>
      (final_bin_windows L X η Ag hLlarge hAg hX hη j hj).2
    have hupper : ‖raw‖ / S₀ ≤ Cg * η :=
      hgraphL hL eligible he hpos hbin (fun n => f n.toNat) (fun n => g n.toNat)
        (fun n => hf n.toNat) (fun n => hg n.toNat) N v hN hv
    have hid : raw - full = ∑ j ∈ bins, nonrawComplexBin P R (eligible j) f g h (T j) :=
      selected_uncut_sub_raw P hp hd R hR A hAb bins b hb f g h T
    have hcerr : ‖raw - full‖ ≤ Cc * L ^ (-3 / 40 : ℝ) * M := by
      rw [hid]
      simpa only [one_mul, M, mul_assoc] using
        hcent eligible (fun _ => (1 : ℂ)) hbin (fun _ _ => by norm_num)
    have hmS : M / 2 ≤ S₀ := (hmassL hL η hη).2
    have hCm := mul_le_mul_of_nonneg_left (show M ≤ 2 * S₀ by linarith)
      (show 0 ≤ Cc * L ^ (-3 / 40 : ℝ) by positivity)
    have hgnum := (div_le_iff₀ hS₀).mp hupper
    have hl := hlower hbiased
    change γ * S₀ / 16 ≤ ‖full‖ at hl
    have htri : ‖full‖ ≤ ‖raw‖ + ‖raw - full‖ := by
      calc
        _ = ‖raw - (raw - full)‖ := by congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    have hstrict := mul_lt_mul_of_pos_right herrL hS₀
    nlinarith
  have heventN := tendsto_natCast_atTop_atTop.eventually hevent
  have hbad : ∀ᶠ N : ℕ in atTop,
      ¬γ ≤ ‖positivePrefix (fun n => f n * g (n + h)) N / (N : ℂ)‖ := by
    filter_upwards [heventN] with N hN
    simpa only [Nat.floor_natCast, Complex.ofReal_natCast] using hN
  exact hfreq hbad

end TwoPointCorrelations

end OAI
