import OAI.NumberTheory.TwoPoint.Bounds.QualitativePartialCentering
import OAI.NumberTheory.TwoPoint.Walks.CanonicalTupleSmooth
import OAI.NumberTheory.TwoPoint.Bounds.ComplexCenteredBridge
import OAI.NumberTheory.TwoPoint.Bounds.PaddingSmoothBound

namespace OAI

/-! The actual canonical nonraw complex bins: the cost of every padding
dilation is summed against its exact reciprocal law. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma nonrawComplexBin_real_denominator {J : ℕ} (P : Fin J → Finset ℕ)
    (R : Finset ℕ) (eligible : ℕ → ℕ → Prop) (F G : ℕ → ℂ) (h : ℕ)
    (T : ℝ) (hT : 1 ≤ T) :
    ‖nonrawComplexBin P R eligible F G h T‖ ≤
      ‖∑ q ∈ R, (actualPaddingCoefficient q : ℂ) *
        ((positivePrefix (tupleComplexCenteredProfile P q eligible F G h) ⌊T⌋₊ -
          positivePrefix (tupleComplexPartialProfile P ∅ q eligible F G h) ⌊T⌋₊) /
          (⌊T⌋₊ : ℂ))‖ := by
  let A : ℕ → ℂ := fun q => (actualPaddingCoefficient q : ℂ) *
    (positivePrefix (tupleComplexCenteredProfile P q eligible F G h) ⌊T⌋₊ -
      positivePrefix (tupleComplexPartialProfile P ∅ q eligible F G h) ⌊T⌋₊)
  have he (c : ℂ) : (∑ q ∈ R, (actualPaddingCoefficient q : ℂ) *
      ((positivePrefix (tupleComplexCenteredProfile P q eligible F G h) ⌊T⌋₊ -
        positivePrefix (tupleComplexPartialProfile P ∅ q eligible F G h) ⌊T⌋₊) / c)) =
      (∑ q ∈ R, A q) / c := by simp only [A, mul_div_assoc, sum_div]
  have hN : (0 : ℝ) < ⌊T⌋₊ := by exact_mod_cast Nat.floor_pos.mpr hT
  rw [nonrawComplexBin, he, he, norm_div, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ T), Complex.norm_natCast]
  exact div_le_div_of_nonneg_left (norm_nonneg _) hN (Nat.floor_le (by linarith))

theorem qualitative_canonical_nonraw_bin (hP : ModFiveThetaInput)
    (hM : PrimeReciprocalInput) (hMRT : MRTShortExponentialInput)
    {F G : ℕ → ℂ} (hFm : Multiplicative F) (hGm : Multiplicative G)
    (hF : OneBounded F) (hG : OneBounded G)
    (hnp : UniformlyNonpretentious F ∨ UniformlyNonpretentious G)
    (h : ℕ) (hh : 0 < h) (E : Finset ℕ) (W : ℝ) (hW : 1 ≤ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Q := paddingPrimeSupply E L
      ∀ R : Finset ℕ, R ⊆ retainedPrimeDivisors Q →
      ∀ η : ℝ, 0 < η → Real.exp (2 * η) < 2 →
      ∀ᶠ T : ℝ in atTop, ∀ j ∈ paddingBinIndices L η,
      ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → actualPaddingBin η (Real.log d) j q) →
      ‖nonrawComplexBin P R eligible F G h T‖ ≤
        C * canonicalRoughParameter L ^ (-11 / 10 : ℝ) * (2 : ℝ) ^ J *
          paddingTiltNormalizer Q * ∏ i, primeHarmonicMass (P i) := by
  obtain ⟨C, hC, hrough⟩ := qualitative_complex_partial_bin hM hMRT hFm hGm hF hG hnp
    h hh 100 (by norm_num)
  refine ⟨2 * C * paddingSmoothConstant,
    mul_pos (mul_pos (by norm_num) hC) paddingSmoothConstant_pos, ?_⟩
  filter_upwards [canonicalRoughParameter_tendsto.eventually hrough,
    eventually_canonical_retained_smooth_cost E W hW,
    hP.eventually_actual_pool_masses E W hW, eventually_ge_atTop (1 : ℝ)] with
    L hrough hcost hmass hL
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Q := paddingPrimeSupply E L
  let B := canonicalRoughParameter L
  let Is := (univ : Finset (Fin J)).powerset.filter Finset.Nonempty
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hB : 0 < B := Real.rpow_pos_of_pos hLp _
  have hp : ∀ i, ∀ p ∈ P i, p.Prime := centeredPrimeBands_prime _ _ _ _
  have hd : ∀ i j, j ≠ i → Disjoint (P i) (P j) := centeredPrimeBands_disjoint _ _ _ _
    (Real.rpow_nonneg hLp.le _) (zero_le_one.trans hW)
  have hlarge : ∀ i, ∀ p ∈ P i, Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ (p : ℝ) := by
    intro i p hip
    rw [canonicalRoughParameter_prime_endpoint L hLp.le]
    exact (centeredPrimeSupply_global_bounds (Real.rpow_nonneg hLp.le _) (zero_le_one.trans hW)
      i.isLt (primeSupplyScale_endpoint W L (by linarith) hL) hip).1.le
  have hQ : ∀ p ∈ Q, p.Prime := fun _ hp => paddingPrimeSupply_prime hp
  intro R hR
  have hRpos : ∀ q ∈ R, 0 < q := fun q hq => retainedPrimeDivisor_pos Q hQ (hR hq)
  have hcop : ∀ q ∈ R, ∀ i, ∀ p ∈ P i, q.Coprime p := by
    intro q hq i p hip
    exact paddingPrimeDivisor_coprime_centered E _ W L J (hR hq) i hip
  have hm : ∀ i, 1 ≤ primeHarmonicMass (P i) := fun i => (hmass.2.1 i).1
  intro η hη hηtwo
  let bins := paddingBinIndices L η
  let e : ℕ → ℝ := fun q => 2 * C * B ^ (-11 / 10 : ℝ) *
    smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ)
  have he : ∀ q ∈ R, 0 ≤ e q := by
    intro q _
    exact mul_nonneg (by positivity) (smoothReciprocalProduct_nonneg _
      (fun _ hp => Nat.prime_of_mem_primeFactors hp) _ (by norm_num))
  have hall : ∀ᶠ N : ℕ in atTop, ∀ j ∈ bins, ∀ q ∈ R, ∀ I ∈ Is,
      ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → actualPaddingBin η (Real.log d) j q) →
      ‖positivePrefix (tupleComplexPartialProfile P I q eligible F G h) N / (N : ℂ)‖ ≤
        e q * ((1 / (q : ℝ)) * ∏ i : {i // i ∉ I}, primeHarmonicMass (P i)) := by
    apply (eventually_all_finset bins).mpr
    intro j hj
    apply (eventually_all_finset R).mpr
    intro q hq
    apply (eventually_all_finset Is).mpr
    intro I hI
    have hjbound := (mem_paddingBinIndices_iff L η j hη).mp hj
    have hupper : Real.exp ((j : ℝ) * η) ≤ Real.exp (100 * B ^ (2 : ℕ)) := by
      apply Real.exp_le_exp.mpr
      exact hjbound.2.trans (mul_le_mul_of_nonneg_left (canonicalRoughParameter_square_ge L hL)
        (by norm_num))
    exact hrough J P hp hd hlarge I (mem_filter.mp hI).2 q (hRpos q hq)
      (hcost I) η hη hηtwo j hupper
  have hsum : (∑ q ∈ R, actualPaddingCoefficient q / (q : ℝ) * e q) ≤
      (2 * C * B ^ (-11 / 10 : ℝ)) *
        (paddingTiltNormalizer Q * paddingSmoothConstant) := by
    calc
      _ = (2 * C * B ^ (-11 / 10 : ℝ)) *
          ∑ q ∈ R, (4 : ℝ) ^ q.primeFactors.card / (q : ℝ) *
            smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro q _
        dsimp only [e, actualPaddingCoefficient]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply le_trans _ (padding_smooth_half_sum_le Q hQ)
        exact sum_le_sum_of_subset_of_nonneg hR (fun q _ _ => mul_nonneg (by positivity)
          (smoothReciprocalProduct_nonneg _ (fun _ hp => Nat.prime_of_mem_primeFactors hp)
            _ (by norm_num)))
  have hnat : ∀ᶠ N : ℕ in atTop, ∀ j ∈ bins, ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → actualPaddingBin η (Real.log d) j q) →
      ‖∑ q ∈ R, (actualPaddingCoefficient q : ℂ) *
        ((positivePrefix (tupleComplexCenteredProfile P q eligible F G h) N -
          positivePrefix (tupleComplexPartialProfile P ∅ q eligible F G h) N) / (N : ℂ))‖ ≤
        (2 * C * paddingSmoothConstant) * B ^ (-11 / 10 : ℝ) * (2 : ℝ) ^ J *
          paddingTiltNormalizer Q * ∏ i, primeHarmonicMass (P i) := by
    filter_upwards [hall] with N hN
    intro j hj eligible hel
    have hb := complex_partial_centering_sum_bound P hp hd hm R actualPaddingCoefficient
      (fun q _ => by unfold actualPaddingCoefficient; positivity) hcop eligible F G h N e he
      (fun q hq I hI => hN j hj q hq I hI eligible hel)
    apply hb.trans
    calc
      _ ≤ (2 : ℝ) ^ J * ((2 * C * B ^ (-11 / 10 : ℝ)) *
          (paddingTiltNormalizer Q * paddingSmoothConstant)) * ∏ i, primeHarmonicMass (P i) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by positivity))
          (prod_nonneg (fun i _ => zero_le_one.trans (hm i)))
      _ = _ := by ring
  filter_upwards [(tendsto_nat_floor_atTop (α := ℝ)).eventually hnat,
    eventually_ge_atTop (1 : ℝ)] with T hT hTone
  intro j hj eligible hel
  exact (nonrawComplexBin_real_denominator P R eligible F G h T hTone).trans
    (hT j hj eligible hel)

end TwoPointCorrelations

end OAI
