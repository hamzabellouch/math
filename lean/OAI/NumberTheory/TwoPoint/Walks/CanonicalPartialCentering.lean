import OAI.NumberTheory.TwoPoint.Bounds.QuantitativeTupleBins
import OAI.NumberTheory.TwoPoint.Bounds.PartialCenteringSum
import OAI.NumberTheory.TwoPoint.Walks.CanonicalPartialWindows
import OAI.NumberTheory.TwoPoint.Bounds.PaddingDivisorEncoding

namespace OAI

/-! Quantitative nonraw centering for one actual logarithmic bin. The
only analytic inputs are the stated prime-reciprocal and MRT inputs. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

noncomputable def tupleNonrawBin {J : ℕ} (P : Fin J → Finset ℕ)
    (R : Finset ℕ) (weight : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (l : ℕ) [NeZero l] (b : ZMod l) (h : ℕ) (T : ℝ) : ℂ :=
  ∑ q ∈ R, (weight q : ℂ) *
    ((positivePrefix (tupleCenteredProfile P q eligible l b h) ⌊T⌋₊ -
      positivePrefix (tuplePartialProfile P ∅ q eligible l b h) ⌊T⌋₊) / (T : ℂ))

lemma tupleNonrawBin_real_denominator {J : ℕ} (P : Fin J → Finset ℕ)
    (R : Finset ℕ) (weight : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (l : ℕ) [NeZero l] (b : ZMod l) (h : ℕ) (T : ℝ) (hT : 1 ≤ T) :
    ‖tupleNonrawBin P R weight eligible l b h T‖ ≤
      ‖∑ q ∈ R, (weight q : ℂ) *
        ((positivePrefix (tupleCenteredProfile P q eligible l b h) ⌊T⌋₊ -
          positivePrefix (tuplePartialProfile P ∅ q eligible l b h) ⌊T⌋₊) / (⌊T⌋₊ : ℂ))‖ := by
  let F : ℕ → ℂ := fun q => (weight q : ℂ) *
    (positivePrefix (tupleCenteredProfile P q eligible l b h) ⌊T⌋₊ -
      positivePrefix (tuplePartialProfile P ∅ q eligible l b h) ⌊T⌋₊)
  have hN : (0 : ℝ) < ⌊T⌋₊ := by exact_mod_cast Nat.floor_pos.mpr hT
  have he (c : ℂ) : (∑ q ∈ R, (weight q : ℂ) *
      ((positivePrefix (tupleCenteredProfile P q eligible l b h) ⌊T⌋₊ -
        positivePrefix (tuplePartialProfile P ∅ q eligible l b h) ⌊T⌋₊) / c)) =
        (∑ q ∈ R, F q) / c := by simp only [F, mul_div_assoc, sum_div]
  rw [tupleNonrawBin, he, he, norm_div, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ T), Complex.norm_natCast]
  exact div_le_div_of_nonneg_left (norm_nonneg _) hN (Nat.floor_le (by linarith))

theorem quantitative_canonical_nonraw_bin (hP : ModFiveThetaInput)
    (hM : PrimeReciprocalInput) (hMRT : MRTLiouvilleShortInput)
    (h : ℕ) (hh : 0 < h) (l : ℕ) [NeZero l] (E : Finset ℕ)
    (hEl : ∀ p, p.Prime → p ∣ l → p ∈ E) (W : ℝ) (hW : 1 ≤ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Q := paddingPrimeSupply E L
      let R := boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊
      ∀ (T : ℝ), Real.exp (L ^ (1000 : ℝ)) ≤ T →
      ∀ (η : ℝ), 0 < η → η < Real.log 2 →
      ∀ (j : ℤ) (eligible : ℕ → ℕ → Prop),
      (∀ d q, eligible d q → actualPaddingBin η (Real.log d) j q) →
      ∀ b : ZMod l,
      ‖tupleNonrawBin P R actualPaddingCoefficient eligible l b h T‖ ≤
        C * L ^ (-21 / 20 : ℝ) * (2 : ℝ) ^ J * paddingTiltNormalizer Q *
          ∏ i, primeHarmonicMass (P i) := by
  obtain ⟨C, hC, hquant⟩ := quantitative_partial_tuple_bin hM hMRT h hh
  have hl : (0 : ℝ) < l := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne l)
  refine ⟨(l : ℝ) * C, mul_pos hl hC, ?_⟩
  filter_upwards [hquant, hP.eventually_canonical_tuple_slices E W hW,
    hP.eventually_partial_extracted_windows E W hW,
    hP.eventually_actual_pool_masses E W hW, eventually_ge_atTop (1000 : ℝ)]
      with L hquant hs hw hm hL
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Q := paddingPrimeSupply E L
  let R := boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊
  have hLp : 0 < L := by linarith
  have hp : ∀ i, ∀ p ∈ P i, p.Prime := centeredPrimeBands_prime _ _ _ _
  have hd : ∀ i k, k ≠ i → Disjoint (P i) (P k) :=
    centeredPrimeBands_disjoint _ _ _ _ (Real.rpow_nonneg hLp.le _) (by linarith)
  have hmass : ∀ i, 1 ≤ primeHarmonicMass (P i) := fun i => (hm.2.1 i).1
  intro T hT η hη hηlog j eligible helig b
  have hTone : 1 ≤ T := (Real.one_le_exp (by positivity)).trans hT
  have hN : 0 < ⌊T⌋₊ := Nat.floor_pos.mpr hTone
  have hqprime (q : ℕ) (hq : q ∈ R) : q ∈ retainedPrimeDivisors Q := (mem_filter.mp hq).1
  have hqb (q : ℕ) (hq : q ∈ R) : 0 < q :=
    retainedPrimeDivisor_pos Q (fun _ hp => paddingPrimeSupply_prime hp) (hqprime q hq)
  have hbound (q : ℕ) (hq : q ∈ R)
      (I : Finset (Fin J)) (hI : I ∈ (univ : Finset (Fin J)).powerset.filter Finset.Nonempty) :
      ‖positivePrefix (tuplePartialProfile P I q eligible l b h) ⌊T⌋₊ / (⌊T⌋₊ : ℂ)‖ ≤
        ((l : ℝ) * C * L ^ (-21 / 20 : ℝ)) *
          ((1 / (q : ℝ)) * ∏ i : {i // i ∉ I}, primeHarmonicMass (P i)) := by
    apply hquant J P hp hd I q ⌊T⌋₊ l (hqb q hq) hN eligible b
      (Real.exp ((j : ℝ) * η)) (Real.exp η) (Real.exp_pos _)
      (by simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_lt_exp.mpr hηlog)
      (fun y => partial_tuple_unit E _ W L J l hEl I (hqprime q hq) y)
      (fun y => hw I q hq y T hT)
    intro y z hz he
    have htp : 0 < ∏ i, (y i).val := prod_pos fun i _ => (hp i _ (y i).property).pos
    have hzp := primeTupleSlice_pos P I hp hz
    have hwin := partial_bin_window q _ z (hqb q hq) htp hzp η j (helig _ _ he)
    have hr := hs.2 I (mem_filter.mp hI).2 z hz
    exact ⟨by simpa only [Nat.cast_mul, Nat.cast_prod] using hwin.1,
      by simpa only [Nat.cast_mul, Nat.cast_prod] using hwin.2, hr.1, hr.2.1, hr.2.2⟩
  have hb := partial_centering_sum_bound P hp hd hmass R actualPaddingCoefficient
    (fun _ _ => by unfold actualPaddingCoefficient; positivity)
    (fun q hq i p hp => paddingPrimeDivisor_coprime_centered E _ W L J (hqprime q hq) i hp)
    eligible l b h ⌊T⌋₊ ((l : ℝ) * C * L ^ (-21 / 20 : ℝ)) (by positivity) hbound
  have hS : (∑ q ∈ R, actualPaddingCoefficient q / (q : ℝ)) ≤ paddingTiltNormalizer Q := by
    rw [paddingTiltNormalizer_eq_divisor_sum Q (fun _ hp => paddingPrimeSupply_prime hp)]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by
      unfold actualPaddingCoefficient; positivity)
  apply (tupleNonrawBin_real_denominator P R actualPaddingCoefficient eligible l b h T hTone).trans
  apply hb.trans
  gcongr
  exact prod_nonneg fun i _ => zero_le_one.trans (hmass i)

end TwoPointCorrelations

end OAI
