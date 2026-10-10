import OAI.NumberTheory.TotientAsymptotic.BandComparison

namespace OAI

/-!
The finite-union and geometric-tail argument behind the manuscript's
`ford-bands` estimate.  Only Ford's explicitly stated Theorems 10 and 16
remain hypotheses; the summation and the passage to model bands are proved.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def modelBandsCondition (x : ℝ) (P n : ℕ) : Prop :=
  ∀ i ∈ Finset.Icc 1 (m x-P),
    (9/10 : ℝ) * bandScale x i ≤ primeDoubleLog n i ∧
      primeDoubleLog n i ≤ (11/10 : ℝ) * bandScale x i

def extractedStructureCondition (x : ℝ) (P n : ℕ) : Prop :=
  modelBandsCondition x P n ∧ extractedSimplexCondition x P n

def positiveFordBandsCondition (x : ℝ) (P n : ℕ) : Prop :=
  ∀ i ∈ Finset.Icc 1 (m x-P), fordPositiveBandCondition x (1/25) i n

lemma totientCount_nonneg (x : ℝ) : 0 ≤ V x := by
  unfold V
  positivity

lemma preimageExceptionCount_forall_le (x : ℝ) (S : Finset ℕ)
    (Q : ℕ → ℕ → Prop) :
    preimageExceptionCount x (fun n => ∀ i ∈ S, Q i n) ≤
      ∑ i ∈ S, preimageExceptionCount x (Q i) := by
  classical
  have hsub : preimageExceptionValues x (fun n => ∀ i ∈ S, Q i n) ⊆
      S.biUnion (fun i => preimageExceptionValues x (Q i)) := by
    intro v hv
    obtain ⟨hv, n, hn, hφ, hQ⟩ := Finset.mem_filter.mp hv
    push Not at hQ
    obtain ⟨i, hi, hin⟩ := hQ
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hv, n, hn, hφ, hin⟩⟩
  have hh := (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  unfold preimageExceptionCount
  exact_mod_cast hh

lemma preimageExceptionCount_and_le (x : ℝ) (Q R : ℕ → Prop) :
    preimageExceptionCount x (fun n => Q n ∧ R n) ≤
      preimageExceptionCount x Q + preimageExceptionCount x R := by
  classical
  have hsub : preimageExceptionValues x (fun n => Q n ∧ R n) ⊆
      preimageExceptionValues x Q ∪ preimageExceptionValues x R := by
    intro v hv
    obtain ⟨hv, n, hn, hφ, hQR⟩ := Finset.mem_filter.mp hv
    by_cases hQ : Q n
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hv, n, hn, hφ, fun hR => hQR ⟨hQ, hR⟩⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv, n, hn, hφ, hQ⟩)
  unfold preimageExceptionCount
  exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

lemma backward_exponential_sum_le (M P : ℕ) (hPM : P ≤ M) :
    (∑ i ∈ Finset.Icc 1 (M-P), Real.exp (-((M-i : ℕ) : ℝ)/2500)) ≤
      Real.exp (-(P : ℝ)/2500) / (1-Real.exp (-(1 : ℝ)/2500)) := by
  have hsum : (∑ i ∈ Finset.Icc 1 (M-P), Real.exp (-((M-i : ℕ) : ℝ)/2500)) =
      ∑ h ∈ Finset.Ico P M, Real.exp (-(h : ℝ)/2500) := by
    apply Finset.sum_bij (fun i _ => M-i)
    · intro i hi
      simp only [Finset.mem_Icc] at hi
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    · intro i hi j hj hij
      simp only [Finset.mem_Icc] at hi hj
      omega
    · intro h hh
      simp only [Finset.mem_Ico] at hh
      refine ⟨M-h, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      omega
    · intro i hi
      rfl
  have he (h : ℕ) : Real.exp (-(h : ℝ)/2500) =
      Real.exp (-(1 : ℝ)/2500)^h := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hsum]
  calc
    (∑ h ∈ Finset.Ico P M, Real.exp (-(h : ℝ)/2500)) =
        ∑ h ∈ Finset.Ico P M, Real.exp (-(1 : ℝ)/2500)^h := by
      apply Finset.sum_congr rfl
      intro h hh
      exact he h
    _ ≤ Real.exp (-(1 : ℝ)/2500)^P / (1-Real.exp (-(1 : ℝ)/2500)) :=
      geom_sum_Ico_le_of_lt_one (Real.exp_pos _).le
        (Real.exp_lt_one_iff.mpr (by norm_num))
    _ = _ := by rw [← he P]

lemma linear_exponential_le (M P : ℕ) (hPM : P ≤ M) :
    (M : ℝ) * Real.exp (-(M : ℝ)/325) ≤
      650 * Real.exp (-(P : ℝ)/2500) := by
  have hM : (M : ℝ) ≤ 650 * Real.exp ((M : ℝ)/650) := by
    have hh := Real.add_one_le_exp ((M : ℝ)/650)
    linarith
  calc
    (M : ℝ) * Real.exp (-(M : ℝ)/325) ≤
        (650 * Real.exp ((M : ℝ)/650)) * Real.exp (-(M : ℝ)/325) :=
      mul_le_mul_of_nonneg_right hM (Real.exp_pos _).le
    _ = 650 * Real.exp (-(M : ℝ)/650) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ 650 * Real.exp (-(P : ℝ)/2500) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
      have hh : (P : ℝ) ≤ M := by exact_mod_cast hPM
      have h0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
      linarith

def bandExceptionFactor : ℝ := 650 + 25 / (1-Real.exp (-(1 : ℝ)/2500))

lemma bandExceptionFactor_pos : 0 < bandExceptionFactor := by
  have hh : Real.exp (-(1 : ℝ)/2500) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  unfold bandExceptionFactor
  positivity

lemma band_error_sum_le (M P : ℕ) (hPM : P ≤ M) :
    (∑ i ∈ Finset.Icc 1 (M-P),
      (Real.exp (-(M : ℝ)/325) + 25 * Real.exp (-((M-i : ℕ) : ℝ)/2500))) ≤
      bandExceptionFactor * Real.exp (-(P : ℝ)/2500) := by
  rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum]
  simp only [nsmul_eq_mul]
  have hcard : ((Finset.Icc 1 (M-P)).card : ℝ) ≤ M := by
    simp only [Nat.card_Icc, Nat.add_sub_cancel]
    exact_mod_cast Nat.sub_le M P
  have hc := mul_le_mul_of_nonneg_right hcard (Real.exp_pos (-(M : ℝ)/325)).le
  have ht := mul_le_mul_of_nonneg_left (backward_exponential_sum_le M P hPM)
    (by norm_num : (0 : ℝ) ≤ 25)
  change ((Finset.Icc 1 (M-P)).card : ℝ) * Real.exp (-(M : ℝ)/325) +
    25 * (∑ i ∈ Finset.Icc 1 (M-P), Real.exp (-((M-i : ℕ) : ℝ)/2500)) ≤ _
  have hl := linear_exponential_le M P hPM
  calc
    _ ≤ 650 * Real.exp (-(P : ℝ)/2500) +
        25 * (Real.exp (-(P : ℝ)/2500) / (1-Real.exp (-(1 : ℝ)/2500))) :=
      add_le_add (hc.trans hl) ht
    _ = _ := by unfold bandExceptionFactor; ring

lemma ford10_single_band_estimate {x C : ℝ} (hC : 0 ≤ C)
    (hford : ∀ i : ℕ, 1 ≤ i → i < m x → ∀ η : ℝ, 0 < η → η ≤ 1/8 →
      (η ≤ (i : ℝ)/(3*m x) →
        preimageExceptionCount x (fordPositiveBandCondition x η i) ≤
          C * V x * ((i : ℝ)/(η*m x)) *
            Real.exp (-η^2 * m x * (m x-i : ℕ)/(4*i))) ∧
      ((i : ℝ)/(3*m x) ≤ η →
        preimageExceptionCount x (fordPositiveBandCondition x η i) ≤
          C * V x * Real.exp (-η*m x/13)))
    {i : ℕ} (hi : 1 ≤ i) (hiM : i < m x) :
    preimageExceptionCount x (fordPositiveBandCondition x (1/25) i) ≤
      C * V x * (Real.exp (-(m x : ℝ)/325) +
        25 * Real.exp (-((m x-i : ℕ) : ℝ)/2500)) := by
  have hcv : 0 ≤ C * V x := mul_nonneg hC (totientCount_nonneg x)
  have hh := hford i hi hiM (1/25) (by norm_num) (by norm_num)
  by_cases hsmall : (i : ℝ)/(3*m x) ≤ 1/25
  · have hs := hh.2 hsmall
    have he : -(1/25 : ℝ) * m x / 13 = -(m x : ℝ)/325 := by ring
    rw [he] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right
      (by positivity)) hcv)
  · have hs := hh.1 (le_of_lt (lt_of_not_ge hsmall))
    have hi0 : (0 : ℝ) < i := Nat.cast_pos.mpr (by omega)
    have hm0 : (0 : ℝ) < m x := Nat.cast_pos.mpr (by omega)
    have him : (i : ℝ) ≤ m x := by exact_mod_cast hiM.le
    have hpref : (i : ℝ)/((1/25 : ℝ)*m x) ≤ 25 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (1/25 : ℝ)*m x)).mpr
      nlinarith
    have hexp : -(1/25 : ℝ)^2 * m x * (m x-i : ℕ)/(4*i) ≤
        -((m x-i : ℕ) : ℝ)/2500 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4*(i : ℝ))).mpr
      have hd : (0 : ℝ) ≤ (m x-i : ℕ) := Nat.cast_nonneg _
      have ht := mul_le_mul_of_nonneg_right him hd
      nlinarith
    have hprod : C * V x * ((i : ℝ)/((1/25 : ℝ)*m x)) *
        Real.exp (-(1/25 : ℝ)^2 * m x * (m x-i : ℕ)/(4*i)) ≤
        C * V x * (25 * Real.exp (-((m x-i : ℕ) : ℝ)/2500)) := by
      calc
        _ ≤ (C * V x * 25) *
            Real.exp (-(1/25 : ℝ)^2 * m x * (m x-i : ℕ)/(4*i)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpref hcv)
            (Real.exp_pos _).le
        _ ≤ (C * V x * 25) * Real.exp (-((m x-i : ℕ) : ℝ)/2500) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
        _ = _ := by ring
    exact (hs.trans hprod).trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (Real.exp_pos _).le) hcv)

/-- Theorem 10 gives the geometric-tail estimate for existing positive
coordinates.  Theorem 16 supplies the missing-coordinate estimate below. -/
theorem positive_ford_bands_exception_bound (hford : FordTheorem10Input) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ P : ℕ, 0 < P → P < m x →
      preimageExceptionCount x (positiveFordBandsCondition x P) ≤
        C * V x * Real.exp (-(P : ℝ)/2500) := by
  obtain ⟨C, hC, hford⟩ := hford
  refine ⟨C * bandExceptionFactor, mul_pos hC bandExceptionFactor_pos, ?_⟩
  filter_upwards [hford] with x hx
  intro P hP hPM
  calc
    _ ≤ ∑ i ∈ Finset.Icc 1 (m x-P),
        preimageExceptionCount x (fordPositiveBandCondition x (1/25) i) :=
      preimageExceptionCount_forall_le _ _ _
    _ ≤ ∑ i ∈ Finset.Icc 1 (m x-P), C * V x *
        (Real.exp (-(m x : ℝ)/325) +
          25 * Real.exp (-((m x-i : ℕ) : ℝ)/2500)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := Finset.mem_Icc.mp hi
      exact ford10_single_band_estimate hC.le hx hh.1 (by omega)
    _ = C * V x * (∑ i ∈ Finset.Icc 1 (m x-P),
        (Real.exp (-(m x : ℝ)/325) +
          25 * Real.exp (-((m x-i : ℕ) : ℝ)/2500))) := by rw [Finset.mul_sum]
    _ ≤ C * V x * (bandExceptionFactor * Real.exp (-(P : ℝ)/2500)) :=
      mul_le_mul_of_nonneg_left (band_error_sum_le _ _ hPM.le)
        (mul_nonneg hC.le (totientCount_nonneg x))
    _ = _ := by ring

/-- Bands and the unclamped simplex hold for every preimage outside one
exceptional set with exponential decay in P. -/
theorem extracted_structure_exception_bound
    (h10 : FordTheorem10Input) (h16 : FordTheorem16Input) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ P : ℕ, 0 < P → P < m x →
      preimageExceptionCount x (extractedStructureCondition x P) ≤
        C * V x * Real.exp (-(P : ℝ)/2500) := by
  obtain ⟨Cb, hCb, hbands⟩ := positive_ford_bands_exception_bound h10
  obtain ⟨Cs, hCs, hsimplex⟩ := h16
  refine ⟨Cb+Cs, add_pos hCb hCs, ?_⟩
  filter_upwards [hbands, hsimplex, fordBands_imply_modelBands] with x hb hs hmodel
  intro P hP hPM
  have htransfer : preimageExceptionCount x (extractedStructureCondition x P) ≤
      preimageExceptionCount x
        (fun n => positiveFordBandsCondition x P n ∧ fordSimplexCondition x P n) := by
    apply preimageExceptionCount_mono
    intro n hn
    refine ⟨?_, fordSimplexCondition_implies_extracted hPM hn.2⟩
    intro i hi
    have hiM : i < m x := by have hh := Finset.mem_Icc.mp hi; omega
    exact hmodel i hiM n (hn.1 i hi (fordSimplexCondition_coordinate_pos hn.2 hi))
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast (show 1 ≤ P by omega)
  have he : Real.exp (-(P : ℝ)^2/4) ≤ Real.exp (-(P : ℝ)/2500) := by
    apply Real.exp_le_exp.mpr
    have hprod := mul_nonneg (Nat.cast_nonneg P : (0 : ℝ) ≤ P)
      (sub_nonneg.mpr hP1)
    nlinarith
  calc
    _ ≤ preimageExceptionCount x (positiveFordBandsCondition x P) +
        preimageExceptionCount x (fordSimplexCondition x P) :=
      htransfer.trans (preimageExceptionCount_and_le _ _ _)
    _ ≤ Cb * V x * Real.exp (-(P : ℝ)/2500) +
        Cs * V x * Real.exp (-(P : ℝ)^2/4) := add_le_add (hb P hP hPM) (hs P hPM)
    _ ≤ Cb * V x * Real.exp (-(P : ℝ)/2500) +
        Cs * V x * Real.exp (-(P : ℝ)/2500) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left he
        (mul_nonneg hCs.le (totientCount_nonneg x)))
    _ = _ := by ring

/-- Missing and nonpositive coordinates are included via Theorem 16,
before the positive-coordinate estimate from Theorem 10 is applied. -/
theorem model_bands_exception_bound (h10 : FordTheorem10Input) (h16 : FordTheorem16Input) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ P : ℕ, 0 < P → P < m x →
      preimageExceptionCount x (modelBandsCondition x P) ≤
        C * V x * Real.exp (-(P : ℝ)/2500) := by
  obtain ⟨C, hC, hbound⟩ := extracted_structure_exception_bound h10 h16
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with x hx
  intro P hP hPM
  exact (preimageExceptionCount_mono (fun _ hn => hn.1)).trans (hx P hP hPM)

/-- The manuscript's order of quantifiers: choose P, then take x large.
Here every P≥1 works, with absolute constants independent of P. -/
theorem extracted_structure_eventually
    (h10 : FordTheorem10Input) (h16 : FordTheorem16Input) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ P : ℕ, 0 < P → ∀ᶠ x : ℝ in atTop,
      P < m x ∧ preimageExceptionCount x (extractedStructureCondition x P) ≤
        C * V x * Real.exp (-c * P) := by
  obtain ⟨C, hC, hbound⟩ := extracted_structure_exception_bound h10 h16
  refine ⟨C, 1/2500, hC, by norm_num, ?_⟩
  intro P hP
  filter_upwards [hbound, m_tendsto.eventually (eventually_gt_atTop P)] with x hx hPx
  refine ⟨hPx, ?_⟩
  have he : -(1/2500 : ℝ)*(P : ℝ) = -(P : ℝ)/2500 := by ring
  rw [he]
  exact hx P hP hPx

/-- The exceptional set removes values with any failing preimage, so the
surviving values satisfy the full retained range simultaneously in every
positive preimage. -/
theorem extracted_structure_all_preimages
    (h10 : FordTheorem10Input) (h16 : FordTheorem16Input) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ P : ℕ, 0 < P → ∀ᶠ x : ℝ in atTop,
      ∃ E : Finset ℕ, P < m x ∧ (E.card : ℝ) ≤ C * V x * Real.exp (-c * P) ∧
        ∀ v ∈ Finset.Icc 1 ⌊x⌋₊, v ∉ E → ∀ n : ℕ, 0 < n → n.totient = v →
          extractedStructureCondition x P n := by
  obtain ⟨C, c, hC, hc, hbound⟩ := extracted_structure_eventually h10 h16
  refine ⟨C, c, hC, hc, ?_⟩
  intro P hP
  filter_upwards [hbound P hP] with x hx
  refine ⟨preimageExceptionValues x (extractedStructureCondition x P), hx.1, hx.2, ?_⟩
  intro v hv hout
  exact (outside_preimageExceptions_iff hv).mp hout

end TotientAsymptotic

end

end OAI
