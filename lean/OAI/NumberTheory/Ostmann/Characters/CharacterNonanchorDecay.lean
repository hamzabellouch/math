import OAI.NumberTheory.Ostmann.Characters.CharacterAnchorDecay
import OAI.NumberTheory.Ostmann.Characters.CharacterBandCutoffs
import OAI.NumberTheory.Ostmann.Characters.CharacterComparisonCounts
import OAI.NumberTheory.Ostmann.Construction.SelectedNonanchorProductDecay
import OAI.NumberTheory.Ostmann.Construction.ConstituentHProductLower

namespace OAI

/-! # Code-changing cancellation on the actual signed character cells -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem eventual_character_nonanchor_decay (k n N : ℕ) (hn : n + 1 < k)
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ x, conj (ψ x) = ψ x)
    (B z c Cmass α βg βw γs βa γw νw νa : ℝ)
    (hB : 1 ≤ B) (hz : 1 ≤ z) (hc : 1 ≤ c) (hCmass : 0 < Cmass)
    (hα : 0 < α) (hβg : 0 < βg) (hαw : α < βw) (hsw : γs < βw)
    (hαa : α < βa) (hwa : γw < βa) (hwg : γw ≤ βg)
    (hβw : βw < νw) (hβa : βa < νa) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℕ, 1 ≤ (m : ℝ) → L ≤ m →
      (m : ℝ) ≤ z * L → (Fintype.card (CharacterRole k) : ℝ) * c ≤ m →
      ∀ (r : Fin k → ℕ) (f : ℕ) (hr : ∀ j, 0 < r j),
      (∀ j, r j ≤ N) → f ≤ N →
      ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
        (Q : (Σ v, Fin (characterSize m r f v)) → Finset ℕ),
      (∀ i, Q i ⊆ P) →
      (∀ i, Real.exp (-Cmass * L) ≤ ∑ p ∈ Q i, (p : ℝ)⁻¹) →
      (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p ∧
        (p : ℝ) ≤ Real.exp (Real.exp (βg * L))) →
      (∀ j p, p ∈ Q (characterAnchor m r f j false) →
        (p : ℝ) ≤ Real.exp (Real.exp (γs * L))) →
      (∀ i p, p ∈ Q (characterBulk m r f i) →
        Real.exp (Real.exp (νw * L)) ≤ p ∧ (p : ℝ) ≤ Real.exp (Real.exp (γw * L))) →
      (∀ j p, p ∈ Q (characterAnchor m r f j true) →
        Real.exp (Real.exp (νa * L)) ≤ p) →
      ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
      ∀ (J : ℕ), 0 < J → ∀ (anchor : Fin k → Bool → ℝ) (F logX : ℝ), 0 < logX →
      let Δ := characterBaseGap B z m
      let T := characterPivotTarget k J (fun j => anchor j false + anchor j true)
        (fun j => characterPivotGap B z m j.val)
      T ⟨n + 1, hn⟩ + c ≤ Real.exp (βg * L) →
      ∀ lower upper : CharacterCell k → ℕ,
      (∀ v, Real.exp (characterLogCenter J T anchor F (true, some v) - c) ≤ lower v) →
      (∀ v, (upper v : ℝ) ≤ Real.exp (characterLogCenter J T anchor F (true, some v) + c)) →
      let lo := initialWordAtomLower J lower
      let hi := initialWordAtomUpper J upper
      let χ₀ := signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ
      let V := naturalTransferCutoff Δ m
      let cap := characterPivotCap T (characterRangeError k c)
      let p := characterPivotAtom ⟨n + 1, hn⟩
      let ρ := fun i : Σ v, Fin (characterSize m r f v) => characterRole k i.1
      let Sbad := cellPreservingMatchings (selectedBulkLabel ρ (n + 1) m
        (characterBulk m r f) (characterBulk_role m r f)) \
        selectedAnchorMatchingSet ρ (n + 1) m (characterBulk m r f) (characterBulk_role m r f)
      (∑ M ∈ Finset.Icc (lo p) (hi p),
        (constituentMatchingFamily (characterRole k) (characterSize m r f) χ₀
          (fun i => primeGaussMultiplier (χ₀ i)) (characterPivot m r f hr) (n + 1) P hP Q
          V cap (atomIntervalRanges (characterRole k) lo hi)
          (scheduleFourierLeaf (characterRole k) ψ (Real.exp logX)
            (Real.exp (Δ - (Fintype.card (CharacterRole k) : ℝ) * c))
            (Real.exp (Δ + (Fintype.card (CharacterRole k) : ℝ) * c)))
          (scheduledFrequencyHistory V (n + 1)) Sbad M).re) ≤
        Real.exp (-(characterPivotGap B z m (n + 1) - 2 * characterRangeError k c)) := by
  let d := B + 20 * Real.log z
  let C₀ := (Fintype.card (CharacterRole k) : ℝ) * c
  let D := (2 : ℝ) ^ k * d + 2 * (4 : ℝ) ^ k
  let C := max D (d + 1)
  let H := Cmass + βg + α + Real.log ((Real.log 2)⁻¹ + 1) + 2
  let S := max 1 (max (SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)))
    (SchwartzMap.seminorm ℝ 0 1 (𝓕 ψ : 𝓢(ℝ, ℂ))))
  have hz0 : 0 < z := by linarith
  have hd1 : 1 ≤ d := by dsimp [d]; linarith [Real.log_nonneg hz]
  have hd : 0 ≤ d := by linarith
  have hC : 0 ≤ C := (by dsimp [D]; positivity : (0 : ℝ) ≤ D).trans (le_max_left _ _)
  have hlc : 0 ≤ Real.log ((Real.log 2)⁻¹ + 1) := by
    have hh : 0 ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr (Real.log_pos (by norm_num)).le
    exact Real.log_nonneg (by linarith)
  have hH : 0 ≤ H := by dsimp [H]; linarith
  have hHm : Cmass ≤ H := by dsimp [H]; linarith
  have hHdy : βg + Real.log ((Real.log 2)⁻¹ + 1) ≤ H := by dsimp [H]; linarith
  have hHratio : βg - α ≤ H := by dsimp [H]; linarith
  have hS : 1 ≤ S := le_max_left _ _
  have hs : 0 ≤ (N : ℝ) + 2 := by positivity
  filter_upwards [eventual_selected_nonanchor_product_decay (characterRole k) n 1
      (3 ^ k * Fintype.card (CharacterRole k)) ((N : ℝ) + 2) C S H z
      α βw γs βa γw 1 0 hs hC hS hH hz0.le hα hαw hsw hαa hwa (by norm_num) (by norm_num),
    eventual_character_band_lower βw νw (hα.trans (hαw.trans hβw)) hβw,
    eventual_character_band_lower βa νa (hα.trans (hαa.trans hβa)) hβa,
    eventual_natural_cutoff_below_primes k d z α 1 hd hz0.le hα (by norm_num),
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hβg)).eventually
      (eventually_ge_atTop (2 : ℝ)),
    eventually_ge_atTop (1 : ℝ)] with L hdec hAw hAa hlarge hRthree hL
  intro m hm hLM hmL hCm r f hr hrN hf P hP Q hQP hmass hPrange hsmall hword hbig
    χ hχ J _hJ anchor F logX hlogX Δ T hT lower upper hlower hupper lo hi χ₀ V cap p ρ Sbad
  have hpos (i) : 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹ := (Real.exp_pos _).trans_le (hmass i)
  have hPne : P.Nonempty := by
    have hne : Q (characterTop m r f) ≠ ∅ := by
      intro he
      have hh := hpos (characterTop m r f)
      simp only [he, Finset.sum_empty, lt_self_iff_false] at hh
    obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    exact ⟨q, hQP _ hq⟩
  let small : Fin (n + 1) → (Σ v, Fin (characterSize m r f v)) :=
    fun j => characterAnchor m r f (j.castLE hn.le) false
  let large : Fin (n + 1) → (Σ v, Fin (characterSize m r f v)) :=
    fun j => characterAnchor m r f (j.castLE hn.le) true
  let Aw := ⌈Real.exp (Real.exp (βw * L))⌉₊
  let Aa := ⌈Real.exp (Real.exp (βa * L))⌉₊
  let Bs := ⌊Real.exp (Real.exp (γs * L))⌋₊
  let Bw := ⌊Real.exp (Real.exp (γw * L))⌋₊
  let Ea := ⌊Real.exp (Real.exp (βg * L))⌋₊
  let ℓ := Real.exp (Real.exp (α * L))
  let Rmax := Real.exp (Real.exp (βg * L))
  have hBw : (Bw : ℝ) ≤ Rmax := by
    apply (Nat.floor_le (Real.exp_nonneg _)).trans
    apply Real.exp_le_exp.mpr
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hwg (by linarith)
  have hEa : (Ea : ℝ) ≤ Rmax := Nat.floor_le (Real.exp_nonneg _)
  have hWB := character_initial_window_bounds d C₀ m hd1 hm (by dsimp [C₀]; positivity) hCm
  change 1 ≤ Real.exp (Δ - C₀) ∧ Real.exp (Δ - C₀) ≤ Real.exp (Δ + C₀) ∧
    Real.exp (Δ + C₀) - Real.exp (Δ - C₀) ≤ Real.exp ((d + 1) * m) at hWB
  have hXlo : 1 < Real.exp logX * Real.exp (Δ - C₀) := by
    have he := Real.one_lt_exp_iff.mpr hlogX
    have hlo := hWB.1
    nlinarith only [he, hlo]
  have hw := character_word_interval_errors J c hc T anchor F lower upper hlower hupper
  have hpositive : 0 < ∏ h : CopyScheduleH (characterRole k) (n + 1),
      (lo (copyScheduleOrigin (n + 1) h.val) : ℝ) :=
    Finset.prod_pos (fun h _ => (Real.exp_pos _).trans_le (hw.1 _))
  have hA : 0 < lo p := by exact_mod_cast (Real.exp_pos _).trans_le (hw.1 p)
  have hcap : hi p ≤ cap (n + 1) := by
    dsimp only [cap]
    rw [characterPivotCap_eq hn]
    apply Nat.le_floor
    exact (hw.2 p).trans (Real.exp_le_exp.mpr (by
      change T ⟨n + 1, hn⟩ + c ≤ T ⟨n + 1, hn⟩ + characterRangeError k c
      linarith only [le_characterRangeError k c (by linarith)]))
  have hgap := character_diagonal_product_gap hn J B z m F c (by linarith) anchor
    lo hi hw.1 hw.2
  have hgap' : Real.exp (characterPivotGap B z m (n + 1) - 2 * characterRangeError k c) *
      (hi p : ℝ) ≤ ∏ h : CopyScheduleH (characterRole k) (n + 1),
        (lo (copyScheduleOrigin (n + 1) h.val) : ℝ) := by
    apply (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcap) (Real.exp_nonneg _)).trans
    simpa only [cap, characterPivotCap_eq hn] using hgap
  have hip : (hi p : ℝ) ≤ Rmax :=
    (hw.2 p).trans (Real.exp_le_exp.mpr hT)
  have huniq : ∀ j ≤ n + 1, ∀ u v, characterRole k u = .pivot j →
      characterRole k v = .pivot j → u = v := by
    intro j hj u v hu hv
    exact (characterPivotAtom_unique ⟨j, hj.trans_lt hn⟩ u hu).trans
      (characterPivotAtom_unique ⟨j, hj.trans_lt hn⟩ v hv).symm
  have hcounts := character_interval_complexity k (n + 1) hn.le lo hi
  have hfreq : (V (n + 1) : ℝ) ≤ Real.exp (C * (1 + (m : ℝ))) := by
    apply (naturalTransferCutoff_linear_bound k (n + 1) d m hn.le hd hm).trans
    apply Real.exp_le_exp.mpr
    have hDC := le_max_left D (d + 1)
    nlinarith only [hDC, hC, Nat.cast_nonneg (α := ℝ) m]
  have hwidth : ∀ i, (WordFourierParameters.uniform (n + 1) (𝓕 ψ : 𝓢(ℝ, ℂ))
      (Real.exp logX) (Real.exp (Δ - C₀)) (Real.exp (Δ + C₀)) hWB.1 hWB.2.1).upper i -
      (WordFourierParameters.uniform (n + 1) (𝓕 ψ : 𝓢(ℝ, ℂ))
      (Real.exp logX) (Real.exp (Δ - C₀)) (Real.exp (Δ + C₀)) hWB.1 hWB.2.1).lower i ≤
        Real.exp (C * (1 + (m : ℝ))) := by
    intro i
    apply hWB.2.2.trans
    apply Real.exp_le_exp.mpr
    have hdC := le_max_right D (d + 1)
    nlinarith only [hdC, hC, Nat.cast_nonneg (α := ℝ) m]
  have result := hdec (characterSize m r f) (m + N + 1) (by omega)
    (characterSize_le k m N r f hrN hf) m (Nat.cast_nonneg _) hmL
    (characterSize_linear_bound m N) χ₀ (fun i => primeGaussMultiplier (χ₀ i))
    (characterPivot m r f hr) (fun i p => (primeGaussMultiplier_norm _ _).le)
    V cap (atomIntervalRanges (characterRole k) lo hi) hcounts.1 hcounts.2 ψ hreal
    (Real.exp logX) (Real.exp (Δ - C₀)) (Real.exp (Δ + C₀)) hWB.1 hWB.2.1
    (Real.exp_pos _) hXlo huniq m (characterBulk m r f) (characterBulk_role m r f)
    (fun e _ i => characterSchedule_matching m r f χ (n + 1) e i)
    small large (fun j => rfl) (fun j => rfl)
    (fun j hj => characterPivot_role m r f hr j (hj.trans hn))
    P hPne hP Q hQP hpos
    (fun j q hq => hχ q (hQP _ hq)) (fun i q hq => hχ q (hQP _ hq))
    ℓ ℓ (Real.exp_pos _) (Real.exp_pos _) Bs Bw Aw Bw Aa Ea hAw.1 hAa.1
    (fun j q hq => ⟨(hPrange q (hQP _ hq)).1, Nat.le_floor (hsmall _ q hq)⟩)
    (fun i q hq => ⟨⟨(hPrange q (hQP _ hq)).1, Nat.le_floor (hword i q hq).2⟩,
      hAw.2.2 q (hword i q hq).1, Nat.le_floor (hword i q hq).2⟩)
    (fun j q hq => ⟨hAa.2.2 q (hbig _ q hq), Nat.le_floor (hPrange q (hQP _ hq)).2⟩)
    (Real.exp (α * L)) Rmax (Real.exp_pos _) (by
      have he : (3 : ℝ) ≤ Real.exp (Real.exp (βg * L)) := by
        have h2 := Real.add_one_le_exp (Real.exp (βg * L))
        have hh : 2 ≤ Real.exp (βg * L) := by simpa only [Function.comp_apply, id_eq] using hRthree
        linarith only [hh, h2]
      exact he)
    (lo p) (hi p) hA hip
    (characterPivotGap B z m (n + 1) - 2 * characterRangeError k c)
    (fun q hq => (Real.le_log_iff_exp_le (by exact_mod_cast (hP q hq).pos)).mpr
      (hPrange q hq).1)
    (fun q hq => (hPrange q hq).2)
    (∏ h : CopyScheduleH (characterRole k) (n + 1),
      (lo (copyScheduleOrigin (n + 1) h.val) : ℝ)) hpositive hgap'
    (constituentHProductLower_of_atom_intervals _ _ _ V cap lo hi _ _ le_rfl)
    V (naturalTransferCutoff_monotone _ _ (mul_nonneg hd (Nat.cast_nonneg _)))
    hfreq ((le_max_left _ _).trans (le_max_right _ _))
    ((le_max_right _ _).trans (le_max_right _ _)) hwidth
    (character_prime_band_dyadic_budget Bw βg L m H hβg.le hL hLM hHdy hH hBw)
    (character_prime_band_dyadic_budget Ea βg L m H hβg.le hL hLM hHdy hH hEa)
    (fun i => (harmonic_mass_inv_energy_budget (Q i) Cmass L m hCmass.le hLM (hmass i)).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hHm (by linarith))))
    (by simp only [one_mul]; exact le_rfl) (by simp only [one_mul]; exact le_rfl)
    hAw.2.1 hAa.2.1 (Nat.floor_le (Real.exp_nonneg _)) (Nat.floor_le (Real.exp_nonneg _))
    (fun q hq => by simpa only [one_mul] using (hPrange q hq).1)
    (character_prime_band_log_ratio α βg L m H (by linarith) hLM hβg.le hHratio hH)
    (fun q hq => hlarge _ hm hmL q (by simpa only [one_mul] using (hPrange q hq).1) _ hn.le)
  simpa only [zero_mul, neg_zero, Real.exp_zero, mul_one] using result

end Ostmann

end OAI
