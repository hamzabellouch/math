import OAI.NumberTheory.Ostmann.Construction.SelectedNaturalAnchorDecay
import OAI.NumberTheory.Ostmann.Characters.CharacterEnergyPrimeRange
import OAI.NumberTheory.Ostmann.Characters.CharacterPriorMass
import OAI.NumberTheory.Ostmann.Characters.CharacterDiagonalGap
import OAI.NumberTheory.Ostmann.Characters.CharacterWordIntervals
import OAI.NumberTheory.Ostmann.Characters.CharacterAtomIteration

namespace OAI

/-! # The code-preserving diagonal for the constructed character cells

The energy length is the actual bulk density times L. This retains a bulk
mass of a L rather than assuming the stronger, generally false, bound L.
-/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem le_characterRangeError (k : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    c ≤ characterRangeError k c := by
  have hp : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hk := Nat.cast_nonneg (α := ℝ) k
  have hh : 1 ≤ (2 : ℝ) ^ k + k + 2 := by linarith
  exact (one_mul c).symm.trans_le (mul_le_mul_of_nonneg_right hh hc)

theorem eventual_character_anchor_decay (k n Bnb : ℕ) (hn : n < k)
    (ψ : 𝓢(ℝ, ℂ)) (K B B₁ z c a b Cmass α β ε : ℝ)
    (hB : 1 ≤ B) (hz : 1 ≤ z) (hc : 1 ≤ c)
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hCmass : 0 < Cmass)
    (hα : 0 < α) (hβ : 0 ≤ β) (hε : 0 < ε)
    (hbudget : 4 * Cmass * Bnb ≤ z)
    (hgap : 2 * B₁ +
      ((β + Real.log ((Real.log 2)⁻¹ + 1)) / a + max (Real.log 3) 0 + ε) +
      Real.log 2 + 6 ≤ B + 20 * Real.log a)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
    ∃ M₀ : ℝ, ∀ᶠ L : ℝ in atTop, ∀ m : ℕ, M₀ ≤ (m : ℝ) → L ≤ m →
      (m : ℝ) ≤ z * L → z * L ≤ 2 * m →
      ∀ (r : Fin k → ℕ) (f : ℕ) (hr : ∀ j, 0 < r j),
      1 + ((∑ j, r j) + 2 * k) ≤ Bnb →
      ∀ (P U : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
        (Q : Fin (m + 1) → Finset ℕ)
        (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ),
      (∀ i : Fin m, Q i.succ = U) →
      (∀ i, Q i ⊆ P) → (∀ v i, R v i ⊆ P) →
      b ≤ ∑ p ∈ Q 0, (p : ℝ)⁻¹ → a * L ≤ ∑ p ∈ U, (p : ℝ)⁻¹ →
      (∀ v i, Real.exp (-Cmass * L) ≤ ∑ p ∈ R v i, (p : ℝ)⁻¹) →
      (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p) →
      (∀ p ∈ U, (p : ℝ) ≤ Real.exp (Real.exp (β * L))) →
      ∀ (J : ℕ), 0 < J → ∀ (anchor : Fin k → Bool → ℝ) (F logX : ℝ), 0 < logX →
      let Δ := characterBaseGap B z m
      let T := characterPivotTarget k J (fun j => anchor j false + anchor j true)
        (fun j => characterPivotGap B z m j.val)
      ∀ lower upper : CharacterCell k → ℕ,
      (∀ v, Real.exp (characterLogCenter J T anchor F (true, some v) - c) ≤ lower v) →
      (∀ v, (upper v : ℝ) ≤ Real.exp (characterLogCenter J T anchor F (true, some v) + c)) →
      ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p),
      let lo := initialWordAtomLower J lower
      let hi := initialWordAtomUpper J upper
      let χ₀ := signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ
      let Q₀ := characterFullPrimeCells m r f Q R
      let V := naturalTransferCutoff Δ m
      let cap := characterPivotCap T (characterRangeError k c)
      let p := characterPivotAtom ⟨n, hn⟩
      (∑ N ∈ Finset.Icc (lo p) (hi p),
        (constituentMatchingFamily (characterRole k) (characterSize m r f) χ₀
          (fun i => primeGaussMultiplier (χ₀ i)) (characterPivot m r f hr) n P hP Q₀
          V cap (atomIntervalRanges (characterRole k) lo hi)
          (scheduleFourierLeaf (characterRole k) ψ (Real.exp logX)
            (Real.exp (Δ - (Fintype.card (CharacterRole k) : ℝ) * c))
            (Real.exp (Δ + (Fintype.card (CharacterRole k) : ℝ) * c)))
          (scheduledFrequencyHistory V n)
          (selectedAnchorMatchingSet
            (fun i : Σ v, Fin (characterSize m r f v) => characterRole k i.1)
            n m (characterBulk m r f) (characterBulk_role m r f)) N).re) ≤
        Real.exp (-(2 * B₁ + 4) * (2 ^ n : ℕ) * (m : ℝ)) := by
  let d := B + 20 * Real.log z
  let C₀ := (Fintype.card (CharacterRole k) : ℝ) * c
  let C₁ := β + Real.log ((Real.log 2)⁻¹ + 1)
  have hz0 : 0 < z := by linarith
  have hd1 : 1 ≤ d := by dsimp [d]; linarith [Real.log_nonneg hz]
  have hd : 0 ≤ d := by linarith
  have hC₁ : 0 ≤ C₁ := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hi : 0 ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr hlog2.le
    exact add_nonneg hβ (Real.log_nonneg (by linarith))
  have hza : 1 ≤ z / a := (le_div_iff₀ ha).mpr (by linarith)
  have hbudget' : 4 * (Cmass / a) * Bnb ≤ z / a := by
    calc
      _ = (4 * Cmass * Bnb) / a := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hbudget ha.le
  obtain ⟨M₁, hdec⟩ := eventual_selected_natural_anchor_decay n Bnb ψ C₀ K d ε
    (Cmass / a) (B + 20 * Real.log a) B₁ (C₁ / a) 1 (z / a)
    hd hε (div_nonneg hCmass.le ha.le) (by norm_num) (div_nonneg hC₁ ha.le)
    hza hbudget' (by simpa only [div_one] using hgap) hψ
  refine ⟨max M₁ (max 1 (max C₀ (2 * characterRangeError k c))), ?_⟩
  have hscaled := (tendsto_id.const_mul_atTop ha).eventually hdec
  simp only [id_eq] at hscaled
  filter_upwards [hscaled, eventual_full_character_mass_floor a b Cmass ha hb hCmass,
    eventual_character_energy_prime_range k ((2 ^ (n + 1) - 1) * (n + 2))
      d z α β hd hz0.le hα hβ,
    eventual_natural_cutoff_below_primes k d z α 1 hd hz0.le hα (by norm_num),
    eventually_ge_atTop (1 / a)] with L hdec hmass hdyadic hsep hLa
  intro m hM hLM hmL hLm r f hr hcount P U hP Q R hQ hQP hRP htop hbulk hR
    hmin hmax J hJ anchor F logX hlogX Δ T lower upper hlower hupper χ
    lo hi χ₀ Q₀ V cap p
  have hm1 : (1 : ℝ) ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hM)
  have hM₁ : M₁ ≤ (m : ℝ) := (le_max_left _ _).trans hM
  have hC₀m : C₀ ≤ (m : ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hM))
  have hCm : 2 * characterRangeError k c ≤ (m : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hM))
  have haL : 1 ≤ a * L := by simpa only [mul_comm] using (div_le_iff₀ ha).mp hLa
  have hL0 : 0 ≤ L := (div_pos zero_lt_one ha).le.trans hLa
  have haLm : a * L ≤ (m : ℝ) :=
    (mul_le_of_le_one_left hL0 ha1).trans hLM
  have heza : z / a * (a * L) = z * L := by field_simp
  have hmL' : (m : ℝ) ≤ z / a * (a * L) := by rwa [heza]
  have hLm' : z / a * (a * L) / 2 ≤ (m : ℝ) := by
    have he : z / a * (a * L) = z * L := by field_simp
    rw [he]
    linarith
  have hall := hmass k m r f Q R htop (fun i => by simpa only [hQ] using hbulk) hR
  have hpos (i) : 0 < ∑ q ∈ Q₀ i, (q : ℝ)⁻¹ := (Real.exp_pos _).trans_le (hall i)
  have hsub := characterFullPrimeCells_subset m r f P Q R hQP hRP
  have hU : U ⊆ P := by
    have hms : 0 < m := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hm1)
    simpa only [hQ] using hQP (⟨0, hms⟩ : Fin m).succ
  obtain ⟨hh, JJ, hmod, hrange, hJJ⟩ := hdyadic (m : ℝ) hm1 hmL U
    (fun q hq => ⟨hmin q (hU hq), hmax q hq⟩)
  have hlarge (q : ℕ) (hq : q ∈ P) : V n < q := by
    exact hsep _ hm1 hmL q (by simpa only [one_mul] using hmin q hq) n hn.le
  have hw := character_word_interval_errors J c hc T anchor F lower upper hlower hupper
  have hpositive : 0 < ∏ h : CopyScheduleH (characterRole k) n,
      (lo (copyScheduleOrigin n h.val) : ℝ) :=
    Finset.prod_pos (fun h _ => (Real.exp_pos _).trans_le (hw.1 _))
  have hA : 0 < lo p := by exact_mod_cast (Real.exp_pos _).trans_le (hw.1 p)
  have hproduct := character_diagonal_product_gap hn J B z m F c (by linarith) anchor
    lo hi hw.1 hw.2
  have hcap : hi p ≤ cap n := by
    dsimp only [cap]
    rw [characterPivotCap_eq hn]
    apply Nat.le_floor
    exact (hw.2 p).trans (Real.exp_le_exp.mpr (by
      change T ⟨n, hn⟩ + c ≤ T ⟨n, hn⟩ + characterRangeError k c
      linarith only [le_characterRangeError k c (by linarith)]))
  have hproduct' : Real.exp (characterPivotGap B z m n - 2 * characterRangeError k c) *
      (hi p : ℝ) ≤ ∏ h : CopyScheduleH (characterRole k) n,
        (lo (copyScheduleOrigin n h.val) : ℝ) := by
    apply (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcap) (Real.exp_nonneg _)).trans
    simpa only [cap, characterPivotCap_eq hn] using hproduct
  have hgaprate := character_diagonal_gap_reserve n B z m (characterRangeError k c)
    (Nat.cast_nonneg _) hCm
  have hlogs : B + 20 * Real.log a + 20 * Real.log (z / a) - 1 = d - 1 := by
    rw [Real.log_div hz0.ne' ha.ne']
    dsimp [d]
    ring
  have hlogap : 1 ≤ Real.exp (Δ - C₀) := Real.one_le_exp_iff.mpr (by
    have hdM := mul_le_mul_of_nonneg_right hd1 (Nat.cast_nonneg (α := ℝ) m)
    change 0 ≤ d * m - C₀
    linarith)
  have hXlo : 1 < Real.exp logX * Real.exp (Δ - C₀) := by
    have hX := Real.one_lt_exp_iff.mpr hlogX
    nlinarith only [hX, hlogap]
  have huniq : ∀ j < n, ∀ u v, characterRole k u = .pivot j →
      characterRole k v = .pivot j → u = v := by
    intro j hj u v hu hv
    exact (characterPivotAtom_unique ⟨j, hj.trans hn⟩ u hu).trans
      (characterPivotAtom_unique ⟨j, hj.trans hn⟩ v hv).symm
  have hms : 0 < m := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hm1)
  let i : Fin m := ⟨0, hms⟩
  have hcard : Nat.card {i : Σ v, Fin (characterSize m r f v) //
      i ∉ Set.range (characterBulk m r f) ∧ characterRole k i.1 ≠ .outside} ≤ Bnb := by
    rw [Nat.card_eq_fintype_card]
    exact (character_original_nonbulk_card m r f).trans hcount
  have hCscale : C₁ / a * (a * L) = C₁ * L := by field_simp
  apply hdec m hM₁ (characterRole k) (characterSize m r f) χ₀
    (fun i => primeGaussMultiplier (χ₀ i)) (characterPivot m r f hr)
    (fun i p => (primeGaussMultiplier_norm _ _).le) V cap
    (atomIntervalRanges (characterRole k) lo hi) (characterBulk m r f i) rfl huniq
    p rfl (fun j hj => characterPivotAtom_unique ⟨n, hn⟩ j hj)
    (characterBulk m r f) (characterBulk_role m r f)
    (Real.exp logX) (Real.exp (Δ - C₀)) (Real.exp (Δ + C₀)) P Q₀
    (fun p hp => ⟨hP p hp, hlarge p hp⟩) (Real.exp_pos _) hXlo le_rfl hsub hpos
    hh JJ (hmod n hn.le) (by simpa only [Q₀, characterFullPrimeCells_bulk, hQ] using hrange)
    haL haLm (by simpa only [Q₀, characterFullPrimeCells_bulk, hQ] using haL.trans hbulk)
    (by rw [hCscale]; exact hJJ) hmL' hLm'
    (fun x => by
      have ho := copyScheduleOrigin_path n (scheduledPathEnumeration n x.1) (characterBulk m r f x.2)
      change a * L ≤ ∑ q ∈ Q₀ (copyScheduleOrigin n
        (selectedBulkCoordinates _ n m _ _ x).val.val), (q : ℝ)⁻¹
      rw [show copyScheduleOrigin n (selectedBulkCoordinates _ n m _ _ x).val.val =
        characterBulk m r f x.2 from ho]
      simpa only [Q₀, characterFullPrimeCells_bulk, hQ] using hbulk)
    lo hi rfl hpositive (lo p) (hi p) hA
    (characterPivotGap B z m n - 2 * characterRangeError k c)
    hproduct'
    (by simpa only [hlogs] using hgaprate)
    hcard
    (fun h => by
      have he : -(Cmass / a) * (a * L) = -Cmass * L := by field_simp
      rw [he]
      exact hall _)

end Ostmann

end OAI
