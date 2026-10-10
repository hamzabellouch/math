import OAI.NumberTheory.Ostmann.ZeroDensity.FullHeightRegionComparison

namespace OAI

/-! # The complex zero-free input follows from the retained real Page input -/

namespace Ostmann

theorem complexZeroRegion_of_page (κ : ℝ) (hκ : 0 < κ)
    (hunique : ∀ Q : ℕ, 2 ≤ Q → ∀ e f : PrimitiveRealZero,
      e.modulus ≤ Q → f.modulus ≤ Q →
      1 - κ / Real.log (4 * (Q : ℝ)) ≤ e.beta →
      1 - κ / Real.log (4 * (Q : ℝ)) ≤ f.beta → e = f) :
    PublishedComplexZeroRegion actualCharacterZeros := by
  classical
  obtain ⟨cn, hcn, hn⟩ := exists_nonquadratic_zero_free_region
  obtain ⟨cr, hcr, hr⟩ := exists_full_height_real_region
  let c := min (cn / 4) (min (cr / 4) κ)
  have hc : 0 < c := lt_min (by positivity) (lt_min (by positivity) hκ)
  have hcnc : c ≤ cn / 4 := min_le_left _ _
  have hcrc : c ≤ cr / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hcP : c ≤ κ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, hc, ?_⟩
  intro Q hQ T hT
  let H := Real.log (2 * (Q : ℝ) * T)
  have hQ1 : 1 ≤ Q := by omega
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one (conductor_height_log_ge_one Q hQ1 T hT)
  have hconvert : ∀ (χ : PrimitiveComplexCharacter), χ.modulus ≤ Q → ∀ i : ℕ,
      |((actualCharacterZeros χ).zeros i).im| ≤ T →
      1 - c / H ≤ ((actualCharacterZeros χ).zeros i).re →
      ∃ e : PrimitiveRealZero, e.modulus = χ.modulus ∧
        e.beta = ((actualCharacterZeros χ).zeros i).re ∧ e.asRealCharacter.asComplex = χ := by
    intro χ hχ i hi hnear
    let U := Real.log χ.modulus + Real.log (T + 2) + 1
    have hq : 0 ≤ Real.log χ.modulus := Real.log_nonneg (by exact_mod_cast χ.positive)
    have ht : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
    have hUp : 0 < U := by dsimp [U]; linarith
    have hUH : U ≤ 2 * H := local_height_log_le χ.modulus Q χ.positive hχ T hT
    have hsq : χ.character ^ 2 = 1 := by
      by_contra hsq
      let V := Real.log χ.modulus + Real.log (|((actualCharacterZeros χ).zeros i).im| + 2) + 1
      have hVp : 0 < V := by
        have hl : 0 ≤ Real.log (|((actualCharacterZeros χ).zeros i).im| + 2) :=
          Real.log_nonneg (by linarith [abs_nonneg ((actualCharacterZeros χ).zeros i).im])
        dsimp [V]
        linarith
      have hVU : V ≤ U := by
        have hl := Real.log_le_log (by positivity : 0 < |((actualCharacterZeros χ).zeros i).im| + 2)
          (show |((actualCharacterZeros χ).zeros i).im| + 2 ≤ T + 2 by linarith)
        dsimp [V, U]
        linarith
      have hcut := small_cutoff_fraction c cn U H hc.le hUp hHp hcnc hUH
      have hhalf : cn / (2 * U) < cn / U := by
        apply (div_lt_div_iff₀ (by positivity) hUp).mpr
        nlinarith
      have hmono : cn / U ≤ cn / V := by
        apply (div_le_div_iff₀ hUp hVp).mpr
        exact mul_le_mul_of_nonneg_left hVU hcn.le
      have hzero := hn χ hsq i
      change cn / V ≤ _ at hzero
      linarith
    have hcut := small_cutoff_fraction c cr U H hc.le hUp hHp hcrc hUH
    have hhalf : cr / (2 * U) ≤ cr / U := by
      apply (div_le_div_iff₀ (by positivity) hUp).mpr
      nlinarith
    have hnearR : 1 - cr / U ≤ ((actualCharacterZeros χ).zeros i).re := by linarith
    have him : ((realCharacterActualZeros (χ.asReal hsq)).zeros i).im = 0 :=
      (hr (χ.asReal hsq) T hT).1 i
        (by rw [realCharacterActualZeros, χ.asReal_asComplex hsq]; exact hi)
        (by
          change 1 - cr / U ≤ ((actualCharacterZeros (χ.asReal hsq).asComplex).zeros i).re
          rw [χ.asReal_asComplex hsq]
          exact hnearR)
    let e := (actualRealCharacterZeroExpansion (χ.asReal hsq)).realZero i him
    refine ⟨e, rfl, ?_, ?_⟩
    · change ((realCharacterActualZeros (χ.asReal hsq)).zeros i).re = _
      rw [realCharacterActualZeros, χ.asReal_asComplex hsq]
    · change ((actualRealCharacterZeroExpansion (χ.asReal hsq)).realZero i him).asRealCharacter.asComplex = χ
      rw [actualRealZero_asCharacter, PrimitiveComplexCharacter.asReal_asComplex]
  have hlog4 : 0 < Real.log (4 * (Q : ℝ)) := Real.log_pos (by exact_mod_cast (by omega : 1 < 4 * Q))
  have hlogH : Real.log (4 * (Q : ℝ)) ≤ H := by
    apply Real.log_le_log (by positivity)
    have hQr : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
    nlinarith
  have hPage : c / H ≤ κ / Real.log (4 * (Q : ℝ)) := by
    apply (div_le_div_iff₀ hHp hlog4).mpr
    exact (mul_le_mul_of_nonneg_left hlogH hc.le).trans
      (mul_le_mul_of_nonneg_right hcP hHp.le)
  have huniq (χ ψ : PrimitiveComplexCharacter) (hχ : χ.modulus ≤ Q) (hψ : ψ.modulus ≤ Q)
      (i j : ℕ) (hi : |((actualCharacterZeros χ).zeros i).im| ≤ T)
      (hj : |((actualCharacterZeros ψ).zeros j).im| ≤ T)
      (hni : 1 - c / H ≤ ((actualCharacterZeros χ).zeros i).re)
      (hnj : 1 - c / H ≤ ((actualCharacterZeros ψ).zeros j).re) : χ = ψ := by
    obtain ⟨e, heq, heb, heχ⟩ := hconvert χ hχ i hi hni
    obtain ⟨f, hfq, hfb, hfψ⟩ := hconvert ψ hψ j hj hnj
    have hef := hunique Q (by omega) e f (by simpa [heq] using hχ)
      (by simpa [hfq] using hψ) (by rw [heb]; linarith) (by rw [hfb]; linarith)
    exact heχ.symm.trans ((congrArg (fun e : PrimitiveRealZero => e.asRealCharacter.asComplex) hef).trans hfψ)
  by_cases hex : ∃ χ : PrimitiveComplexCharacter, χ.modulus ≤ Q ∧ ∃ i : ℕ,
      |((actualCharacterZeros χ).zeros i).im| ≤ T ∧ 1 - c / H ≤ ((actualCharacterZeros χ).zeros i).re
  · obtain ⟨χ₀, hχ₀, i₀, hi₀, hn₀⟩ := hex
    refine ⟨some χ₀, ?_⟩
    intro χ hχ hne i hi
    by_contra hbad
    have hn : 1 - c / H ≤ ((actualCharacterZeros χ).zeros i).re := by linarith [lt_of_not_ge hbad]
    exact hne (congrArg some (huniq χ χ₀ hχ hχ₀ i i₀ hi hi₀ hn hn₀))
  · refine ⟨none, ?_⟩
    intro χ hχ _ i hi
    by_contra hbad
    exact hex ⟨χ, hχ, i, hi, by linarith [lt_of_not_ge hbad]⟩

theorem PublishedProgressionInput.complexZeroRegion (P : PublishedProgressionInput) :
    PublishedComplexZeroRegion actualCharacterZeros :=
  complexZeroRegion_of_page P.kappa P.kappa_pos P.unique

end Ostmann

end OAI
