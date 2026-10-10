import OAI.Combinatorics.ParityLifts.FixedBridge

namespace OAI

namespace ParityWL.Complexity

lemma rate_parameters (P : ℕ) (δ : ℝ) (hδ : 0<δ) :
    ∃ (j : ℕ), 0<j ∧ ∃ c : ℝ, 0<c ∧ ∃ K : ℕ, 4 ≤ K ∧
      ∀ k t : ℕ, K ≤ k → k ≤ t →
        reductionRate P j t (c*k)+δ/4 ≤ δ := by
  obtain ⟨j₀,hj₀⟩ := exists_nat_gt (16/δ)
  let j := j₀+1
  have hj : 0<j := by dsimp only [j]; omega
  have hj' : (0 : ℝ)<j := by exact_mod_cast hj
  have hjb : 16/δ<(j : ℝ) := by dsimp only [j]; push_cast; linarith
  have h4j : 4/(j : ℝ)<δ/4 := by
    apply (div_lt_iff₀ hj').mpr
    have hh := (div_lt_iff₀ hδ).mp hjb
    nlinarith
  let D : ℝ := 6*(P : ℝ)*(densityFactor (12*j) : ℝ)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let c := δ/(16*(D+1))
  have hc : 0<c := by dsimp [c]; positivity
  have hDc : D*c<δ/16 := by
    calc
      D*c=(δ/16)*(D/(D+1)) := by dsimp only [c]; rw [div_mul_eq_div_div]; ring
      _ < (δ/16)*1 := mul_lt_mul_of_pos_left ((div_lt_one (by positivity)).mpr (by linarith)) (by positivity)
      _ = _ := by ring
  obtain ⟨K₀,hK₀⟩ := exists_nat_gt (16*(D+1)/δ)
  let K := K₀+4
  have hK : 4 ≤ K := by dsimp only [K]; omega
  refine ⟨j,hj,c,hc,K,hK,?_⟩
  intro k t hk hkt
  have hkpos : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have htk : (k : ℝ) ≤ t := by exact_mod_cast hkt
  have hkb : 16*(D+1)/δ<(k : ℝ) := by
    have hk' : (K₀ : ℝ)+4 ≤ k := by exact_mod_cast hk
    linarith
  have hDk : D/(k : ℝ)<δ/16 := by
    apply (div_lt_iff₀ hkpos).mpr
    have hh := (div_lt_iff₀ hδ).mp hkb
    nlinarith
  have hb : D*(c*k+1)/(t : ℝ) ≤ D*c+D/k := by
    calc
      _ ≤ D*(c*k+1)/k := div_le_div_of_nonneg_left (by positivity) hkpos htk
      _ = _ := by field_simp
  have he : reductionRate P j t (c*k)=4/(j : ℝ)+D*(c*k+1)/t := by
    dsimp only [reductionRate,leafSlope,D]
    ring
  rw [he]
  linarith

/-- Positive-rate ETH: one absolute slope and one threshold,
uniform over both refinements and both histogram implementations. -/
theorem fixed_dimension_eth : FixedDimensionETHStatement := by
  intro hETH
  obtain ⟨δ,hδ,hETH⟩ := hETH
  obtain ⟨P,hP,hRed⟩ := fixed_reduction_rate
  obtain ⟨j,hj,c,hc,K,hK,hRate⟩ := rate_parameters P δ hδ
  refine ⟨c,hc,K,hK,?_⟩
  intro k hk conv i hM
  obtain ⟨M,hM⟩ := hM
  have hk4 : 4 ≤ k := hK.trans hk
  have hkt : k ≤ bagParameter conv k := by cases conv <;> simp [bagParameter]
  let : NeZero (bagParameter conv k) := ⟨by omega⟩
  obtain ⟨C,hC,hSAT⟩ := hRed j hj k hk4 conv i M (c*k) (by positivity) hM (δ/4) (by positivity)
  exact hETH ⟨(fixedSATCode j (bagParameter conv k) M).decision,C,
    2*normalizeProgram.degree+2,hC,hSAT.rate_mono hC.le (hRate k _ hk hkt)⟩

end ParityWL.Complexity

end OAI
