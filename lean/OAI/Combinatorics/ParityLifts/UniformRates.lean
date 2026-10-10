import OAI.Combinatorics.ParityLifts.UniformTrial

namespace OAI

namespace ParityWL.Complexity

lemma uniform_rate_parameters (D P : ℕ) (g : ℕ → ℝ)
    (hg : ∀ k,0 ≤ g k)
    (hlim : Filter.Tendsto (fun k : ℕ => g k/k) Filter.atTop (nhds 0))
    (η : ℝ) (hη : 0<η) : ∃ j : ℕ, 0<j ∧ ∃ k : ℕ, 4 ≤ k ∧
      ∀ t : ℕ, k ≤ t → (D : ℝ)/j+(P : ℝ)*(g k+1)*leafSlope t (12*j)<η := by
  obtain ⟨j₀,hj₀⟩ := exists_nat_gt (4*(D+1 : ℝ)/η)
  let j := j₀+1
  have hj : 0<j := by dsimp [j]; omega
  have hj' : (0 : ℝ)<j := by exact_mod_cast hj
  have hD : (D : ℝ)/j<η/4 := by
    apply (div_lt_iff₀ hj').mpr
    have hh := (div_lt_iff₀ hη).mp hj₀
    dsimp only [j]
    push_cast
    nlinarith
  let H : ℝ := 3*(P : ℝ)*(densityFactor (12*j) : ℝ)
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have htol : 0<η/(8*(H+1)) := by positivity
  have he : ∀ᶠ k : ℕ in Filter.atTop, g k/k<η/(8*(H+1)) :=
    hlim.eventually (gt_mem_nhds htol)
  obtain ⟨K,hK⟩ := Filter.eventually_atTop.1 he
  obtain ⟨q,hq⟩ := exists_nat_gt (8*(H+1)/η)
  let k := max K q+4
  have hk : 4 ≤ k := by dsimp [k]; omega
  have hkpos : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hkK : K ≤ k := by dsimp [k]; omega
  have hqk : (q : ℝ)<k := by exact_mod_cast (show q<k by dsimp [k]; omega)
  have hHk : H/k<η/8 := by
    apply (div_lt_iff₀ hkpos).mpr
    have hh := (div_lt_iff₀ hη).mp hq
    nlinarith
  have hgk : H*(g k/k)<η/8 := by
    have hh := mul_le_mul_of_nonneg_left (hK k hkK).le hH
    have ht : H*(η/(8*(H+1)))<η/8 := by
      calc
        _ = (η/8)*(H/(H+1)) := by rw [div_mul_eq_div_div]; ring
        _ < (η/8)*1 := mul_lt_mul_of_pos_left ((div_lt_one (by positivity)).mpr (by linarith)) (by positivity)
        _ = _ := by ring
    exact hh.trans_lt ht
  refine ⟨j,hj,k,hk,?_⟩
  intro t hkt
  have htk : (k : ℝ) ≤ t := by exact_mod_cast hkt
  have ht : H*(g k+1)/t ≤ H*(g k/k)+H/k := by
    calc
      _ ≤ H*(g k+1)/k := div_le_div_of_nonneg_left (by have := hg k; positivity) hkpos htk
      _ = _ := by ring
  have heq : (P : ℝ)*(g k+1)*leafSlope t (12*j)=H*(g k+1)/t := by
    dsimp only [leafSlope,H]; ring
  rw [heq]
  linarith

end ParityWL.Complexity

end OAI
