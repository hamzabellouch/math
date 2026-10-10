import OAI.Probability.SATVariance.FailureWindows

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

theorem fixed_cap_variance_lower (k : ℕ) (hk : 3 ≤ k) :
    ∃ B : ℝ, U k ≤ B ∧ ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → k ≤ n →
        c*n ≤ variance (T B : Stream n k → ℝ) (streamLaw n k) := by
  obtain ⟨R,hR,hRU,hRq⟩ := exists_lower_scale k (by omega)
  let β := Real.exp (-4*(R:ℝ)*k^2)
  have hβ : 0 < β := Real.exp_pos _
  have hβ1 : β ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : (0:ℝ) ≤ R := by positivity
    nlinarith [sq_nonneg (k:ℝ)]
  obtain ⟨a,ha,ha1,haHall,haβ⟩ := exists_lower_density hβ hβ1
  let d := (a/(16*((2*R:ℕ)+1:ℝ)^2))*a*β/16
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨Ng,hNg⟩ := eventual_geometric_small
    (by positivity [real_rate_pos (by omega : 1 ≤ k)] : 0 ≤ 2*(1-((2:ℝ)^k)⁻¹)^R)
    hRq (show 0 < β/4 by positivity)
  obtain ⟨Na,hNa⟩ := positive_linear_absorb a ha 8
  obtain ⟨Nd,hNd⟩ := positive_linear_absorb d hd 4
  refine ⟨2*(R:ℝ),hRU,d/4,by positivity,max (2*k^2) (max Ng (max Na Nd)),?_⟩
  intro n hn hkn
  have hn2 : 2*k^2 ≤ n := by omega
  have hng : Ng ≤ n := by omega
  have hna : Na ≤ n := by omega
  have hnd : Nd ≤ n := by omega
  let := clause_nonempty n k hkn
  have hs := sentinel_linear_lower (by omega : 2 ≤ k) hkn hR hn2 ha ha1 haHall haβ
    (hNa n hna) (hNg n hng)
  change d*n ≤ fvariance (fun w : Fin (2*R*n) → Clause n k => (listStop (List.ofFn w):ℝ)) at hs
  have hb := sentinel_variance_bridge (n := n) (k := k) (M := 2*R*n)
  have hcap : cap n (2*(R:ℝ)) = 2*R*n := by
    have he : 2*(R:ℝ)*n = ((2*R*n:ℕ):ℝ) := by
      simp only [Nat.cast_mul,Nat.cast_ofNat]
    simp only [cap,he,Nat.floor_natCast]
  have hv := cap_variance_finite hkn (2*(R:ℝ))
  rw [hcap] at hv
  rw [←hv] at hb
  have hdn := hNd n hnd
  nlinarith

theorem variance_linear_lower (k : ℕ) (hk : 3 ≤ k) :
    ∃ c : ℝ, 0 < c ∧
      (∃ N : ℕ, ∀ n : ℕ, N ≤ n → k ≤ n →
        c*n ≤ variance (H : Stream n k → ℝ) (streamLaw n k)) ∧
      (∀ B : ℝ, U k < B → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → k ≤ n →
        c*n ≤ variance (T B : Stream n k → ℝ) (streamLaw n k)) := by
  obtain ⟨B₀,hB₀,c₀,hc₀,N₀,hN₀⟩ := fixed_cap_variance_lower k hk
  have hk1 : 1 ≤ k := by omega
  have hK := bridgeC_nonneg hk1
  obtain ⟨N₁,hN₁⟩ := positive_linear_absorb c₀ hc₀ (12*bridgeC k)
  refine ⟨c₀/8,by positivity,?_,?_⟩
  · refine ⟨max N₀ N₁,fun n hn hkn => ?_⟩
    have hl := hN₀ n (by omega) hkn
    have ha := hN₁ n (by omega)
    have hv := cap_variance_le_H hk1 hkn hB₀
    have hn0 : (0:ℝ) ≤ n := by positivity
    nlinarith
  · intro B hB
    refine ⟨max N₀ N₁,fun n hn hkn => ?_⟩
    have hl := hN₀ n (by omega) hkn
    have ha := hN₁ n (by omega)
    have hv := cap_variance_le_H hk1 hkn hB₀
    have hv' := H_variance_le_cap hk1 hkn hB.le
    nlinarith

end RandomKSAT

end

end OAI
