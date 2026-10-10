import OAI.MeasureTheory.Falconer.Incidence.UniformSmallCoverPencils

namespace OAI

/-! Polynomial bounds for the uniform pencils selected from a small cover. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem uniform_packet_bounds (N : ℕ) {κ s t K D : ℝ}
    (hκ : 0 < κ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hgap : κ ≤ t-s)
    (hK : 1 ≤ K) (hKD : K ≤ D) (hD : 80 ≤ D) (hH : projectionGapConstant κ ≤ D)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, (T x).Nonempty ∧ InBoundedLineChart (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l)
    (hunion : ((P.biUnion T).card:ℝ) ≤ D/((1/(2:ℝ)^N)^s)^2)
    (hlog : (Nat.log 2 (P.biUnion T).card+1:ℕ) ≤ D) :
    ∃ k : ℕ, ∃ R ⊆ P, R.Nonempty ∧ (P.card:ℝ) ≤ D*(R.card:ℝ) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) t (D^2) R ∧
      1/(D^2*(1/(2:ℝ)^N)^s) ≤ (2:ℝ)^k ∧
      (2:ℝ)^k ≤ D^9/(1/(2:ℝ)^N)^s ∧
      ∀ x ∈ R, (2:ℝ)^k ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ 2*(2:ℝ)^k := by
  let J := Nat.log 2 (P.biUnion T).card+1
  let δ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδs : 0 < δ^s := Real.rpow_pos_of_pos hδ _
  have hD1 : 1 ≤ D := by linarith only [hD]
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hJ0 : 0 ≤ (J:ℝ) := Nat.cast_nonneg _
  have hKJ : K*(J:ℝ) ≤ D^2 := by
    calc
      _ ≤ D*D := mul_le_mul hKD hlog hJ0 hD0
      _ = _ := by ring
  have hst : s < t := by linarith only [hκ,hgap]
  have hp := planarPotentialConstant_pos hst
  have hpot : planarPotentialConstant s t ≤ D := (planarPotentialConstant_gap hκ hs1 hgap).trans hH
  have hD3 : 1 ≤ D^3 := one_le_pow₀ hD1
  have h320 : 320 ≤ D^3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 80) hD 3
    norm_num at hh
    linarith only [hh]
  have h80 : (80:ℝ)^s ≤ 80 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ) ≤ 80) hs1
  obtain ⟨k,R,hRP,hR,hsize,hRball,hlo,hup,hband⟩ := uniform_small_cover_pencils N hs hst hK
    (show 0 ≤ D/((1/(2:ℝ)^N)^s)^2 by positivity) P T hP hPchart hPball hT hunion
  refine ⟨k,R,hRP,hR,hsize.trans (mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg _)),?_,?_,?_,hband⟩
  · intro z r hr hr1
    exact (hRball z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKJ (Real.rpow_nonneg (hδ.le.trans hr) _)) (Nat.cast_nonneg _))
  · apply le_trans _ hlo
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have hh : 2*K ≤ D^2 := by
      have hd : 2 ≤ D := by linarith only [hD]
      have hh := mul_le_mul_of_nonneg_right hd hD0
      nlinarith only [hh,hKD]
    nlinarith only [mul_le_mul_of_nonneg_right hh hδs.le]
  · have hp' : 1+(K*(J:ℝ))*planarPotentialConstant s t ≤ 2*D^3 := by
      calc
        _ ≤ 1+D^2*D := by gcongr
        _ ≤ _ := by nlinarith only [hD3]
    calc
      (2:ℝ)^k ≤ 2*(D/(δ^s)^2)*(K*(J:ℝ))*(80*δ)^s*(1+(K*(J:ℝ))*planarPotentialConstant s t) := hup
      _ = 2*(D/(δ^s)^2)*(K*(J:ℝ))*((80:ℝ)^s*δ^s)*(1+(K*(J:ℝ))*planarPotentialConstant s t) := by
        rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 80) hδ.le]
      _ ≤ 2*(D/(δ^s)^2)*D^2*(80*δ^s)*(2*D^3) := by gcongr
      _ = 320*D^6/δ^s := by field_simp; ring
      _ ≤ D^9/δ^s := by
        apply div_le_div_of_nonneg_right _ hδs.le
        calc
          _ ≤ D^3*D^6 := mul_le_mul_of_nonneg_right h320 (pow_nonneg hD0 _)
          _ = _ := by ring

end Falconer

end OAI
