import OAI.Analysis.Cotype.GrowthTheorem
import OAI.Analysis.Cotype.SlowDrop

namespace OAI

noncomputable section

universe u v
namespace Cotype

theorem sequence_drop_rate (w : ℕ → ℝ) (m n₀ : ℕ) (hm : 0 < m)
    (hanti : Antitone w) (hdrop : ∀ n, n₀ ≤ n → w n ≤ (1/2)*w (n-2*m)) :
    ∀ N, w N ≤ (1/2 : ℝ)^((N-n₀)/(2*m))*w 0 := by
  have hsteps : ∀ j, w (n₀+2*m*j) ≤ (1/2 : ℝ)^j*w 0 := by
    intro j
    induction j with
    | zero => simpa using hanti (Nat.zero_le n₀)
    | succ j ih =>
      have h := hdrop (n₀+2*m*(j+1)) (by omega)
      have he : n₀+2*m*(j+1)-2*m = n₀+2*m*j := by
        simp only [Nat.mul_add, Nat.mul_one]; omega
      rw [he] at h
      calc
        _ ≤ (1/2)*w (n₀+2*m*j) := h
        _ ≤ (1/2)*((1/2 : ℝ)^j*w 0) := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = _ := by rw [pow_succ]; ring
  intro N
  by_cases hN : n₀ ≤ N
  · have he : n₀+2*m*((N-n₀)/(2*m)) ≤ N := by
      have h := (Nat.le_div_iff_mul_le (Nat.mul_pos (by decide : 0 < 2) hm)).mp
        (le_refl ((N-n₀)/(2*m)))
      rw [Nat.mul_comm ((N-n₀)/(2*m)) (2*m)] at h
      omega
    exact (hanti he).trans (hsteps _)
  · simpa [Nat.sub_eq_zero_of_le (le_of_not_ge hN)] using hanti (Nat.zero_le N)

def uniformDecayRate (m n₀ N : ℕ) : ℝ := (1/2 : ℝ)^((N-n₀)/(2*m))

theorem uniformDecayRate_tendsto (m n₀ : ℕ) (hm : 0 < m) :
    Filter.Tendsto (uniformDecayRate m n₀) Filter.atTop (nhds 0) := by
  apply (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)).comp
  apply Filter.tendsto_atTop.mpr
  intro b
  filter_upwards [Filter.eventually_ge_atTop (n₀+2*m*b)] with N hN
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2*m)).mpr
  rw [Nat.mul_comm b (2*m)]
  omega

theorem exists_uniform_walsh_decay (m : ℕ) (Dg Df : ℝ)
    (hDg1 : 1 ≤ Dg) (hDf1 : 1 ≤ Df)
    (hcut : 4 ≤ degreeCutoff m) (hcutm : degreeCutoff m < m)
    (hsize : 80 * (degreeCutoff m : ℝ) * (degreeCutoff m + 1 : ℝ)^2 ≤
      min ((m : ℝ)*(1/(2*24*Dg*Real.sqrt m))) ((m : ℝ)*(1/(2*24*Df*Real.sqrt m)))) :
    ∃ n₀ : ℕ, 4*m < n₀ ∧
      Filter.Tendsto (uniformDecayRate m n₀) Filter.atTop (nhds 0) ∧
      ∀ (X : Type u) (Y : Type v) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
        [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : X →L[ℝ] Y),
        FixedCotypeBound (X →L[ℝ] ℝ) m Dg → FixedCotypeBound Y m Df →
        FiniteDimensional ℝ (LinearMap.range T.toLinearMap) →
        (∀ n, n₀ ≤ n → walshNorm n T ≤ (1/2)*walshNorm (n-2*m) T) ∧
        ∀ N, walshNorm N T ≤ uniformDecayRate m n₀ N * ‖T‖ := by
  have hm : 0 < m := by omega
  obtain ⟨c,hc,hc1,hgrowth⟩ := exists_growth_constant.{u,v} m Dg Df hDg1 hDf1 hcut hcutm hsize
  let q := Real.sqrt ((2 : ℝ)⁻¹)
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    exact (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  obtain ⟨n₀,hn₀,hdrop⟩ := uniform_drop_of_growth m hm c q hc hq0 hq1
  refine ⟨n₀,hn₀,uniformDecayRate_tendsto m n₀ hm,?_⟩
  intro X Y _ _ _ _ _ T hDg hDf hfin
  have hd : ∀ n, n₀ ≤ n → walshNorm n T ≤ (1/2)*walshNorm (n-2*m) T := by
    by_cases hT : T = 0
    · subst T; intro n hn
      have h := walshNorm_le n (0 : X →L[ℝ] Y)
      have h0 := walshNorm_nonneg (n-2*m) (0 : X →L[ℝ] Y)
      simp only [norm_zero] at h
      linarith
    obtain ⟨D,hD,hDn⟩ := finiteRank_walshNorm_decay T hfin
    have hbound : ∃ D : ℝ, ∀ n, walshNorm n T ≤ D*q^n := by
      refine ⟨D,?_⟩
      intro n
      have hs : ∀ l : ℕ, Real.sqrt ((2 : ℝ)⁻¹ ^ l) = q^l := by
        intro l
        induction l with
        | zero => simp
        | succ l ih =>
          rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]
      simpa only [hs] using hDn n
    intro n hn
    have h := hdrop (fun n => walshNorm n T) (fun n => walshNorm_pos n hT)
      (walshNorm_antitone T) hbound (hgrowth X Y T hDg hDf hT) n hn
    linarith
  refine ⟨hd,?_⟩
  intro N
  have h := sequence_drop_rate (fun n => walshNorm n T) m n₀ hm (walshNorm_antitone T) hd N
  simpa [uniformDecayRate, walshNorm_zero] using h

end Cotype

end

end OAI
