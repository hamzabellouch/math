import Mathlib
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodGlobal

namespace OAI

namespace ConvexSkorokhod

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma mesh_nearby_variation (B : Body E) (x₀ c : E) (r R : ℝ)
    (hx₀ : x₀∈B.carrier) (hr : 0 < r) (hball : Metric.closedBall c r⊆B.carrier)
    (hR : ∀x∈B.carrier,‖x-c‖ ≤ R) (w : ℝ → E) (hw : ContinuousOn w (Icc 0 1)) :
    ∃M : ℕ,0 < M ∧ ∀v : ℝ → E,
      (∀t∈Icc (0:ℝ) 1,‖v t-w t‖ ≤ r/8) → ∀N : ℕ,M ≤ N →
      variation (regulator B x₀ (sampledDriver v N)) N ≤ (M:ℝ)*(R^2/r) := by
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hw
  obtain ⟨η,hη,hηw⟩ := Metric.uniformContinuousOn_iff.mp huc (r/4) (by positivity)
  obtain ⟨M,hM⟩ := exists_nat_gt ((2:ℝ)/η)
  have hMpos : 0 < M := by exact_mod_cast lt_trans (by positivity : (0:ℝ) < 2/η) hM
  have hM' : (0:ℝ) < M := by exact_mod_cast hMpos
  have hsmall : (2:ℝ)/M < η := by
    apply (div_lt_iff₀ hM').mpr
    have hh := (div_lt_iff₀ hη).mp hM
    simpa only [mul_comm] using hh
  refine ⟨M,hMpos,fun v hv N hMN => ?_⟩
  have hNpos : 0 < N := hMpos.trans_le hMN
  have hN' : (0:ℝ) < N := by exact_mod_cast hNpos
  let L := N/M+1
  let q : ℕ → ℕ := fun j => min (j*L) N
  have hq : Monotone q := fun i j hij => min_le_min_right N (Nat.mul_le_mul_right L hij)
  have hq₀ : q 0=0 := by simp [q]
  have hqM : q M=N := by
    apply min_eq_right
    exact (Nat.div_lt_iff_lt_mul hMpos).mp (Nat.lt_succ_self (N/M)) |>.le.trans_eq (Nat.mul_comm _ _)
  have hL : (L:ℝ)/N ≤ 2/M := by
    have hdiv : (N/M)*M ≤ N := Nat.div_mul_le_self N M
    have hdiv' : ((N/M:ℕ):ℝ)*M ≤ N := by exact_mod_cast hdiv
    have hMN' : (M:ℝ) ≤ N := by exact_mod_cast hMN
    apply (div_le_div_iff₀ hN' hM').mpr
    dsimp [L]
    push_cast
    nlinarith
  have htime (i : ℕ) (hi : i ≤ N) : (i:ℝ)/N∈Icc (0:ℝ) 1 := by
    refine ⟨by positivity,?_⟩
    rw [div_le_one hN'];exact_mod_cast hi
  have hb := variation_partition_bound B x₀ c r R hx₀ hr hball hR (sampledDriver v N) q hq hq₀ M
    (by
      intro j hj i hi
      have hnext : q (j+1) ≤ N := min_le_right _ _
      have hcur : q j ≤ N := min_le_right _ _
      have hle := hq (Nat.le_succ j)
      have hai : q j+i ≤ N := by omega
      have hwidth : q (j+1)-q j ≤ L := by
        change min ((j+1)*L) N - min (j*L) N ≤ L
        rw [Nat.add_mul,Nat.one_mul]
        by_cases h : j*L ≤ N
        · rw [min_eq_left h]
          apply Nat.sub_le_iff_le_add.mpr
          exact (min_le_left (j*L+L) N).trans_eq (Nat.add_comm _ _)
        · rw [min_eq_right (le_of_not_ge h),Nat.sub_eq_zero_of_le (min_le_right _ _)]
          exact Nat.zero_le _
      have hiL : i ≤ L := hi.trans hwidth
      have hdiff : ((q j+i:ℕ):ℝ)/N-(q j:ℝ)/N=(i:ℝ)/N := by push_cast;ring
      have hdist : dist (((q j+i:ℕ):ℝ)/N) ((q j:ℝ)/N) < η := by
        rw [Real.dist_eq,hdiff,abs_of_nonneg (by positivity)]
        exact ((div_le_div_of_nonneg_right (by exact_mod_cast hiL) hN'.le).trans hL).trans_lt hsmall
      have hh := hηw _ (htime _ hai) _ (htime _ hcur) hdist
      have ha := hv _ (htime _ hai)
      have hb := hv _ (htime _ hcur)
      have htri : ‖v (((q j+i:ℕ):ℝ)/N)-v ((q j:ℝ)/N)‖ ≤
          ‖v (((q j+i:ℕ):ℝ)/N)-w (((q j+i:ℕ):ℝ)/N)‖+
          ‖w (((q j+i:ℕ):ℝ)/N)-w ((q j:ℝ)/N)‖+
          ‖v ((q j:ℝ)/N)-w ((q j:ℝ)/N)‖ := by
        calc
          _ ≤ ‖v (((q j+i:ℕ):ℝ)/N)-w (((q j+i:ℕ):ℝ)/N)‖+
            ‖w (((q j+i:ℕ):ℝ)/N)-v ((q j:ℝ)/N)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ _ := by
            have hz := norm_sub_le_norm_sub_add_norm_sub (w (((q j+i:ℕ):ℝ)/N))
              (w ((q j:ℝ)/N)) (v ((q j:ℝ)/N))
            rw [norm_sub_rev (w ((q j:ℝ)/N)) (v ((q j:ℝ)/N))] at hz
            linarith
      rw [dist_eq_norm] at hh
      change ‖v (((q j+i:ℕ):ℝ)/N)-v ((q j:ℝ)/N)‖ ≤ r/2
      linarith)
  simpa only [hqM] using hb

end ConvexSkorokhod

end OAI
