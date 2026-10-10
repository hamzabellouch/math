import Mathlib
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodLocal

namespace OAI

namespace ConvexSkorokhod

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma variation_partition_bound (B : Body E) (x₀ c : E) (r R : ℝ)
    (hx₀ : x₀∈B.carrier) (hr : 0 < r) (hball : Metric.closedBall c r⊆B.carrier)
    (hR : ∀x∈B.carrier,‖x-c‖ ≤ R) (w : ℕ → E) (q : ℕ → ℕ)
    (hq : Monotone q) (hq₀ : q 0=0) (M : ℕ)
    (hosc : ∀j < M,∀i ≤ q (j+1)-q j,‖w (q j+i)-w (q j)‖ ≤ r/2) :
    variation (regulator B x₀ w) (q M) ≤ (M:ℝ)*(R^2/r) := by
  have step (j : ℕ) (hj : j < M) :
      variation (regulator B x₀ w) (q (j+1)) ≤
        variation (regulator B x₀ w) (q j)+R^2/r := by
    have hle := hq (Nat.le_succ j)
    have hpart := regulator_variation_bound B (walk B x₀ w (q j)) c r R
      (walk_mem B x₀ hx₀ w _) hr (hR _ (walk_mem B x₀ hx₀ w _)) hball
      (fun i => w (q j+i)) (q (j+1)-q j) (by simpa only [Nat.add_zero] using hosc j hj)
    have he : regulator B (walk B x₀ w (q j)) (fun i => w (q j+i)) =
        fun i => regulator B x₀ w (q j+i)-regulator B x₀ w (q j) := by
      funext i;exact regulator_shift B x₀ w (q j) i
    rw [he,variation_sub_const] at hpart
    calc
      _=variation (regulator B x₀ w) (q j)+
        variation (fun i => regulator B x₀ w (q j+i)) (q (j+1)-q j) := by
          conv_lhs => rw [←Nat.add_sub_of_le hle]
          exact variation_add _ _ _
      _ ≤ _ := add_le_add le_rfl hpart
  have hsum : ∀j ≤ M,variation (regulator B x₀ w) (q j) ≤ (j:ℝ)*(R^2/r) := by
    intro j
    induction j with
    | zero => intro _;simp [hq₀,variation]
    | succ j ih =>
      intro hj
      have hb := (step j (by omega)).trans (add_le_add (ih (by omega)) le_rfl)
      simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul] using hb
  exact hsum M le_rfl

lemma mesh_global_variation (B : Body E) (x₀ c : E) (r R : ℝ)
    (hx₀ : x₀∈B.carrier) (hr : 0 < r) (hball : Metric.closedBall c r⊆B.carrier)
    (hR : ∀x∈B.carrier,‖x-c‖ ≤ R) (w : ℝ → E) (hw : ContinuousOn w (Icc 0 1)) :
    ∃M : ℕ,0 < M ∧ ∀N : ℕ,M ≤ N →
      variation (regulator B x₀ (sampledDriver w N)) N ≤ (M:ℝ)*(R^2/r) := by
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hw
  obtain ⟨η,hη,hηw⟩ := Metric.uniformContinuousOn_iff.mp huc (r/2) (half_pos hr)
  obtain ⟨M,hM⟩ := exists_nat_gt ((2:ℝ)/η)
  have hMpos : 0 < M := by exact_mod_cast lt_trans (by positivity : (0:ℝ) < 2/η) hM
  have hM' : (0:ℝ) < M := by exact_mod_cast hMpos
  have hsmall : (2:ℝ)/M < η := by
    apply (div_lt_iff₀ hM').mpr
    have hh := (div_lt_iff₀ hη).mp hM
    simpa only [mul_comm] using hh
  refine ⟨M,hMpos,fun N hMN => ?_⟩
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
  have hb := variation_partition_bound B x₀ c r R hx₀ hr hball hR (sampledDriver w N) q hq hq₀ M
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
      simpa only [sampledDriver,dist_eq_norm] using hh.le)
  simpa only [hqM] using hb

end ConvexSkorokhod

end OAI
