import OAI.Probability.SLE.Loewner.RawReverseComposition
import OAI.Probability.SLE.Loewner.RawSurvivingMonotone
import OAI.Probability.SLE.Loewner.SmoothRawReverseEstimates
import OAI.Probability.SLE.Loewner.SmoothRawTrace
import OAI.Probability.SLE.Loewner.ReverseHeightUpper

namespace OAI

/-! The smooth raw tip survives at every earlier time. The proof uses
compactness of an intermediate reverse image, with a uniform positive
height, and the raw inverse composition identity. -/
noncomputable section
open Set Filter Metric Complex
open scoped Topology NNReal

namespace SLEExactGauge.Target

theorem smooth_raw_tip_survives_short_past
    (b : Driver) (T a : ℝ≥0) (ha : a ≤ T) (ha0 : 0 < a) (b' : ℝ → ℝ)
    (hd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt (driverValue b)
      (b' t) (Icc 0 (T : ℝ)) t)
    {L : ℝ} (hL : 0 ≤ L) (hb : ∀ t ∈ Icc 0 (T : ℝ), |b' t| ≤ L)
    (hsmall : L^2*(a : ℝ) ≤ 1) : Surviving 1 b (trace 1 b T) (T-a : ℝ≥0) := by
  let y (n : ℕ) : ℝ := 1/((n : ℝ)+1)
  let w (n : ℕ) : ℂ := (b T : ℂ)+(y n : ℂ)*I
  have hy (n : ℕ) : 0 < y n := by dsimp [y]; positivity
  have hy1 (n : ℕ) : y n ≤ 1 := by
    dsimp [y]
    apply (div_le_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hw (n : ℕ) : w n ∈ upperHalfPlane := by simpa [w,upperHalfPlane] using hy n
  choose q hq0 hheight hqd heq using (fun n => exists_raw_reverse_trajectory b T (w n) (hw n))
  let v (n : ℕ) : ℂ := q n a
  let z (n : ℕ) : ℂ := q n T
  have hqp (n : ℕ) (t : ℝ) (ht : 0 ≤ t) : 0 < (q n t).im :=
    (hw n).trans_le (hheight n t ht)
  have hqb (n : ℕ) : |(v n).re-b (T-a)| ≤ L*a ∧ 2*(a : ℝ) ≤ (v n).im^2 := by
    have hh := smooth_raw_reverse_estimates b T b' hd hL hb (q n)
      (fun t ht => (hqd n t ht.1).mono Icc_subset_Ici_self)
      (fun t ht => hqp n t ht.1) (by simp [hq0,w]) a ⟨a.coe_nonneg,ha⟩ hsmall
    simpa only [v,driverValue,show ((T : ℝ)-(a : ℝ)).toNNReal=T-a from rfl] using hh
  have hvi (n : ℕ) : (v n).im ≤ 1+4*(a : ℝ) := by
    have hh := reverse_height_square_le a.coe_nonneg (q n)
      (fun t => driverValue b ((T : ℝ)-t))
      (fun t ht => (hqd n t ht.1).mono Icc_subset_Ici_self)
      (fun t ht => hqp n t ht.1)
    rw [hq0 n] at hh
    have hwi : (w n).im=y n := by simp [w]
    rw [hwi] at hh
    change (v n).im^2 ≤ (y n)^2+4*(a : ℝ) at hh
    nlinarith [hy n,hy1 n,hqp n a a.coe_nonneg,a.coe_nonneg,sq_nonneg (4*(a : ℝ))]
  let R : ℝ := L*a+|b (T-a)|+(1+4*(a : ℝ))
  have hball (n : ℕ) : v n ∈ closedBall 0 R := by
    rw [mem_closedBall,dist_zero_right]
    have hre : |(v n).re| ≤ L*a+|b (T-a)| := by
      calc
        |(v n).re| = |((v n).re-b (T-a))+b (T-a)| := by congr 1; ring
        _ ≤ |(v n).re-b (T-a)|+|b (T-a)| := abs_add_le _ _
        _ ≤ L*a+|b (T-a)| := add_le_add (hqb n).1 le_rfl
    have hvp : 0 < (v n).im := hqp n a a.coe_nonneg
    exact (Complex.norm_le_abs_re_add_abs_im (v n)).trans
      (add_le_add hre (by simpa only [abs_of_pos hvp] using hvi n))
  obtain ⟨v₀,_,φ,hφ,hlim⟩ := (isCompact_closedBall (0 : ℂ) R).tendsto_subseq hball
  have him := Complex.continuous_im.continuousAt.tendsto.comp hlim
  have hnonneg : 0 ≤ v₀.im := ge_of_tendsto him
    (Eventually.of_forall (fun n => (hqp (φ n) a a.coe_nonneg).le))
  have hlow : 2*(a : ℝ) ≤ v₀.im^2 := ge_of_tendsto (him.pow 2)
    (Eventually.of_forall (fun n => (hqb (φ n)).2))
  have hv₀ : v₀ ∈ upperHalfPlane := by
    have hap : 0 < (a : ℝ) := ha0
    change 0 < v₀.im
    nlinarith
  have hFv (n : ℕ) : inverseFlow 1 b (T-a : ℝ≥0) (v n)=z n := by
    have hh := raw_reverse_tail_inverse b T (T-a) tsub_le_self (q n) (hqd n) (hqp n)
    have hdiff : (T : ℝ)-((T-a : ℝ≥0) : ℝ)=(a : ℝ) := by rw [NNReal.coe_sub ha]; ring
    simpa only [hdiff,v,z] using hh
  have hFc : ContinuousAt (inverseFlow 1 b (T-a : ℝ≥0)) v₀ :=
    (continuousOn_inverseFlow 1 (by norm_num) b (T-a)).continuousAt
      (isOpen_upperHalfPlane.mem_nhds hv₀)
  have hFz : Tendsto (fun n => z (φ n)) atTop (𝓝 (inverseFlow 1 b (T-a : ℝ≥0) v₀)) := by
    have hh := hFc.tendsto.comp hlim
    convert hh using 1
    funext n
    exact (hFv (φ n)).symm
  have hy0 : Tendsto y atTop (𝓝[>] (0 : ℝ)) := tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_one_div_add_atTop_nhds_zero_nat,Eventually.of_forall hy⟩
  have hzlim : Tendsto z atTop (𝓝 (trace 1 b T)) := by
    have hh := (tendsto_inverseFlow_smooth_trace b T b' hd hL hb).comp hy0
    convert hh using 1
    funext n
    exact (heq n).symm
  have hfinal := tendsto_nhds_unique hFz (hzlim.comp hφ.tendsto_atTop)
  exact hfinal ▸ inverseFlow_surviving 1 (by norm_num) b (T-a) v₀ hv₀

end SLEExactGauge.Target

end

end OAI
