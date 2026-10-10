import OAI.Probability.SLE.Geometry.DiagonalComplexLimit
import OAI.Probability.SLE.Loewner.InitialDrivingRightContinuity
import OAI.Probability.SLE.Loewner.InitialForwardTimeContinuity

namespace OAI

/-! Every left-hand cluster of the driver is the exact tip value. -/
noncomputable section
open Set Filter Function Complex Metric
open scoped Topology

namespace SLEExactGauge

theorem initialDriving_left_cluster (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {R : ℝ} (hR : 0<R) (hp : ∀ t : unitInterval, ‖p t‖<R)
    {s : unitInterval} (hs0 : s≠0) (hs : s<1)
    {t : ℕ → unitInterval} (hts : ∀ n, t n<s) (ht : Tendsto t atTop (𝓝 s))
    {a : ℝ} (ha : Tendsto (fun n => initialDriving p hi h0 hH (t n)) atTop (𝓝 a)) :
    a=initialDriving p hi h0 hH s := by
  let D : ℝ := (1-(s:ℝ))/2
  have hD : 0<D := half_pos (sub_pos.mpr hs)
  let d := fun n : ℕ => D*(1/((n:ℝ)+1))
  have hd (n : ℕ) : d n∈Ioo 0 (1-(s:ℝ)) := by
    have hn : (0:ℝ)<(n:ℝ)+1 := by positivity
    have hb : 1/((n:ℝ)+1)≤1 := (div_le_one hn).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    refine ⟨mul_pos hD (one_div_pos.mpr hn),?_⟩
    have hle := mul_le_mul_of_nonneg_left hb hD.le
    dsimp only [D] at hD hle
    dsimp only [d,D]
    linarith
  let q := fun n => slitFutureParameter s (d n)
  have hsq (n : ℕ) : s<q n := by
    change (s:ℝ)<(slitFutureParameter s (d n):ℝ)
    rw [slitFutureParameter_coe s (hd n)]
    linarith [(hd n).1]
  have hq1 (n : ℕ) : q n<1 := by
    change (slitFutureParameter s (d n):ℝ)<1
    rw [slitFutureParameter_coe s (hd n)]
    linarith [(hd n).2]
  have hdlim : Tendsto d atTop (𝓝 0) := by
    simpa only [mul_zero,d] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul D
  have hqlim : Tendsto q atTop (𝓝 s) := by
    simpa only [slitFutureParameter_zero,Function.comp_def,q] using
      ((slitFutureParameter_continuous s).tendsto 0).comp hdlim
  have hg : Tendsto (fun n => initialForwardChart p hi h0 hH s (p (q n)))
      atTop (𝓝 (initialDrivingValue p hi h0 hH s hs:ℂ)) :=
    (initialDrivingValue_spec p hi h0 hH s hs).comp
      (tendsto_nhdsWithin_iff.mpr ⟨hdlim,Eventually.of_forall fun n => (hd n).1⟩)
  have hf (k : ℕ) : Tendsto (fun n => initialForwardChart p hi h0 hH (t n) (p (q k)))
      atTop (𝓝 (initialForwardChart p hi h0 hH s (p (q k)))) :=
    initialForwardChart_tendsto p hi h0 hH ht tendsto_const_nhds
      (point_after_prefix_mem_domain p hi hH (hsq k))
      (fun n => point_after_prefix_mem_domain p hi hH ((hts n).trans (hsq k)))
  obtain ⟨φ,hφ,hφlim⟩ := diagonal_complex_limit hf hg
  have hφtop : Tendsto φ atTop atTop := tendsto_atTop_mono hφ tendsto_id
  have ha' : Tendsto (fun n => initialDrivingValue p hi h0 hH (t (φ n))
      (((hts (φ n)).trans (hsq n)).trans (hq1 n))) atTop (𝓝 a) := by
    convert ha.comp hφtop using 1
    funext n
    exact (initialDriving_of_lt p hi h0 hH ((hts (φ n)).trans hs)).symm
  have he := initialDriving_shrinking_endpoint_unique p hi h0 hH hR hp hs0
    (ht.comp hφtop) hqlim (fun n => (hts (φ n)).trans (hsq n)) hq1 ha' hφlim
  exact he.trans (initialDriving_of_lt p hi h0 hH hs).symm

end SLEExactGauge

end

end OAI
