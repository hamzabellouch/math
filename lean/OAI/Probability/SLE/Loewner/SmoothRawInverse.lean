import OAI.Probability.SLE.Loewner.ReverseTrajectoryExistence
import OAI.Probability.SLE.Loewner.SmoothReverseContraction
import OAI.Probability.SLE.Loewner.TargetInverseContinuity

namespace OAI

/-! A boundary Cauchy estimate for the exact raw inverse map, without
assuming the existence of a capacity trace. -/
noncomputable section
open Set Filter Complex
open scoped Topology NNReal

namespace SLEExactGauge.Target

lemma exists_raw_reverse_trajectory (b : Driver) (T : ℝ≥0) (w : ℂ)
    (hw : w ∈ upperHalfPlane) :
    ∃ q : ℝ → ℂ, q 0=w ∧
      (∀ t, 0 ≤ t → w.im ≤ (q t).im) ∧
      (∀ t, 0 ≤ t → HasDerivWithinAt q
        (-2/(q t-(driverValue b ((T : ℝ)-t) : ℂ))) (Ici 0) t) ∧
      inverseFlow 1 b T w=q T := by
  have hu : Continuous (fun t : ℝ => driverValue b ((T : ℝ)-t)) :=
    b.continuous.comp (continuous_real_toNNReal.comp (continuous_const.sub continuous_id))
  obtain ⟨q,hq0,hheight,hqd⟩ := exists_reverse_trajectory _ hu w hw
  refine ⟨q,hq0,hheight,hqd,?_⟩
  have hh := inverseFlow_eq_reverse_trajectory 1 (by norm_num) b T w
    (w.im/2) (half_pos hw) (half_le_self hw.le) q hq0 (fun t ht => ?_)
  · simpa only [div_one] using hh
  · have he : reverseField (w.im/2) (driverValue b ((T : ℝ)-1*t)) (q t) =
        -2/(q t-(driverValue b ((T : ℝ)-t) : ℂ)) := by
      rw [one_mul,reverseField,reverseCenter_eq ((half_le_self hw.le).trans (hheight t ht))]
      rfl
    rw [he]
    exact hqd t ht

theorem inverseFlow_vertical_contraction (b : Driver) (T : ℝ≥0) (b' : ℝ → ℝ)
    (hd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt (fun s => b s.toNNReal)
      (b' t) (Icc 0 (T : ℝ)) t)
    {L : ℝ} (hL : 0 ≤ L) (hb : ∀ t ∈ Icc 0 (T : ℝ), |b' t| ≤ L)
    (hsmall : L^2*(T : ℝ) ≤ 1) {y v : ℝ} (hy : 0 < y) (hv : 0 < v) :
    dist (inverseFlow 1 b T ((b T : ℂ)+(y : ℂ)*I))
      (inverseFlow 1 b T ((b T : ℂ)+(v : ℂ)*I)) ≤ |y-v| := by
  obtain ⟨q,hq0,hqy,hqd,heq⟩ := exists_raw_reverse_trajectory b T
    ((b T : ℂ)+(y : ℂ)*I) (by simpa [upperHalfPlane] using hy)
  obtain ⟨r,hr0,hry,hrd,her⟩ := exists_raw_reverse_trajectory b T
    ((b T : ℂ)+(v : ℂ)*I) (by simpa [upperHalfPlane] using hv)
  let u (s : ℝ) := driverValue b ((T : ℝ)-s)
  have hreflect (s : ℝ) (hs : s ∈ Icc 0 (T : ℝ)) :
      (T : ℝ)-s ∈ Icc 0 (T : ℝ) :=
    ⟨sub_nonneg.mpr hs.2,sub_le_self _ hs.1⟩
  have hu (s : ℝ) (hs : s ∈ Icc 0 (T : ℝ)) : HasDerivWithinAt u
      (-b' ((T : ℝ)-s)) (Icc 0 (T : ℝ)) s := by
    have hi : HasDerivWithinAt (fun t : ℝ => (T : ℝ)-t) (-1) (Icc 0 (T : ℝ)) s := by
      simpa using ((hasDerivAt_id s).const_sub (T : ℝ)).hasDerivWithinAt
    convert! (hd _ (hreflect s hs)).comp s hi hreflect using 1
    simp only [mul_neg,mul_one]
  have hh := smooth_reverse_trajectories_contract T.coe_nonneg hL q r u
    (fun s => -b' ((T : ℝ)-s))
    (fun s hs => (hqd s hs.1).mono Icc_subset_Ici_self)
    (fun s hs => (hrd s hs.1).mono Icc_subset_Ici_self) hu
    (fun s hs => by simpa using hb _ (hreflect s hs))
    (fun s hs => hy.trans_le (by simpa using hqy s hs.1))
    (fun s hs => hv.trans_le (by simpa using hry s hs.1))
    (by simp [hq0,u,driverValue]) (by simp [hr0,u,driverValue]) hsmall
  rw [heq,her]
  convert hh using 1
  rw [hq0,hr0,dist_eq_norm]
  have he : ((b T : ℂ)+(y : ℂ)*I)-((b T : ℂ)+(v : ℂ)*I)=((y-v : ℝ) : ℂ)*I := by
    push_cast
    ring
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]

end SLEExactGauge.Target

end

end OAI
