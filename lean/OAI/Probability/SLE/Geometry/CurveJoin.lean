import OAI.Probability.SLE.Gauge.NormalRibbonPatch

namespace OAI

/-! Joining the straight and circular pieces of the serpentine at matching
positions and tangents. The joins preserve the actual derivative and the
common tangent Lipschitz constant. -/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge.Serpentine

def curveJoin (c : ℝ) (f g : ℝ → ℂ) (t : ℝ) : ℂ := if t ≤ c then f t else g t

@[simp] lemma curveJoin_of_le {c t : ℝ} (h : t ≤ c) (f g : ℝ → ℂ) :
    curveJoin c f g t = f t := by simp only [curveJoin, ite_eq_left h]

@[simp] lemma curveJoin_of_gt {c t : ℝ} (h : c < t) (f g : ℝ → ℂ) :
    curveJoin c f g t = g t := by simp only [curveJoin, ite_eq_right (not_le_of_gt h)]

theorem curveJoin_continuous (c : ℝ) (f g : ℝ → ℂ) (hf : Continuous f)
    (hg : Continuous g) (he : f c = g c) : Continuous (curveJoin c f g) := by
  classical
  change Continuous ((Iic c).piecewise f g)
  apply Continuous.piecewise ?_ hf hg
  intro t ht
  have ht' : t = c := by simpa only [frontier_Iic, mem_singleton_iff] using ht
  simpa only [ht'] using he

lemma curveJoin_lipschitz {c : ℝ} {f g : ℝ → ℂ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith K g) (he : f c = g c) :
    LipschitzWith K (curveJoin c f g) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro u v
  by_cases hu : u ≤ c
  · by_cases hv : v ≤ c
    · simpa only [curveJoin_of_le hu, curveJoin_of_le hv] using hf.dist_le_mul u v
    · have hcv : c < v := lt_of_not_ge hv
      rw [curveJoin_of_le hu, curveJoin_of_gt hcv]
      calc
        dist (f u) (g v) ≤ dist (f u) (f c) + dist (g c) (g v) := by
          simpa only [he] using dist_triangle (f u) (f c) (g v)
        _ ≤ K * dist u c + K * dist c v := add_le_add (hf.dist_le_mul _ _) (hg.dist_le_mul _ _)
        _ = K * dist u v := by
          rw [Real.dist_eq, Real.dist_eq, Real.dist_eq,
            abs_of_nonpos (sub_nonpos.mpr hu), abs_of_neg (sub_neg.mpr hcv),
            abs_of_neg (sub_neg.mpr (hu.trans_lt hcv))]
          ring
  · have hcu : c < u := lt_of_not_ge hu
    by_cases hv : v ≤ c
    · rw [curveJoin_of_gt hcu, curveJoin_of_le hv]
      calc
        dist (g u) (f v) ≤ dist (g u) (g c) + dist (f c) (f v) := by
          simpa only [he] using dist_triangle (g u) (g c) (f v)
        _ ≤ K * dist u c + K * dist c v := add_le_add (hg.dist_le_mul _ _) (hf.dist_le_mul _ _)
        _ = K * dist u v := by
          rw [Real.dist_eq, Real.dist_eq, Real.dist_eq,
            abs_of_pos (sub_pos.mpr hcu), abs_of_nonneg (sub_nonneg.mpr hv),
            abs_of_pos (sub_pos.mpr (hv.trans_lt hcu))]
          ring
    · simpa only [curveJoin_of_gt hcu, curveJoin_of_gt (lt_of_not_ge hv)] using hg.dist_le_mul u v

theorem curveJoin_hasDerivAt (c : ℝ) (f g df dg : ℝ → ℂ)
    (hf : ∀ t, HasDerivAt f (df t) t) (hg : ∀ t, HasDerivAt g (dg t) t)
    (he : f c = g c) (hd : df c = dg c) (t : ℝ) :
    HasDerivAt (curveJoin c f g) (curveJoin c df dg t) t := by
  by_cases hlt : t < c
  · have heq : curveJoin c f g =ᶠ[𝓝 t] f := by
      filter_upwards [eventually_lt_nhds hlt] with u hu
      exact curveJoin_of_le hu.le f g
    rw [curveJoin_of_le hlt.le]
    exact (hf t).congr_of_eventuallyEq heq
  · by_cases hgt : c < t
    · have heq : curveJoin c f g =ᶠ[𝓝 t] g := by
        filter_upwards [eventually_gt_nhds hgt] with u hu
        exact curveJoin_of_gt hu f g
      rw [curveJoin_of_gt hgt]
      exact (hg t).congr_of_eventuallyEq heq
    · have ht : t = c := le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
      subst t
      have hl : HasDerivWithinAt (curveJoin c f g) (df c) (Iic c) c := by
        apply (hf c).hasDerivWithinAt.congr
        · intro u hu
          exact curveJoin_of_le hu f g
        · exact curveJoin_of_le le_rfl f g
      have hr : HasDerivWithinAt (curveJoin c f g) (df c) (Ici c) c := by
        rw [hd]
        apply (hg c).hasDerivWithinAt.congr
        · intro u hu
          by_cases heq : u = c
          · simpa only [heq, curveJoin_of_le le_rfl] using he
          · exact curveJoin_of_gt (lt_of_le_of_ne hu (Ne.symm heq)) f g
        · simpa only [curveJoin_of_le le_rfl] using he
      have hh := hl.union hr
      rw [Iic_union_Ici] at hh
      simpa only [curveJoin_of_le le_rfl] using hh.hasDerivAt (by simp)

end SLEExactGauge.Serpentine

end

end OAI
