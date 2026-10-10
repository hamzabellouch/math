import OAI.Geometry.IsometricImmersion.Flows.PicardFamily

namespace OAI

noncomputable section
open Set Metric Filter Function
open scoped ContDiff Topology NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem exists_cap_flow {q : Coord → ℝ} {U : Set Coord}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hsmall : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100) :
    ∃ Y : ℝ → ℝ → ℝ,
      ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ContDiffOn ℝ ∞ (Y s) (Icc (-2 : ℝ) 2)) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
        HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
        |Y s t - s| ≤ (1 : ℝ) / 100 * |t|) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, |Y s t - s| ≤ (1 : ℝ) / 50) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
        |Y s t| ≤ (101 : ℝ) / 50 ∧ coordinatePoint t (Y s t) ∈ modelSquare) ∧
      (∃ J : ℝ≥0, ∀ t, LipschitzOnWith J (fun s => Y s t) (Icc (-2 : ℝ) 2)) := by
  obtain ⟨L, hPL⟩ := exists_cap_picard hq hU hSU hsmall
  obtain ⟨Y, hY, hconf, ⟨J, hJ⟩, hcont, htime⟩ :=
    exists_confined_continuous_picard_family hPL
  have hball (s : ℝ) (hs : s ∈ Icc (-2 : ℝ) 2) :
      s ∈ closedBall (0 : ℝ) (↑(2 : ℝ≥0)) := by
    simpa only [mem_closedBall, Real.dist_eq, sub_zero, NNReal.coe_ofNat] using abs_le.mpr hs
  have hz : (0 : ℝ) ∈ Icc (-2 : ℝ) 2 := by norm_num
  have hstart (s : ℝ) (hs : s ∈ Icc (-2 : ℝ) 2) : Y s 0 = s :=
    (hY s (hball s hs)).1
  have hderiv (s : ℝ) (hs : s ∈ Icc (-2 : ℝ) 2) (t : ℝ)
      (ht : t ∈ Icc (-2 : ℝ) 2) :
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t :=
    (hY s (hball s hs)).2 t ht
  have hdispl (s : ℝ) (hs : s ∈ Icc (-2 : ℝ) 2) (t : ℝ)
      (ht : t ∈ Icc (-2 : ℝ) 2) : |Y s t - s| ≤ (1 : ℝ) / 100 * |t| := by
    have hh := (htime s (hball s hs)).dist_le_mul t ht 0 hz
    rw [hstart s hs] at hh
    simpa only [Real.dist_eq, sub_zero, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hh
  have hdispl' (s : ℝ) (hs : s ∈ Icc (-2 : ℝ) 2) (t : ℝ)
      (ht : t ∈ Icc (-2 : ℝ) 2) : |Y s t - s| ≤ (1 : ℝ) / 50 := by
    have hd := hdispl s hs t ht
    have habs := abs_le.mpr ht
    nlinarith
  have hfield : ContDiffOn ℝ ∞ (uncurry (flowField q))
      (Icc (-2 : ℝ) 2 ×ˢ closedBall (0 : ℝ) 3) := by
    apply hq.neg.comp (by unfold coordinatePoint; fun_prop)
    intro p hp
    have hy : |p.2| ≤ 3 := by
      simpa only [mem_closedBall, Real.dist_eq, sub_zero] using hp.2
    exact hSU (coordinatePoint_mem_modelSquare
      ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩ (abs_le.mp hy))
  refine ⟨Y, hcont.mono (fun p hp => ⟨hball p.1 hp.1, hp.2⟩), ?_, hstart,
    hderiv, hdispl, hdispl', ?_, ⟨J, fun t => (hJ t).mono (fun s hs => hball s hs)⟩⟩
  · intro s hs
    exact ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt hfield (hderiv s hs)
      (fun t _ => hconf s (hball s hs) t)
  · intro s hs t ht
    have hys : |Y s t| ≤ (101 : ℝ) / 50 := by
      have hsum : |Y s t| ≤ |Y s t - s| + |s| := by
        simpa only [sub_add_cancel] using abs_add_le (Y s t - s) s
      have hd := hdispl' s hs t ht
      have hs2 := abs_le.mpr hs
      linarith
    refine ⟨hys, coordinatePoint_mem_modelSquare
      ⟨by linarith [ht.1], by linarith [ht.2]⟩ ?_⟩
    exact abs_le.mp (hys.trans (by norm_num))

end SmoothLocal.Flow

end

end OAI
