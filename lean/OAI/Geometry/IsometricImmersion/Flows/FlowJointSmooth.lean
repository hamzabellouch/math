import OAI.Geometry.IsometricImmersion.Flows.FlowVariation
import OAI.Geometry.IsometricImmersion.Calculus.FinitePrimitive

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def flowCoordinateMap (Y : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : Coord :=
  coordinatePoint p.1 (Y p.2 p.1)

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}

theorem cap_flow_joint_contDiffOn
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2) := by
  let D := pairRectangle 2 (-2) 2
  let F (p : ℝ × ℝ) := Y p.2 p.1
  let B (p : ℝ × ℝ) := coordPartial 1 q (flowCoordinateMap Y p)
  have hmem : MapsTo (flowCoordinateMap Y) D U := by
    intro p hp
    exact hSU (coordinatePoint_mem_modelSquare
      ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
      (hrange p.2 ⟨hp.2.1.le, hp.2.2.le⟩ p.1 ⟨hp.1.1.le, hp.1.2.le⟩))
  have hdx (p : ℝ × ℝ) (hp : p ∈ D) :
      HasDerivAt (fun x => F (x, p.2)) (-q (flowCoordinateMap Y p)) p.1 := by
    exact (hode p.2 ⟨hp.2.1.le, hp.2.2.le⟩ p.1 ⟨hp.1.1.le, hp.1.2.le⟩).hasDerivAt
      (Icc_mem_nhds hp.1.1 hp.1.2)
  have hdy (p : ℝ × ℝ) (hp : p ∈ D) :
      HasDerivAt (fun y => F (p.1, y)) (Real.exp (-pairPrimitive B p)) p.2 := by
    exact cap_flow_hasDerivAt_initial hq hU hSU hY hrange hstart hode hp.2 hp.1
  have hnat : ∀ n : ℕ, ContDiffOn ℝ n F D := by
    intro n
    induction n with
    | zero =>
        have hc : ContinuousOn F D := hY.comp continuous_swap.continuousOn
          (fun p hp => ⟨⟨hp.2.1.le, hp.2.2.le⟩, ⟨hp.1.1.le, hp.1.2.le⟩⟩)
        simpa only [Nat.cast_zero, contDiffOn_zero] using hc
    | succ n hn =>
        have horder : (n : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
        have hmap : ContDiffOn ℝ n (flowCoordinateMap Y) D := by
          exact (contDiffOn_fst.smul contDiffOn_const).add (hn.smul contDiffOn_const)
        have hfx : ContDiffOn ℝ n (fun p => -q (flowCoordinateMap Y p)) D :=
          ((hq.of_le horder).comp hmap hmem).neg
        have hB : ContDiffOn ℝ n B D :=
          ((partial_contDiffOn hq hU 1).of_le horder).comp hmap hmem
        have hfy : ContDiffOn ℝ n (fun p => Real.exp (-pairPrimitive B p)) D :=
          ((pairPrimitive_contDiffOn_nat n hB).neg).exp
        exact contDiffOn_succ_of_continuous_partials (pairRectangle_isOpen 2 (-2) 2) n
          hfx hfy hdx hdy
  exact contDiffOn_infty.mpr hnat

theorem exists_smooth_cap_flow
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hsmall : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100) :
    ∃ Y : ℝ → ℝ → ℝ,
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
        HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
        |Y s t - s| ≤ (1 : ℝ) / 50) ∧
      (∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
        HasDerivAt (fun u => Y u t)
          (Real.exp (-(∫ r in 0..t, coordPartial 1 q (coordinatePoint r (Y s r))))) s ∧
        0 < deriv (fun u => Y u t) s) := by
  obtain ⟨Y, hY, htime, hstart, hode, hdisp, hdisp', hrange, hLip⟩ :=
    exists_cap_flow hq hU hSU hsmall
  have hrange' (s : ℝ) (hs : s ∈ Icc (-2 : ℝ) 2) (t : ℝ)
      (ht : t ∈ Icc (-2 : ℝ) 2) : Y s t ∈ Icc (-3 : ℝ) 3 :=
    abs_le.mp ((hrange s hs t ht).1.trans (by norm_num))
  refine ⟨Y, cap_flow_joint_contDiffOn hq hU hSU hY hrange' hstart hode,
    hstart, hode, hdisp', ?_⟩
  intro s hs t ht
  exact ⟨cap_flow_hasDerivAt_initial hq hU hSU hY hrange' hstart hode hs ht,
    cap_flow_initial_deriv_pos hq hU hSU hY hrange' hstart hode hs ht⟩

end SmoothLocal.Flow

end

end OAI
