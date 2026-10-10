import OAI.MeasureTheory.Falconer.Recursion.ParentConeSource
import OAI.MeasureTheory.Falconer.Recursion.ParentBinFamily
import OAI.MeasureTheory.Falconer.Graphs.GraphParentDiameter
import OAI.MeasureTheory.Falconer.Estimates.ParallelCandidateCount

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem radial_perpendicular_bound (x y : Plane) (u : UnitCircle) {D d : ℝ}
    (hD : dist x y ≤ D) (hd : dist (sourceRadialUnit y x) u ≤ d) :
    |inner ℝ (quarterTurn (u:Plane)) (x-y)| ≤ D*d := by
  have hdp : 0 ≤ d := dist_nonneg.trans hd
  have he : ‖x-y‖ • (sourceRadialUnit y x : Plane) = x-y := by
    by_cases h : x = y
    · simp [h]
    · simp only [sourceRadialUnit,sourceRadialVector,ite_eq_right h,smul_smul,
        mul_inv_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)),one_smul]
  have horth : inner ℝ (quarterTurn (sourceRadialUnit y x:Plane)) (x-y) = 0 := by
    calc
      _ = inner ℝ (quarterTurn (sourceRadialUnit y x:Plane))
          (‖x-y‖ • (sourceRadialUnit y x:Plane)) := congrArg _ he.symm
      _ = 0 := by
        rw [real_inner_smul_right]
        have hz : inner ℝ (quarterTurn (sourceRadialUnit y x:Plane)) (sourceRadialUnit y x:Plane) = 0 := by
          simp [quarterTurn,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two]
          ring
        rw [hz,mul_zero]
  have hn : ‖quarterTurn ((u:Plane)-(sourceRadialUnit y x:Plane))‖ ≤ d := by
    rw [graph_quarterTurn_norm,← dist_eq_norm,dist_comm]
    exact hd
  have hh := abs_real_inner_le_norm (quarterTurn ((u:Plane)-(sourceRadialUnit y x:Plane))) (x-y)
  rw [quarterTurn_sub,inner_sub_left,horth,sub_zero] at hh
  apply hh.trans
  rw [quarterTurn_sub] at hn
  exact (mul_le_mul hn (by simpa only [dist_eq_norm] using hD) (norm_nonneg _) hdp).trans_eq (mul_comm _ _)

theorem active_rotated_bin_direction_bound {θ : ℝ} (hθ : 0 < θ) (hcap : θ ≤ 2*Real.pi)
    (axis : ℝ) (j : ℕ) (e u : UnitCircle)
    (hu : sourceCircleRotate (-axis) u ∈ tsupport (circleAngularBin (angularBinCount θ) j))
    (ha : AngularBinActive (angularBinCount θ) j (sourceCircleRotate (-axis) e) (3*θ)) :
    dist e u ≤ 7*θ := by
  obtain ⟨w,hw,hew⟩ := ha
  have hh := circleAngularBin_scale_diameter hθ hcap j hw hu
  have ht := dist_triangle (sourceCircleRotate (-axis) e) w (sourceCircleRotate (-axis) u)
  rw [sourceCircleRotate_dist] at ht
  linarith

theorem parent_active_bin_strip (X Y P Q : DyadicSquare) {a θ : ℝ}
    (hX : 0 < X.side) (hY : 0 < Y.side) (hP : 0 < P.side) (hQ : 0 < Q.side)
    (hXa : X.side ≤ (2:ℝ)^(-a)) (hYa : Y.side ≤ (2:ℝ)^(-a))
    (hsep : dist X.center Y.center ≤ 2000*(2:ℝ)^(-a))
    (hPX : P.carrier ⊆ X.carrier) (hQY : Q.carrier ⊆ Y.carrier)
    (hθ : 0 < θ) (hcap : θ ≤ 2*Real.pi) (j : ℕ) (u : UnitCircle)
    (hu : sourceCircleRotate (-sourceParentAxis X Y) u ∈
      tsupport (circleAngularBin (angularBinCount θ) j))
    (ha : AngularBinActive (angularBinCount θ) j (sourceCenteredCellDirection X Y P Q) (3*θ)) :
    |inner ℝ (quarterTurn (u:Plane)) (P.center-Q.center)| ≤ 14028*(2:ℝ)^(-a)*θ := by
  have hd := dyadic_two_parent_diameter X Y hX hY hXa hYa hsep
    (Or.inl (hPX (P.center_mem hP))) (Or.inr (hQY (Q.center_mem hQ)))
  have hh := active_rotated_bin_direction_bound hθ hcap (sourceParentAxis X Y) j
    (sourceRadialUnit Q.center P.center) u hu ha
  exact (radial_perpendicular_bound P.center Q.center u hd hh).trans_eq (by ring)

theorem sourceParentBinLabels_activity {N n : ℕ} {sig t : ℝ} {X Y : DyadicSquare}
    {ρ ν : Measure Plane} {e : ParentDistanceBinLabel}
    (he : e ∈ sourceParentBinLabels N sig t X Y ρ ν n) :
    AngularBinActive (angularBinCount (graphUncappedAngularScale N sig t)) e.2
      (sourceCenteredCellDirection X Y (X.descendant e.1.1) (Y.descendant e.1.2))
      (3*graphUncappedAngularScale N sig t) := by
  classical
  obtain ⟨hj,hn⟩ := Finset.mem_sdiff.mp (sourceParentBinLabels_spec he).2.2
  by_contra ha
  exact hn (Finset.mem_filter.mpr ⟨hj,ha⟩)

end PlanarFalconer

end OAI
