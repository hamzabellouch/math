import OAI.MeasureTheory.Falconer.Estimates.CollisionFubini
import OAI.MeasureTheory.Falconer.Shells.DistanceLinearization
import OAI.MeasureTheory.Falconer.Geometry.BinEstimates

namespace OAI

/-! # The local collision estimate in the all-dimensional suffix step

A projection test on the entire second conditional cell controls every
translated collision window. Quadratic distance linearization transfers
that test to the original distance pushforward, before any cell grouping.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem projection_shifted_band_bound (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (e : Space d) {w : ℝ} (hw : 0 < w) (C s : ℝ) :
    (μ.prod μ) {z : Space d × Space d | |inner ℝ e (z.1-z.2)-s| ≤ C*w} ≤
      ((PlanarFalconer.bandOffsets C).card : ℝ≥0∞) *
        (μ.prod μ) {z : Space d × Space d | |inner ℝ e (z.1-z.2)| ≤ w} := by
  let f : Space d → ℝ := fun y => inner ℝ e y
  have hf : Measurable f := by dsimp [f]; fun_prop
  let ν := Measure.map f μ
  have he (v s : ℝ) :
      (ν.prod ν) {z : ℝ × ℝ | |z.1-z.2-s| ≤ v} =
      (μ.prod μ) {z : Space d × Space d | |inner ℝ e (z.1-z.2)-s| ≤ v} := by
    rw [show ν.prod ν = Measure.map (Prod.map f f) (μ.prod μ) from
      Measure.map_prod_map μ μ hf hf,Measure.map_apply (hf.prodMap hf) (by measurability)]
    congr 1
    ext z
    change |f z.1-f z.2-s| ≤ v ↔ |inner ℝ e (z.1-z.2)-s| ≤ v
    simp only [f,inner_sub_right]
  have h := PlanarFalconer.real_bin_shifted_self_band_bound ν hw C s
  rw [he] at h
  have hz := he w 0
  simp only [sub_zero] at hz
  rwa [hz] at h

theorem affine_distance_collision {x x' y y' e : Space d} {w : ℝ}
    (hx : |dist x y-inner ℝ e (x-y)| ≤ w)
    (hx' : |dist x' y'-inner ℝ e (x'-y')| ≤ w)
    (hc : |dist x y-dist x' y'| ≤ w) :
    |inner ℝ e (y-y')-inner ℝ e (x-x')| ≤ 3*w := by
  have he : inner ℝ e (y-y')-inner ℝ e (x-x') =
      -(inner ℝ e (x-y)-inner ℝ e (x'-y')) := by
    simp only [inner_sub_right]
    ring
  rw [he,abs_neg]
  obtain ⟨h₁,h₂⟩ := abs_le.mp hx
  obtain ⟨h₃,h₄⟩ := abs_le.mp hx'
  obtain ⟨h₅,h₆⟩ := abs_le.mp hc
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem local_distance_collision_bound (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (P Q : DyadicCube d) (e : Space d) {w : ℝ} (hw : 0 < w)
    (haff : ∀ x ∈ P.carrier, ∀ y ∈ Q.carrier, |dist x y-inner ℝ e (x-y)| ≤ w)
    {H : ℝ≥0∞}
    (hproj : ((ν.restrict Q.carrier).prod (ν.restrict Q.carrier))
      {z : Space d × Space d | |inner ℝ e (z.1-z.2)| ≤ w} ≤ H) :
    (((μ.restrict P.carrier).prod (ν.restrict Q.carrier)).prod
      ((μ.restrict P.carrier).prod (ν.restrict Q.carrier)))
        {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ w} ≤
      (μ P.carrier)^2 * (((PlanarFalconer.bandOffsets 3).card : ℝ≥0∞)*H) := by
  apply (pair_collision_fiber_bound (μ.restrict P.carrier) (ν.restrict Q.carrier)
    _ (by measurability) (((PlanarFalconer.bandOffsets 3).card : ℝ≥0∞)*H) ?_).trans_eq
      (by simp)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem P.measurable),
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem P.measurable)] with xx hx hx'
  apply le_trans _ (mul_le_mul' le_rfl hproj)
  apply le_trans _ (projection_shifted_band_bound (ν.restrict Q.carrier) e hw 3
    (inner ℝ e (xx.1-xx.2)))
  apply measure_mono_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem Q.measurable),
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem Q.measurable)] with yy hy hy'
  intro hc
  exact affine_distance_collision (haff xx.1 hx yy.1 hy) (haff xx.2 hx' yy.2 hy') hc

/-- The geometric hypotheses are supplied by the actual center separation
and common child side, not by an abstract distance approximation. -/
theorem suffix_cell_collision_bound (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (P Q : DyadicCube d) (hP : 0 < P.side) (hQ : Q.side = P.side)
    {g w : ℝ} (hg : 0 < g) (hsep : g ≤ ‖P.center-Q.center‖) (hw : 0 < w)
    (hsmall : 2*(d:ℝ)*P.side^2/g ≤ w) {H : ℝ≥0∞}
    (hproj : ((ν.restrict Q.carrier).prod (ν.restrict Q.carrier))
      {z : Space d × Space d |
        |inner ℝ (‖P.center-Q.center‖⁻¹ • (P.center-Q.center)) (z.1-z.2)| ≤ w} ≤ H) :
    (((μ.restrict P.carrier).prod (ν.restrict Q.carrier)).prod
      ((μ.restrict P.carrier).prod (ν.restrict Q.carrier)))
        {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ w} ≤
      (μ P.carrier)^2 * (((PlanarFalconer.bandOffsets 3).card : ℝ≥0∞)*H) :=
  local_distance_collision_bound μ ν P Q _ hw
    (fun _ hx _ hy => (P.distance_linearization Q hP hQ hg hsep hx hy).trans hsmall) hproj

end Falconer

end OAI
