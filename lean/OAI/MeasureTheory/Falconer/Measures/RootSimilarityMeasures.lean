import OAI.MeasureTheory.Falconer.Geometry.RootSimilarityGeometry
import OAI.MeasureTheory.Falconer.Radial.SourceRadialSetup

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem dilate_ball_preimage {s : ℝ} (hs : 0 < s) (x : Plane) (r : ℝ) :
    (fun y : Plane => s • y) ⁻¹' ball x r = ball (s⁻¹ • x) (r/s) := by
  ext y
  simp only [mem_preimage,mem_ball]
  have he : dist (s • y) x = s*dist y (s⁻¹ • x) := by
    calc
      _ = dist (s • y) (s • (s⁻¹ • x)) := by rw [smul_inv_smul₀ hs.ne']
      _ = _ := by rw [dist_smul₀,Real.norm_eq_abs,abs_of_pos hs]
  rw [he,lt_div_iff₀ hs,mul_comm s]

theorem BallBound.dilate {ρ : Measure Plane} {u C s : ℝ}
    (hb : BallBound ρ u C) (hs : 0 < s) :
    BallBound (ρ.map (fun x : Plane => s • x)) u (C/s^u) := by
  intro x r hr
  rw [Measure.map_apply (by fun_prop) measurableSet_ball,dilate_ball_preimage hs]
  apply (hb (s⁻¹ • x) (r/s) (by positivity)).trans_eq
  congr 1
  rw [Real.div_rpow hr.le hs.le]
  ring

theorem dilate_carried_compact (ρ : Measure Plane) (A : Set Plane)
    (hA : IsCompact A) (hρ : ρ Aᶜ = 0) (s : ℝ) :
    (ρ.map (fun x : Plane => s • x)) ((fun x : Plane => s • x) '' A)ᶜ = 0 := by
  rw [Measure.map_apply (by fun_prop) (hA.image (by fun_prop)).measurableSet.compl]
  apply measure_mono_null _ hρ
  intro x hx hmem
  exact hx ⟨x,hmem,rfl⟩

theorem dilate_carried_root (ρ : Measure Plane) (Q : DyadicSquare)
    (hρ : ρ Q.carrierᶜ = 0) {s : ℝ} (hs : 0 < s) :
    (ρ.map (fun x : Plane => s • x)) (Q.dilate s).carrierᶜ = 0 := by
  rw [Measure.map_apply (by fun_prop) (DyadicSquare.measurable _).compl,
    preimage_compl,DyadicSquare.dilate_carrier_preimage _ hs]
  exact hρ

theorem radial_pushforward_dilate (ρ : Measure Plane) {s : ℝ} (hs : 0 < s) (x : Plane) :
    (ρ.map (fun y : Plane => s • y)).map (sourceRadialUnit (s • x)) =
      ρ.map (sourceRadialUnit x) := by
  rw [Measure.map_map (measurable_sourceRadialUnit _) (by fun_prop)]
  congr 1
  funext y
  exact sourceRadialUnit_dilate hs x y

theorem distanceSet_dilate (E : Set Plane) {s : ℝ} (hs : 0 < s) :
    distanceSet ((fun x : Plane => s • x) '' E) = (fun r : ℝ => s*r) '' distanceSet E := by
  ext r
  constructor
  · rintro ⟨x,⟨a,ha,rfl⟩,y,⟨b,hb,rfl⟩,hr⟩
    refine ⟨dist a b,⟨a,ha,b,hb,rfl⟩,?_⟩
    simpa only [dist_smul₀,Real.norm_eq_abs,abs_of_pos hs] using hr
  · rintro ⟨t,⟨x,hx,y,hy,rfl⟩,rfl⟩
    exact ⟨s • x,⟨x,hx,rfl⟩,s • y,⟨y,hy,rfl⟩,by simp [dist_smul₀,abs_of_pos hs]⟩

theorem distanceSet_positive_of_dilate (E : Set Plane) {s : ℝ} (hs : 0 < s)
    (hpos : 0 < volume (distanceSet ((fun x : Plane => s • x) '' E))) :
    0 < volume (distanceSet E) := by
  rw [distanceSet_dilate E hs] at hpos
  have he : (fun r : ℝ => s*r) '' distanceSet E = (fun r : ℝ => s⁻¹*r) ⁻¹' distanceSet E := by
    ext r
    constructor
    · rintro ⟨t,ht,rfl⟩
      simpa only [mem_preimage,inv_mul_cancel_left₀ hs.ne'] using ht
    · intro hr
      exact ⟨s⁻¹*r,hr,mul_inv_cancel_left₀ hs.ne' r⟩
  rw [he,Real.volume_preimage_mul_left (inv_ne_zero hs.ne')] at hpos
  exact (ENNReal.mul_pos_iff.mp hpos).2

end PlanarFalconer

end OAI
