import OAI.Probability.SLE.Mass.DiskChartMass
import OAI.Probability.SLE.Geometry.PhysicalCellDisk

namespace OAI

/-! The disk scalar controls the actual centered and rescaled inverse
Loewner pushforward. The marked angle is retained exactly. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Multipoint

lemma diskChartMass_eq_of_coordinates
    (κ θ : ℝ) (f H : ℂ → ℂ)
    (he : ∀ z ∈ upperHalfPlane, f (Target.diskMap θ z)=H z)
    (μ : Measure upperHalfPlane) :
    diskChartMass κ θ f μ = weightedImageMass (fun z : upperHalfPlane => H z)
      (fun z : upperHalfPlane => ENNReal.ofReal (‖deriv H z‖^dimension κ)) μ := by
  have hmap : (fun z : upperHalfPlane => f (Target.diskMap θ z))=
      (fun z : upperHalfPlane => H z) := funext (fun z => he z z.property)
  have hder (z : upperHalfPlane) : deriv (f ∘ Target.diskMap θ) z=deriv H z := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_upperHalfPlane.mem_nhds z.property] with w hw
    exact he w hw
  unfold diskChartMass
  rw [hmap]
  congr 1
  funext z
  rw [hder]

lemma diskToHalfPlane_real_affine (c a : ℝ) (z ξ : ℂ)
    (hξ : ξ ∈ ball (0:ℂ) 1) :
    diskToHalfPlane ((c:ℂ)+(a:ℂ)*z) ξ =
      (c:ℂ)+(a:ℂ)*diskToHalfPlane z ξ := by
  simp only [diskToHalfPlane,star_add,star_mul,Complex.star_def,Complex.conj_ofReal]
  field_simp [disk_denominator_ne hξ]
  ring

lemma physicalDiskChart_normalized
    (F G : ℝ≥0 → ℂ → ℂ) (t : ℝ≥0) (z : ℂ) (c a θ : ℝ)
    (he : G t z=(c:ℂ)+(a:ℂ)*Complex.exp (θ*Complex.I))
    {ξ : ℂ} (hξ : ξ ∈ ball (0:ℂ) 1) :
    physicalDiskChart id F G t z ξ =
      F t ((c:ℂ)+(a:ℂ)*Target.diskMapInv θ ξ) := by
  change F t (diskToHalfPlane (G t z) ξ)=_
  rw [he,diskToHalfPlane_real_affine c a _ ξ hξ,← Target.diskMapInv_eq_diskToHalfPlane]

lemma physicalDiskChart_mass_eq
    (κ θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi)
    (F G : ℝ≥0 → ℂ → ℂ) (t : ℝ≥0) (z : ℂ) (c a : ℝ)
    (he : G t z=(c:ℂ)+(a:ℂ)*Complex.exp (θ*Complex.I))
    (μ : Measure upperHalfPlane) :
    diskChartMass κ θ (physicalDiskChart id F G t z) μ =
      weightedImageMass (fun w : upperHalfPlane => F t ((c:ℂ)+(a:ℂ)*w))
        (fun w : upperHalfPlane => ENNReal.ofReal
          (‖deriv (fun v : ℂ => F t ((c:ℂ)+(a:ℂ)*v)) w‖^dimension κ)) μ := by
  apply diskChartMass_eq_of_coordinates κ θ (physicalDiskChart id F G t z)
    (fun v : ℂ => F t ((c:ℂ)+(a:ℂ)*v))
  intro w hw
  rw [physicalDiskChart_normalized F G t z c a θ he (Target.diskMap_maps hθ hw),
    Target.diskMapInv_diskMap hθ hw]

lemma IsCapacityTwoWitness.physical_quarter_mass_bounds
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hgrowth : PublishedDiskUnivalentGrowth)
    (κ : ℝ) (hκ : 0 < κ) (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi)
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ t) (a : ℝ)
    (he : G t z=(U t:ℂ)+(a:ℂ)*Complex.exp (θ*Complex.I))
    (μ : Measure upperHalfPlane) [IsFiniteMeasureOnCompacts μ] :
    let f := physicalDiskChart id F G t z
    let ν := weightedImageMass (fun w : upperHalfPlane => F t ((U t:ℂ)+(a:ℂ)*w))
      (fun w : upperHalfPlane => ENNReal.ofReal
        (‖deriv (fun v : ℂ => F t ((U t:ℂ)+(a:ℂ)*v)) w‖^dimension κ)) μ
    let L := ENNReal.ofReal (compactWeightedMass (Target.diskMassWeight κ θ hθ)
      (Target.diskSourceHalfPlane θ) μ)
    ENNReal.ofReal ((fullRadius G t z/16)^dimension κ)*L ≤ ν (f '' Target.diskK) ∧
      ν (f '' Target.diskK) ≤ ENNReal.ofReal ((16*fullRadius G t z)^dimension κ)*L := by
  obtain ⟨hd,hi,_,hder,_⟩ := hw.physical_disk_chart id differentiableOn_id
    (fun _ _ _ _ h => h) t z hz
  have hder' : ‖deriv (physicalDiskChart id F G t z) 0‖=fullRadius G t z := by
    simpa [physicalConformalRadius] using hder
  have hb := diskChartMass_quarter_bounds hgrowth κ hκ θ hθ
    (physicalDiskChart id F G t z) hd hi μ
  rw [hder',physicalDiskChart_mass_eq κ θ hθ F G t z (U t) a he μ] at hb
  exact hb

end SLEExactGauge

end

end OAI
