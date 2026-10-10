import OAI.Geometry.CylinderCovering.Radial.SqrtRealizationDefinitions
import OAI.Geometry.CylinderCovering.Radial.SqrtCap
import OAI.Geometry.CylinderCovering.Radial.FinitePair
import OAI.Geometry.CylinderCovering.Radial.PairedSweep
import OAI.Geometry.CylinderCovering.Radial.CapCoverage

namespace OAI

noncomputable section
namespace CylinderCovering.RadialSqrtCap
open Set Filter
open scoped Topology

theorem exists_coverage_threshold {β : ℝ} (hβ : 0 < β) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      RadialPairedSweep.tetrahedron (Real.sqrt 2) ⊆
        RadialPairedSweep.upperSweep (Real.sqrt 2) ε (cap β ε) ∪
        RadialPairedSweep.lowerSweep (Real.sqrt 2) ε (cap β ε) := by
  obtain ⟨δ, hδ, hpad⟩ := exists_padding_threshold hβ
  refine ⟨δ, hδ, ?_⟩
  intro ε he hεδ
  obtain ⟨heβ, hcap⟩ := hpad ε he hεδ
  have hlinear := RadialCapCoverage.linear_covers (h := Real.sqrt 2)
    (beta := β / 2) (by positivity) he (by linarith only [heβ])
  have hmono : ∀ q ∈ Icc (-1 : ℝ) 1,
      RadialCaps.linearCap (β / 2) ε q ≤ cap β ε q := by
    intro q hq
    exact hcap q (abs_le.mpr hq)
  exact hlinear.trans (Set.union_subset_union
    (RadialPairedSweep.upperSweep_mono _ _ hmono)
    (RadialPairedSweep.lowerSweep_mono _ _ hmono))

theorem finite_family {β ε : ℝ}
    (hcover : RadialPairedSweep.tetrahedron (Real.sqrt 2) ⊆
      RadialPairedSweep.upperSweep (Real.sqrt 2) ε (cap β ε) ∪
      RadialPairedSweep.lowerSweep (Real.sqrt 2) ε (cap β ε))
    (tagU tagL : (N : ℕ) → Fin N → ℝ)
    (htagU : ∀ N, RadialRiemann.IsTagged (-1) 1 N (tagU N))
    (htagL : ∀ N, RadialRiemann.IsTagged (-1) 1 N (tagL N)) :
    ∃ C : (N : ℕ) → Fin (2 * N) → TriangularCovering.TriCylinder,
      FamilyConclusion β ε tagU tagL C := by
  obtain ⟨U, L, hUL, hlim⟩ := RadialPairedSweep.paired_radial_sweeps
    (Real.sqrt 2) ε (by positivity) (cap β ε)
    (cap_continuous β ε).continuousOn (fun q _ => cap_nonneg β ε q)
    tagU tagL htagU htagL
  refine ⟨fun N => RadialPairedSweep.join (U N) (L N), ?_, ?_⟩
  · intro N hN
    obtain ⟨haxes, hU, hL⟩ := hUL N hN
    have hwhole := RadialPairedSweep.join_covers_union (U N) (L N) hU hL
    refine ⟨?_, ?_, hwhole⟩
    · intro i
      simpa only [RadialPairedSweep.join_upper, RadialPairedSweep.join_lower] using haxes i
    · intro z hz
      exact hwhole z (hcover hz)
  · rw [RadialPairedSweep.physicalCost_sqrt_two] at hlim
    exact RadialPairedSweep.join_totalArea_tendsto U L hlim

theorem full_square_root_cap : FullStatement := by
  refine ⟨fun β ε hβ he => cost_expansion hβ he, ?_, ?_⟩
  · intro β hβ
    obtain ⟨δ, hδ, hcover⟩ := exists_coverage_threshold hβ
    refine ⟨δ, hδ, ?_⟩
    intro ε he hεδ
    have hc := hcover ε he hεδ
    exact ⟨hc, fun tagU tagL htagU htagL => finite_family hc tagU tagL htagU htagL⟩
  · intro β hβ hβmax
    obtain ⟨δc, hδc, hcover⟩ := exists_coverage_threshold hβ
    obtain ⟨δs, hδs, hsave⟩ := exists_saving_threshold hβ hβmax
    refine ⟨min δc δs, lt_min hδc hδs, ?_⟩
    intro ε he hεδ
    have hc := hcover ε he (lt_of_lt_of_le hεδ (min_le_left _ _))
    have hs := hsave ε he (lt_of_lt_of_le hεδ (min_le_right _ _))
    refine ⟨hs, ?_⟩
    intro tagU tagL htagU htagL
    obtain ⟨C, hC⟩ := finite_family hc tagU tagL htagU htagL
    refine ⟨C, hC, ?_⟩
    apply RadialPairedSweep.eventually_strict_finite_cost C hC.2
    have hp : 0 < 2 * Real.sqrt 2 := by positivity
    simpa only [mul_one] using mul_lt_mul_of_pos_left hs hp

end CylinderCovering.RadialSqrtCap

end

end OAI
