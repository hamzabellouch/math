import OAI.Geometry.CylinderCovering.Beams.StatementsDefinitions
import OAI.Geometry.CylinderCovering.Beams.Radial
import OAI.Geometry.CylinderCovering.Radial.Assembly

namespace OAI

open Filter
open scoped Topology

namespace ShortenedBeam

theorem coverageStatement : CoverageStatement := by
  intro a ha ha'
  exact ⟨beamMinus_isCompact a, beamPlus_isCompact a, tetrahedron_covered ha.le ha'.le⟩

theorem finiteBeams_of_aligned
    (hRadial : CylinderCovering.RadialSweep.AlignedStatement) : FiniteBeamsStatement := by
  intro a ha ha' tag htag
  have ha2 : a ≤ 2 := by linarith
  obtain ⟨Cminus, hminus, hminuslim⟩ := hRadial (radialData a ha2) tag htag
  obtain ⟨Cplus, hplus, hpluslim⟩ := hRadial (radialDataPlus a ha2) tag htag
  refine ⟨Cminus, Cplus, ?_, ?_⟩
  · intro N hN
    obtain ⟨hminusaxis, hminuscover⟩ := hminus N hN
    obtain ⟨hplusaxis, hpluscover⟩ := hplus N hN
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact ⟨(hminusaxis i).1.trans (radialData_direction a (tag N i) ha2),
        (hplusaxis i).1.trans (radialDataPlus_direction a (tag N i) ha2)⟩
    · simpa only [radialData_sweep] using hminuscover
    · simpa only [radialDataPlus_sweep] using hpluscover
  · have hlim := hminuslim.add hpluslim
    rw [radialData_total_weightedArea] at hlim
    exact hlim

theorem exists_finite_beam_cover (hfinite : FiniteBeamsStatement)
    {a ε : ℝ} (ha : 0 < a) (ha' : a < 1/2) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∃ Cminus Cplus : Fin N → TriangularCovering.TriCylinder,
      (∀ z ∈ beamMinus a, ∃ i : Fin N, z ∈ (Cminus i).carrier) ∧
      (∀ z ∈ beamPlus a, ∃ i : Fin N, z ∈ (Cplus i).carrier) ∧
      TriangularCovering.totalArea Cminus + TriangularCovering.totalArea Cplus ≤
        (Real.sqrt 2/4)*CylinderCovering.BeamCost.beamCost a + ε := by
  let tag : (N : ℕ) → Fin N → ℝ := fun N i =>
    CylinderCovering.RadialRiemann.point 0 1 N i
  have htag : ∀ N, CylinderCovering.RadialRiemann.IsTagged 0 1 N (tag N) := by
    intro N i
    have hN : 0 < N := Nat.zero_lt_of_lt i.isLt
    have hNreal : (0:ℝ) < N := by exact_mod_cast hN
    have hstep : 0 < CylinderCovering.RadialRiemann.step 0 1 N := by
      unfold CylinderCovering.RadialRiemann.step
      positivity
    refine ⟨le_rfl, ?_⟩
    dsimp [tag, CylinderCovering.RadialRiemann.point]
    push_cast
    nlinarith
  obtain ⟨Cminus,Cplus,hcover,hlim⟩ := hfinite a ha ha' tag htag
  have hevent : ∀ᶠ N in atTop,
      TriangularCovering.totalArea (Cminus N) + TriangularCovering.totalArea (Cplus N) <
        (Real.sqrt 2/4)*CylinderCovering.BeamCost.beamCost a + ε :=
    (tendsto_order.1 hlim).2 _ (by linarith)
  obtain ⟨N,hcost,hN⟩ := (hevent.and (eventually_ge_atTop 1)).exists
  have hNpos : 0 < N := by omega
  exact ⟨N,hNpos,Cminus N,Cplus N,(hcover N hNpos).2.1,
    (hcover N hNpos).2.2,hcost.le⟩

theorem finiteBeamsStatement : FiniteBeamsStatement :=
  finiteBeams_of_aligned CylinderCovering.RadialSweep.aligned_radial_sweep

theorem finite_beam_cover {a ε : ℝ} (ha : 0 < a) (ha' : a < 1/2) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∃ Cminus Cplus : Fin N → TriangularCovering.TriCylinder,
      (∀ z ∈ beamMinus a, ∃ i : Fin N, z ∈ (Cminus i).carrier) ∧
      (∀ z ∈ beamPlus a, ∃ i : Fin N, z ∈ (Cplus i).carrier) ∧
      TriangularCovering.totalArea Cminus + TriangularCovering.totalArea Cplus ≤
        (Real.sqrt 2/4)*CylinderCovering.BeamCost.beamCost a + ε :=
  exists_finite_beam_cover finiteBeamsStatement ha ha' hε

end ShortenedBeam

end OAI
