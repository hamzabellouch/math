import OAI.Geometry.CylinderCovering.Beams.Finite

namespace OAI

open Filter
open scoped Topology

noncomputable section
namespace ShortenedBeam

open CylinderCovering

lemma radialDataPlus_frozenArea_eq (a : ℝ) (ha : a ≤ 2)
    (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) :
    RadialSweep.frozenArea (radialDataPlus a ha) N tag i =
      RadialSweep.frozenArea (radialData a ha) N tag i := by
  unfold RadialSweep.frozenArea
  rw [radialDataPlus_kappa, radialData_kappa]
  simp only [RadialSweep.radialError, RadialSweep.collar, RadialSweep.scalarBound,
    radialDataPlus, radialData, norm_neg]

lemma radialDataPlus_frozenArea {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 2)
    {N : ℕ} (hN : 0 < N) (tag : Fin N → ℝ) (i : Fin N) :
    RadialSweep.frozenArea (radialDataPlus a ha') N tag i =
      (1/(N:ℝ))*((2-a)+(8*a*(2-a)+1)/(N:ℝ))^2 /
        (4*Real.sqrt (1+‖velocity a (tag i)‖^2)) := by
  rw [radialDataPlus_frozenArea_eq]
  exact radialData_frozenArea ha ha' hN tag i

theorem finiteBeams_exact (a : ℝ) (ha : 0 < a) (ha' : a < 1/2)
    (tag : (N : ℕ) → Fin N → ℝ)
    (htag : ∀ N, RadialRiemann.IsTagged 0 1 N (tag N)) :
    ∃ Cminus Cplus : (N : ℕ) → Fin N → TriangularCovering.TriCylinder,
      (∀ N, 0 < N →
        (∀ i : Fin N,
          (Cminus N i).axis = axisMinus a (tag N i) ∧
          (Cplus N i).axis = axisPlus a (tag N i) ∧
          (Cminus N i).base = RadialSweep.frozenBase
            (radialData a (by linarith)) N (tag N) i ∧
          (Cplus N i).base = RadialSweep.frozenBase
            (radialDataPlus a (by linarith)) N (tag N) i ∧
          TriangularCovering.area (Cminus N i).base =
            (1/(N:ℝ))*((2-a)+(8*a*(2-a)+1)/(N:ℝ))^2 /
              (4*Real.sqrt (1+‖velocity a (tag N i)‖^2)) ∧
          TriangularCovering.area (Cplus N i).base =
            (1/(N:ℝ))*((2-a)+(8*a*(2-a)+1)/(N:ℝ))^2 /
              (4*Real.sqrt (1+‖velocity a (tag N i)‖^2))) ∧
        (∀ z ∈ beamMinus a, ∃ i : Fin N, z ∈ (Cminus N i).carrier) ∧
        (∀ z ∈ beamPlus a, ∃ i : Fin N, z ∈ (Cplus N i).carrier)) ∧
      Tendsto (fun N => TriangularCovering.totalArea (Cminus N) +
        TriangularCovering.totalArea (Cplus N)) atTop
        (𝓝 ((Real.sqrt 2/4)*BeamCost.beamCost a)) := by
  have ha2 : a ≤ 2 := by linarith
  obtain ⟨Cminus, hminus, hminuslim⟩ :=
    RadialSweep.aligned_radial_sweep (radialData a ha2) tag htag
  obtain ⟨Cplus, hplus, hpluslim⟩ :=
    RadialSweep.aligned_radial_sweep (radialDataPlus a ha2) tag htag
  refine ⟨Cminus, Cplus, ?_, ?_⟩
  · intro N hN
    obtain ⟨hminuslocal, hminuscover⟩ := hminus N hN
    obtain ⟨hpluslocal, hpluscover⟩ := hplus N hN
    refine ⟨?_, ?_, ?_⟩
    · intro i
      refine ⟨(hminuslocal i).1.trans (radialData_direction a (tag N i) ha2),
        (hpluslocal i).1.trans (radialDataPlus_direction a (tag N i) ha2),
        (hminuslocal i).2.1, (hpluslocal i).2.1, ?_, ?_⟩
      · exact (hminuslocal i).2.2.trans (radialData_frozenArea ha.le ha2 hN (tag N) i)
      · exact (hpluslocal i).2.2.trans (radialDataPlus_frozenArea ha.le ha2 hN (tag N) i)
    · simpa only [radialData_sweep] using hminuscover
    · simpa only [radialDataPlus_sweep] using hpluscover
  · have hlim := hminuslim.add hpluslim
    rw [radialData_total_weightedArea] at hlim
    exact hlim

end ShortenedBeam

end

end OAI
