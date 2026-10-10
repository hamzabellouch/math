import Mathlib
import OAI.Analysis.Conductivity.Fourier.PureModeWallRegion
import OAI.Analysis.Conductivity.Walls.SimpleCriticalWallCoordinates
import OAI.Analysis.Conductivity.Geometry.LocalFamilyRegionCoordinates

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_simple_critical_wall_region
    {u v : P×Coord3 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P)
    {σ lam k : ℝ} (hσ : σ≠0) (hlam : lam≠0) (hk : k≠0)
    (hub : ∀ y,u (p,y)=y 0)
    (hvb : ∀ y,v (p,y)=pureWallMode σ lam k (boxCoordinates y))
    {x : Coord3} (hxz : x 2=0)
    {U : Set Coord3} (hU : IsOpen U) (hx : x∈U) :
    ∃ B : VanishingCorrectionRegion (fun z => ![u z,v z]) p U,x∈B.region := by
  obtain ⟨Y,hYs,hYU,hY,hYb,hsm,hinv,w,hw,hwb,hwz,hpot⟩ :=
    exists_simple_critical_wall_coordinates hu hv p hσ hk hub hvb hxz hU hx
  have huv : ContDiff ℝ (↑(⊤:ℕ∞)) (fun z => ![u z,v z]) :=
    contDiff_pi.mpr (by intro i; fin_cases i; exact hu; exact hv)
  apply exists_transported_vanishing_region huv (wallCoordinatePair_parametric_smooth hw)
    p Y hY hsm hinv hYU hYs hpot
  intro A hA hxA
  rw [hYb] at hxA ⊢
  exact exists_pure_mode_wall_region hw p hwz hσ hlam hk hwb hA hxA hxz

end ScalarConductivity

end
end

end OAI
