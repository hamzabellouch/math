import OAI.Geometry.NodalSets.Waves.FiniteWaveSupport
import OAI.Geometry.NodalSets.Waves.LatticeFieldBounds
import OAI.Geometry.NodalSets.Waves.LocalWaveSupportCore

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped Topology
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
  {D U : Set Coord} {m J K k0 : ℕ}

theorem LocalCompactWaveData.lattice_residual_support
    (a : LocalCompactWaveData g w S D m J K k0)
    (hD : IsCompact D) (hUD : U ⊆ D) (hUb : Bornology.IsBounded U)
    {Ω : Set Coord} (hΩ : IsOpen Ω) (hDΩ : D ⊆ Ω) :
    ∃ C : Set Coord, IsCompact C ∧ C ⊆ Ω ∧ D ⊆ interior C ∧
      ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
        letI := hfin
        ∀ coeff : ((SourceGrid U n × Fin 3) × Fin 2) → ℝ,
          let u := gaussianWaveField
            (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff
          tsupport u ⊆ C ∧
          tsupport (fun z ↦ sourceWeightedOperator g w (fun x ↦ (u x : ℂ)) z +
            ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*(u z:ℂ)) ⊆ C ∧
          ∀ x ∉ C, ∀ k : ℕ,
            iteratedFDeriv ℝ k (fun z ↦ sourceWeightedOperator g w (fun x ↦ (u x:ℂ)) z +
              ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*(u z:ℂ)) x = 0 := by
  obtain ⟨C,hC,hCΩ,hDC,hcore⟩ := a.uniform_support_core hD hΩ hDΩ
  refine ⟨C,hC,hCΩ,hDC,?_⟩
  filter_upwards [hcore,eventually_gt_atTop (0:ℕ)] with n hn hnpos
  have := finite_source_grid hUb hnpos
  let hfin := Fintype.ofFinite (SourceGrid U n)
  let := hfin
  refine ⟨hfin,?_⟩
  intro coeff
  let V := fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2
  have hVs (i : SourceGrid U n × Fin 3) : tsupport (V i) ⊆ C :=
    (hn (latticeFrame a.cover hUD n i.1,i.2)).1
  have hu := gaussianWaveField_tsupport_subset V coeff hC.isClosed hVs
  have hc := complexified_tsupport_subset (gaussianWaveField V coeff) hC.isClosed hu
  refine ⟨hu,source_residual_tsupport_subset g w _ _ hC.isClosed hc,?_⟩
  intro x hx k
  exact source_residual_derivative_zero g w _ _ x (fun hz ↦ hx (hc hz)) k

end
end Yau.Geometry

end OAI
