import OAI.Geometry.PeriodicTiling.ConstituentAssembly
import OAI.Geometry.PeriodicTiling.MarkedCell
import OAI.Geometry.PeriodicTiling.GridRigidity
import OAI.Geometry.PeriodicTiling.LatticeDescent
import OAI.Geometry.PeriodicTiling.QuotientTiling
import OAI.Geometry.PeriodicTiling.TilingTransport

namespace OAI

noncomputable section

namespace PeriodicTilingThree.MarkedTile.ResidueSection

open CyclicQuotient

variable {m : ℕ} [NeZero m] (s : ResidueSection m)

theorem no_euclideanFullyPeriodic
    (hm : 2 ≤ m) (hdiff : RigidDifferences m s.Tstar)
    (Q : ℕ) [NeZero Q] (F : Finset (CyclicQuotient.Group Q)) (hF0 : 0 ∈ F)
    (haperiodic : ∀ B, Tiles F B → ¬ FullyPeriodic B)
    {A : Set (Space 3)}
    (htile : AETiles
      (Thickening (s.finalTile (kernelStep Q) (representatives Q F))) A) :
    ¬ EuclideanFullyPeriodic A := by
  classical
  rintro ⟨b, hb⟩
  let U := representatives Q F
  let w := kernelStep Q
  have h0 : 0 ∈ U := zero_mem_representatives Q hF0
  have hw : w ∉ U := kernelStep_not_mem_representatives Q F
  have htyped := s.typed_constituents hm h0 hw htile
  have hinj := s.center_injective hm h0 hw htile
  obtain ⟨c₀, _hc₀, hgrid'⟩ := periodic_voxel_assembly_grid_range hm
    s.Tstar_subset_T0 (s.Tstar_subset_T1 w) hdiff s.card_T0 (s.card_T1 w)
    b (fun v hv => period_centers (hb v hv)) hb htyped
  have hgrid : centers m U A =
      Set.range (fun z : Lattice 3 => c₀ + scaledCast m z) := hgrid'
  let B := normalizedComplement m c₀ A
  have hBtile : Tiles U B := tiles_of_centers_grid hinj hgrid
  have hAne : A.Nonempty := by
    obtain ⟨z, hz⟩ := hBtile.complement_nonempty
    exact ⟨c₀ + scaledCast m z, hz⟩
  have hAgrid : ∀ a ∈ A, ∃ z : Lattice 3, c₀ + scaledCast m z = a := by
    intro a ha
    have hc := subset_centers (m := m) h0 A ha
    rw [hgrid] at hc
    exact hc
  have hBperiodic : FullyPeriodic B :=
    fullyPeriodic_normalizedComplement m c₀ hAne hAgrid ⟨b, hb⟩
  have hnormalized := normalized_typedAETiles m (NeZero.ne m) c₀ hgrid htyped
  have hkernel : ∀ k ∈ (projection Q).ker, Period B k :=
    s.kernel_periods_of_marked_cells Q B hnormalized
  have hquotient : Tiles F ((projection Q) '' B) := by
    have h := tiles_image_of_kernel_periods (projection Q) (projection_surjective Q)
      hBtile hkernel
    simpa only [U, projection_image_representatives] using h
  exact haperiodic _ hquotient
    (FullyPeriodic.image_of_surjective (projection Q) (projection_surjective Q) hBperiodic)

end PeriodicTilingThree.MarkedTile.ResidueSection

end

end OAI
