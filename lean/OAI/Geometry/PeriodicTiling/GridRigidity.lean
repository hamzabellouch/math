import OAI.Geometry.PeriodicTiling.SeparatedCenters
import OAI.Geometry.PeriodicTiling.CenterFiniteness
import OAI.Geometry.PeriodicTiling.AuxiliaryCubes
import OAI.Geometry.PeriodicTiling.PeriodicVolume
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Abel

namespace OAI

noncomputable section

namespace PeriodicTilingThree

open Set MeasureTheory

theorem grid_difference_of_cube_chain {m : ℕ} {C : Set (Space 3)}
    (hnear : ∀ c c' : C, ‖(c' : Space 3) - (c : Space 3)‖ ≤ (m : ℝ) →
      (c' : Space 3) - (c : Space 3) ∈ scaledGrid m)
    {c₀ c : C}
    (hchain : Relation.ReflTransGen
      (CoverIntersects (fun a : C => auxiliaryCube m a)) c₀ c) :
    (c : Space 3) - (c₀ : Space 3) ∈ scaledGrid m := by
  induction hchain with
  | refl => simpa only [sub_self] using (scaledGrid m).zero_mem
  | @tail a b _ hab ih =>
      have hedge := hnear a b (auxiliaryCube_inter_norm_le hab)
      have hid : (b : Space 3) - (c₀ : Space 3) =
          ((b : Space 3) - (a : Space 3)) + ((a : Space 3) - (c₀ : Space 3)) := by
        abel
      rw [hid]
      exact (scaledGrid m).add_mem hedge ih

theorem grid_coset_of_auxiliary_cover {m : ℕ} (hm : 0 < m)
    (C : Set (Space 3))
    (hlocal : LocallyFinite (fun c : C => auxiliaryCube m c))
    (hcover : ∀ x : Space 3, ∃ c : C, x ∈ auxiliaryCube m c)
    (hnear : ∀ c c' : C, ‖(c' : Space 3) - (c : Space 3)‖ ≤ (m : ℝ) →
      (c' : Space 3) - (c : Space 3) ∈ scaledGrid m) :
    ∃ c₀ ∈ C, C = {x : Space 3 | x - c₀ ∈ scaledGrid m} := by
  obtain ⟨c₀, _hc₀⟩ := hcover 0
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hgrid (c : C) : (c : Space 3) - (c₀ : Space 3) ∈ scaledGrid m := by
    apply grid_difference_of_cube_chain hnear
    exact closed_cover_chain_connected (fun a : C => auxiliaryCube m a)
      (fun a => auxiliaryCube_nonempty m a) (fun a => auxiliaryCube_isClosed m a)
      hlocal hcover c₀ c
  refine ⟨c₀, c₀.property, ?_⟩
  ext x
  constructor
  · intro hx
    exact hgrid ⟨x, hx⟩
  · intro hx
    obtain ⟨c, hxc⟩ := hcover x
    have hdiff : x - (c : Space 3) ∈ scaledGrid m := by
      have h := (scaledGrid m).sub_mem hx (hgrid c)
      have hid : (x - (c₀ : Space 3)) - ((c : Space 3) - (c₀ : Space 3)) =
          x - (c : Space 3) := by abel
      rwa [hid] at h
    have hnorm : ‖x - (c : Space 3)‖ < (m : ℝ) := by
      have hle : dist x (c : Space 3) ≤ (m : ℝ) / 2 := hxc
      rw [dist_eq_norm] at hle
      linarith
    have hxc' : x = (c : Space 3) :=
      sub_eq_zero.mp (scaledGrid_eq_zero_of_norm_lt hm hdiff hnorm)
    rw [hxc']
    exact c.property

theorem periodic_voxel_assembly_grid
    {m : ℕ} (hm : 2 ≤ m) {S0 S1 S : Finset (Lattice 3)}
    (h0 : S ⊆ S0) (h1 : S ⊆ S1) (hdiff : RigidDifferences m S)
    (hcard0 : S0.card = m ^ 3) (hcard1 : S1.card = m ^ 3)
    {C C1 : Set (Space 3)}
    (b : Module.Basis (Fin 3) ℝ (Space 3))
    (hp : ∀ v ∈ latticeOfBasis b, Period C v)
    (ht : ∀ v ∈ latticeOfBasis b, Period C1 v)
    (htile : TypedAETiles (Thickening S0) (Thickening S1) C C1) :
    ∃ c₀ ∈ C, C = {x : Space 3 | x - c₀ ∈ scaledGrid m} := by
  have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hsep : C.Pairwise (fun x y => (m : ℝ) ≤ ‖x - y‖) := by
    intro x hx y hy hxy
    have hne : (⟨y, hy⟩ : C) ≠ ⟨x, hx⟩ := by
      intro heq
      exact hxy (congrArg Subtype.val heq).symm
    exact typed_centers_separated hm h0 h1 hdiff htile hne
  have hcount := centers_countable hmR hsep
  have hfin : ∀ K : Set (Space 3), Bornology.IsBounded K → (C ∩ K).Finite :=
    fun _ hK => centers_finite_on_bounded hmR hsep hK
  have hnear : ∀ c c' : C, ‖(c' : Space 3) - (c : Space 3)‖ ≤ (m : ℝ) →
      (c' : Space 3) - (c : Space 3) ∈ scaledGrid m := by
    intro c c' hcc'
    by_cases heq : c = c'
    · subst c'
      simpa only [sub_self] using (scaledGrid m).zero_mem
    · exact typed_nearby_centers_mem_scaledGrid hm h0 h1 hdiff htile heq hcc'
  have hvol : volume (Thickening S1) = volume (Thickening S0) := by
    rw [thickening_volume, thickening_volume, hcard0, hcard1]
  have hJvol : volume (auxiliaryCube m 0) = volume (Thickening S0) := by
    rw [auxiliaryCube_volume, thickening_volume, hcard0]
  have hpack : Pairwise fun c c' : C => AEDisjoint volume
      (PeriodicVolume.translate c (auxiliaryCube m 0))
      (PeriodicVolume.translate c' (auxiliaryCube m 0)) := by
    intro c c' hne
    change AEDisjoint volume {x | x - (c : Space 3) ∈ auxiliaryCube m 0}
      {x | x - (c' : Space 3) ∈ auxiliaryCube m 0}
    rw [auxiliaryCube_translate, auxiliaryCube_translate]
    apply auxiliaryCube_aedisjoint hmpos
    exact hsep c.property c'.property (fun heq => hne (Subtype.ext heq))
  have hae := PeriodicVolume.replacement_ae_covers b
    (Thickening S0) (Thickening S1) (auxiliaryCube m 0) C C1
    hcount hfin (thickening_measurableSet S0) (thickening_measurableSet S1)
    (auxiliaryCube_measurableSet m 0) hvol hJvol hp ht htile hpack
  have haecubes : ∀ᵐ x ∂volume, ∃ c : C, x ∈ auxiliaryCube m c := by
    filter_upwards [hae] with x hx
    obtain ⟨c, hc⟩ := hx
    refine ⟨c, ?_⟩
    rw [← auxiliaryCube_translate]
    exact hc
  exact grid_coset_of_auxiliary_cover hmpos C (auxiliaryCube_locallyFinite m C hfin)
    (auxiliaryCube_cover_of_ae m C hfin haecubes) hnear

theorem periodic_voxel_assembly_grid_range
    {m : ℕ} (hm : 2 ≤ m) {S0 S1 S : Finset (Lattice 3)}
    (h0 : S ⊆ S0) (h1 : S ⊆ S1) (hdiff : RigidDifferences m S)
    (hcard0 : S0.card = m ^ 3) (hcard1 : S1.card = m ^ 3)
    {C C1 : Set (Space 3)}
    (b : Module.Basis (Fin 3) ℝ (Space 3))
    (hp : ∀ v ∈ latticeOfBasis b, Period C v)
    (ht : ∀ v ∈ latticeOfBasis b, Period C1 v)
    (htile : TypedAETiles (Thickening S0) (Thickening S1) C C1) :
    ∃ c₀ ∈ C, C = Set.range (fun z : Lattice 3 => c₀ + (m : ℝ) • castLattice z) := by
  obtain ⟨c₀, hc₀, heq⟩ := periodic_voxel_assembly_grid hm h0 h1 hdiff
    hcard0 hcard1 b hp ht htile
  refine ⟨c₀, hc₀, heq.trans ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := mem_scaledGrid.mp hx
    refine ⟨z, ?_⟩
    change c₀ + (m : ℝ) • castLattice z = x
    rw [hz, add_sub_cancel]
  · rintro ⟨z, rfl⟩
    apply mem_scaledGrid.mpr
    refine ⟨z, ?_⟩
    change (m : ℝ) • castLattice z = (c₀ + (m : ℝ) • castLattice z) - c₀
    exact (add_sub_cancel_left c₀ ((m : ℝ) • castLattice z)).symm

end PeriodicTilingThree

end

end OAI
