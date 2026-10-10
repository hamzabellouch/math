import OAI.Geometry.PeriodicTiling.WeakPeriodicity
import OAI.Geometry.PeriodicTiling.PeriodicPartGrouping
import OAI.Geometry.PeriodicTiling.ComponentTargets
import OAI.Geometry.PeriodicTiling.PeriodicRegion

namespace OAI

universe uG uι

noncomputable section

namespace PeriodicTilingThree

open scoped BigOperators Classical

theorem Tiles.image_add {G : Type uG} [AddCommGroup G]
    {F : Finset G} {A : Set G} (h : Tiles F A) (u : G) :
    Tiles (F.image (fun f => f + u)) A := by
  classical
  apply tiles_iff_unique_tile.mpr
  intro x
  obtain ⟨f, hf, huniq⟩ := tiles_iff_unique_tile.mp h (x - u)
  let f' : ↥(F.image (fun f => f + u)) :=
    ⟨(f : G) + u, Finset.mem_image_of_mem _ f.property⟩
  have hsub (g : G) : x - (g + u) = (x - u) - g := by abel
  refine ⟨f', ?_, ?_⟩
  · change x - ((f : G) + u) ∈ A
    rwa [hsub]
  · intro g hg
    obtain ⟨z, hz, hzg⟩ := Finset.mem_image.mp g.property
    have hzA : (x - u) - z ∈ A := by
      rw [← hsub, hzg]
      exact hg
    have hzf : (⟨z, hz⟩ : ↥F) = f := huniq ⟨z, hz⟩ hzA
    apply Subtype.ext
    change (g : G) = (f : G) + u
    have hzf' : z = (f : G) := congrArg Subtype.val hzf
    rw [← hzg, hzf']

theorem fullyPeriodic_finite_union {G : Type uG} {ι : Type uι} [AddCommGroup G] [Finite ι]
    (parts : ι → Set G) (hp : ∀ i, FullyPeriodic (parts i)) :
    FullyPeriodic {x | ∃ i, x ∈ parts i} := by
  classical
  choose P hindex hperiod using hp
  let common : AddSubgroup G := ⨅ i, P i
  refine ⟨common, AddSubgroup.finiteIndex_iInf hindex, ?_⟩
  intro v hv x
  have hv' (i : ι) : v ∈ P i := (AddSubgroup.mem_iInf.mp hv) i
  change (∃ i, x + v ∈ parts i) ↔ ∃ i, x ∈ parts i
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (hperiod i v (hv' i) x).mp hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (hperiod i v (hv' i) x).mpr hi⟩

theorem tiles_union_of_region_partition {G : Type uG} {ι : Type uι} [AddCommGroup G]
    (F : Finset G) (parts targets : ι → Set G)
    (htile : ∀ i, TilesRegion F (parts i) (targets i))
    (hcover : ∀ x, ∃! i, x ∈ targets i) :
    Tiles F {x | ∃ i, x ∈ parts i} := by
  apply tiles_iff_unique_tile.mpr
  intro x
  obtain ⟨i, hi, huniq⟩ := hcover x
  obtain ⟨f, hf, hfuniq⟩ := (htile i).unique x hi
  refine ⟨f, ⟨i, hf⟩, ?_⟩
  rintro g ⟨j, hj⟩
  have hxj : x ∈ targets j := by
    simpa [add_comm] using (htile j).add_mem g g.property (x - g) hj
  have hji : j = i := huniq j hxj
  subst j
  exact hfuniq g hj

theorem Tiles.fullyPeriodic_of_finite_periodic_partition
    {ι : Type uι} [Fintype ι] {F : Finset Plane} {A : Set Plane}
    (h : Tiles F A) (parts : ι → Set Plane) (v : ι → Plane)
    (hpartition : ∀ x, (∑ i, tileIndicator ℝ (parts i) x) = tileIndicator ℝ A x)
    (hv : ∀ i, v i ≠ 0) (hperiod : ∀ i, Period (parts i) (v i)) :
    ∃ B : Set Plane, Tiles F B ∧ FullyPeriodic B := by
  classical
  obtain ⟨m, w, grouped, hw, htrans, hsum, hp⟩ :=
    exists_grouped_periodic_parts parts v hv hperiod hpartition
  obtain ⟨htiles, hcover, htargets⟩ := component_targets grouped w h hsum hw hp htrans
  have hex (j : Fin m) : ∃ B : Set Plane,
      TilesRegion F B (componentTarget F (grouped j)) ∧ FullyPeriodic B :=
    periodic_region_replacement (htiles j) ⟨w j, hw j, hp j⟩ (htargets j)
  choose replacements hregion hfull using hex
  refine ⟨{x | ∃ j, x ∈ replacements j}, ?_, ?_⟩
  · exact tiles_union_of_region_partition F replacements
      (fun j => componentTarget F (grouped j)) hregion hcover
  · exact fullyPeriodic_finite_union replacements hfull

theorem plane_tile_has_fullyPeriodic_complement
    (F : Finset Plane) (hF : F.Nonempty)
    (h : ∃ A : Set Plane, Tiles F A) :
    ∃ B : Set Plane, Tiles F B ∧ FullyPeriodic B := by
  classical
  obtain ⟨A, hA⟩ := h
  obtain ⟨f, hf⟩ := hF
  let : DecidableEq Plane := fun a b => Classical.propDecidable (a = b)
  let F₀ := F.image (fun x => x + -f)
  have hzero : (0 : Plane) ∈ F₀ := by
    apply Finset.mem_image.mpr
    exact ⟨f, hf, add_neg_cancel f⟩
  have hA₀ : Tiles F₀ A := hA.image_add (-f)
  obtain ⟨m, parts, v, hpartition, hv, hp⟩ := hA₀.exists_weak_periodic_partition hzero
  obtain ⟨B, hB, hfull⟩ :=
    hA₀.fullyPeriodic_of_finite_periodic_partition parts v hpartition hv hp
  refine ⟨B, ?_, hfull⟩
  have hback := hB.image_add f
  simpa only [F₀, Finset.image_image, Function.comp_def, add_assoc,
    neg_add_cancel, add_zero, Finset.image_id'] using hback

end PeriodicTilingThree

end

end OAI
