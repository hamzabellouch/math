import OAI.Geometry.PeriodicTiling.ConstituentGeometry
import OAI.Geometry.PeriodicTiling.AETilingCountable

namespace OAI

noncomputable section

namespace PeriodicTilingThree.MarkedTile

open Set MeasureTheory Filter

namespace ResidueSection

variable {m : ℕ} [NeZero m] (s : ResidueSection m)

theorem translated_parts_unique_ae {w : Lattice 3} {U : Finset (Lattice 3)}
    (hw : w ∉ U) (a : Space 3) (u u' : ↥U) :
    ∀ᵐ x ∂volume,
      x - center m a u ∈ Thickening (s.constituent w u) →
      x - center m a u' ∈ Thickening (s.constituent w u') → u = u' := by
  classical
  by_cases he : u = u'
  · exact Eventually.of_forall (fun _ _ _ => he)
  · have hnull := thickening_inter_measure_zero_of_disjoint (s.parts_disjoint hw he)
    have havoid : ∀ᵐ x ∂volume,
        x ∉ Thickening (s.part w u) ∩ Thickening (s.part w u') :=
      compl_mem_ae_iff.mpr hnull
    have hshift := (measurePreserving_sub_right volume a).quasiMeasurePreserving.ae havoid
    filter_upwards [hshift] with x hx
    intro hu hu'
    exact False.elim (hx ⟨s.mem_translated_part.mpr hu,
      s.mem_translated_part.mpr hu'⟩)

theorem indexed_constituents_ae {w : Lattice 3} {U : Finset (Lattice 3)}
    (h0 : 0 ∈ U) (hw : w ∉ U) {A : Set (Space 3)}
    (htile : AETiles (Thickening (s.finalTile w U)) A) :
    ∀ᵐ x ∂volume, ∃! q : A × ↥U,
      x - center m q.1 q.2 ∈ Thickening (s.constituent w q.2) := by
  classical
  have hcount := htile.countable_of_thickening (s.finalTile_nonempty w h0)
  let : Countable A := hcount.to_subtype
  have hall : ∀ᵐ x ∂volume, ∀ (a : A) (u u' : ↥U),
      x - center m a u ∈ Thickening (s.constituent w u) →
      x - center m a u' ∈ Thickening (s.constituent w u') → u = u' := by
    apply ae_all_iff.mpr
    intro a
    apply ae_all_iff.mpr
    intro u
    apply ae_all_iff.mpr
    intro u'
    exact s.translated_parts_unique_ae hw a u u'
  filter_upwards [htile, hall] with x hx hpieces
  obtain ⟨a, ha, haunique⟩ := hx
  obtain ⟨u, hu⟩ := s.mem_translated_finalTile.mp ha
  refine ⟨(a, u), hu, ?_⟩
  rintro ⟨a', u'⟩ hq
  have ha' : a' = a := haunique a' (s.mem_translated_finalTile.mpr ⟨u', hq⟩)
  subst a'
  exact Prod.ext rfl (hpieces a u' u hq hu)

theorem center_injective {w : Lattice 3} {U : Finset (Lattice 3)}
    (hm : 2 ≤ m) (h0 : 0 ∈ U) (hw : w ∉ U) {A : Set (Space 3)}
    (htile : AETiles (Thickening (s.finalTile w U)) A) :
    Function.Injective (fun q : A × ↥U => center m q.1 q.2) := by
  classical
  have hcover := s.indexed_constituents_ae h0 hw htile
  obtain ⟨t, ht⟩ := s.Tstar_nonempty hm
  intro q q' he
  by_contra hne
  have hnull : volume (unitVoxel (center m q.1 q.2 + castLattice t)) = 0 := by
    apply measure_mono_null ?_ (ae_iff.mp hcover)
    intro x hx huniq
    obtain ⟨r, _hr, hruniq⟩ := huniq
    have hq : x - center m q.1 q.2 ∈ Thickening (s.constituent w q.2) :=
      s.common_voxel_subset_constituent w q.2 q.1 ht hx
    have hq' : x - center m q'.1 q'.2 ∈ Thickening (s.constituent w q'.2) := by
      apply s.common_voxel_subset_constituent w q'.2 q'.1 ht
      simpa only [he] using hx
    exact hne ((hruniq q hq).trans (hruniq q' hq').symm)
  rw [unitVoxel_volume] at hnull
  exact one_ne_zero hnull

theorem center_mem_A_iff
    {m : ℕ} [NeZero m]
    {U : Finset (Lattice 3)} (h0 : 0 ∈ U)
    {A : Set (Space 3)}
    (hinj : Function.Injective (fun q : A × ↥U => center m q.1 q.2))
    (q : A × ↥U) : center m q.1 q.2 ∈ A ↔ (q.2 : Lattice 3) = 0 := by
  constructor
  · intro hc
    have he : q = ((⟨center m q.1 q.2, hc⟩ : A), (⟨0, h0⟩ : ↥U)) := by
      apply hinj
      simp
    exact congrArg (fun p : A × ↥U => (p.2 : Lattice 3)) he
  · intro hu
    simpa only [hu, center_zero] using q.1.property

open scoped Classical in
theorem constituent_type_eq {w : Lattice 3} {U : Finset (Lattice 3)} (h0 : 0 ∈ U)
    {A : Set (Space 3)}
    (hinj : Function.Injective (fun q : A × ↥U => center m q.1 q.2))
    (q : A × ↥U) :
    (if center m q.1 q.2 ∈ A then Thickening (s.T1 w) else Thickening s.T0) =
      Thickening (s.constituent w q.2) := by
  classical
  by_cases hu : (q.2 : Lattice 3) = 0
  · rw [ite_eq_left ((center_mem_A_iff h0 hinj q).mpr hu)]
    simp only [constituent, ite_eq_left hu]
  · have hc : center m q.1 q.2 ∉ A := fun h => hu ((center_mem_A_iff h0 hinj q).mp h)
    simp only [hc, ite_false, constituent, hu]

theorem typed_constituents {w : Lattice 3} {U : Finset (Lattice 3)}
    (hm : 2 ≤ m) (h0 : 0 ∈ U) (hw : w ∉ U) {A : Set (Space 3)}
    (htile : AETiles (Thickening (s.finalTile w U)) A) :
    TypedAETiles (Thickening s.T0) (Thickening (s.T1 w)) (centers m U A) A := by
  classical
  have hinj := s.center_injective hm h0 hw htile
  have hcover := s.indexed_constituents_ae h0 hw htile
  filter_upwards [hcover] with x hx
  obtain ⟨q, hq, hqunique⟩ := hx
  let c : centers m U A := ⟨center m q.1 q.2, ⟨q, rfl⟩⟩
  refine ⟨c, ?_, ?_⟩
  · change x - center m q.1 q.2 ∈
      if center m q.1 q.2 ∈ A then Thickening (s.T1 w) else Thickening s.T0
    rw [s.constituent_type_eq h0 hinj q]
    exact hq
  · intro c' hc'
    obtain ⟨q', he⟩ := c'.property
    change center m q'.1 q'.2 = (c' : Space 3) at he
    have hq' : x - center m q'.1 q'.2 ∈ Thickening (s.constituent w q'.2) := by
      rw [← s.constituent_type_eq h0 hinj q', he]
      exact hc'
    have hqq := hqunique q' hq'
    apply Subtype.ext
    change (c' : Space 3) = center m q.1 q.2
    rw [← he, hqq]

end ResidueSection

theorem period_centers {m : ℕ} {U : Finset (Lattice 3)} {A : Set (Space 3)}
    {v : Space 3} (hA : Period A v) : Period (centers m U A) v := by
  intro c
  constructor
  · intro hc
    obtain ⟨a, ha, u, hu, he⟩ := mem_centers.mp hc
    have hav : a - v ∈ A := (hA (a - v)).mp (by simpa using ha)
    refine mem_centers.mpr ⟨a - v, hav, u, hu, ?_⟩
    calc
      center m (a - v) u = center m a u - v := by unfold center; abel
      _ = c := by rw [he]; abel
  · intro hc
    obtain ⟨a, ha, u, hu, he⟩ := mem_centers.mp hc
    refine mem_centers.mpr ⟨a + v, (hA a).mpr ha, u, hu, ?_⟩
    calc
      center m (a + v) u = center m a u + v := by unfold center; abel
      _ = c + v := by rw [he]

theorem fullyPeriodic_centers {m : ℕ} {U : Finset (Lattice 3)} {A : Set (Space 3)}
    (hA : EuclideanFullyPeriodic A) : EuclideanFullyPeriodic (centers m U A) := by
  obtain ⟨b, hb⟩ := hA
  exact ⟨b, fun v hv => period_centers (hb v hv)⟩

theorem tiles_of_centers_grid {m : ℕ} {U : Finset (Lattice 3)} {A : Set (Space 3)}
    {c0 : Space 3}
    (hinj : Function.Injective (fun q : A × ↥U => center m q.1 q.2))
    (hgrid : centers m U A = Set.range (fun z : Lattice 3 => c0 + scaledCast m z)) :
    Tiles U {z : Lattice 3 | c0 + scaledCast m z ∈ A} := by
  classical
  rw [tiles_iff_unique_tile]
  intro z
  have hz : c0 + scaledCast m z ∈ centers m U A := by
    rw [hgrid]
    exact ⟨z, rfl⟩
  obtain ⟨q, hq⟩ := hz
  have hd : c0 + scaledCast m (z - (q.2 : Lattice 3)) = (q.1 : Space 3) := by
    have he : (q.1 : Space 3) + scaledCast m (q.2 : Lattice 3) =
        c0 + scaledCast m z := hq
    rw [map_sub]
    calc
      c0 + (scaledCast m z - scaledCast m (q.2 : Lattice 3)) =
          (c0 + scaledCast m z) - scaledCast m (q.2 : Lattice 3) := by abel
      _ = (q.1 : Space 3) := by rw [← he]; abel
  refine ⟨q.2, ?_, ?_⟩
  · change c0 + scaledCast m (z - (q.2 : Lattice 3)) ∈ A
    rw [hd]
    exact q.1.property
  · intro u hu
    let a : A := ⟨c0 + scaledCast m (z - (u : Lattice 3)), hu⟩
    have hc : center m a u = c0 + scaledCast m z := by
      change (c0 + scaledCast m (z - (u : Lattice 3))) + scaledCast m u = _
      rw [map_sub]
      abel
    have he : (a, u) = q := hinj (hc.trans hq.symm)
    exact congrArg Prod.snd he

end PeriodicTilingThree.MarkedTile

end

end OAI
