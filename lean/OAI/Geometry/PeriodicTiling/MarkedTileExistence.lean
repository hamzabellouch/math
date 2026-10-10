import OAI.Geometry.PeriodicTiling.MarkedTile
import OAI.Geometry.PeriodicTiling.CyclicQuotient

namespace OAI

namespace PeriodicTilingThree.MarkedTile

noncomputable section

def periodEquiv {B : Set (Lattice 3)} {w : Lattice 3} (hB : Period B w) : B ≃ B where
  toFun b := ⟨(b : Lattice 3) + w, (hB b).mpr b.property⟩
  invFun b := ⟨(b : Lattice 3) - w, by
    have h := (hB ((b : Lattice 3) - w)).mp
    apply h
    simp [b.property]⟩
  left_inv b := by
    apply Subtype.ext
    change ((b : Lattice 3) + w) - w = (b : Lattice 3)
    exact add_sub_cancel_right _ _
  right_inv b := by
    apply Subtype.ext
    change ((b : Lattice 3) - w) + w = (b : Lattice 3)
    exact sub_add_cancel _ _

@[simp] theorem periodEquiv_apply {B : Set (Lattice 3)} {w : Lattice 3}
    (hB : Period B w) (b : B) : (periodEquiv hB b : Lattice 3) = (b : Lattice 3) + w := rfl

@[simp] theorem periodEquiv_symm_apply {B : Set (Lattice 3)} {w : Lattice 3}
    (hB : Period B w) (b : B) : ((periodEquiv hB).symm b : Lattice 3) = (b : Lattice 3) - w := rfl

def relocate {m : ℕ} {U : Finset (Lattice 3)} {B : Set (Lattice 3)}
    {w : Lattice 3} (hB : Period B w) :
    ((↥U × B) × Residue m) ≃ ((↥U × B) × Residue m) where
  toFun q := if (q.1.1 : Lattice 3) = 0 ∧ q.2 = 0 then
    ((q.1.1, periodEquiv hB q.1.2), q.2) else q
  invFun q := if (q.1.1 : Lattice 3) = 0 ∧ q.2 = 0 then
    ((q.1.1, (periodEquiv hB).symm q.1.2), q.2) else q
  left_inv q := by
    rcases q with ⟨⟨u, b⟩, v⟩
    by_cases h : (u : Lattice 3) = 0 ∧ v = 0 <;> simp [h]
  right_inv q := by
    rcases q with ⟨⟨u, b⟩, v⟩
    by_cases h : (u : Lattice 3) = 0 ∧ v = 0 <;> simp [h]

namespace ResidueSection

variable {m : ℕ} [NeZero m] (s : ResidueSection m)

def baseline {U : Finset (Lattice 3)} {B : Set (Lattice 3)}
    (q : (↥U × B) × Residue m) : Lattice 3 :=
  scale m ((q.1.1 : Lattice 3) + (q.1.2 : Lattice 3)) + s.t q.2

theorem baseline_bijective {U : Finset (Lattice 3)} {B : Set (Lattice 3)}
    (h : Tiles U B) : Function.Bijective (s.baseline (U := U) (B := B)) := by
  constructor
  · rintro ⟨⟨u, b⟩, v⟩ ⟨⟨u', b'⟩, v'⟩ he
    have hc : ((u : Lattice 3) + (b : Lattice 3), v) =
        ((u' : Lattice 3) + (b' : Lattice 3), v') :=
      s.coordinates_injective he
    have hi : (u, b) = (u', b') := h.1 (congrArg Prod.fst hc)
    have hv : v = v' := congrArg (fun p : Lattice 3 × Residue m => p.2) hc
    exact Prod.ext hi hv
  · intro x
    obtain ⟨⟨a, v⟩, hx⟩ := s.coordinates_surjective x
    obtain ⟨⟨u, b⟩, ha⟩ := h.2 a
    refine ⟨((u, b), v), ?_⟩
    change scale m ((u : Lattice 3) + (b : Lattice 3)) + s.t v = x
    change (u : Lattice 3) + (b : Lattice 3) = a at ha
    rw [ha]
    exact hx

def placement {U : Finset (Lattice 3)} {B : Set (Lattice 3)}
    (w : Lattice 3) (q : (↥U × B) × Residue m) : Lattice 3 :=
  s.point w q.1.1 q.2 + scale m q.1.2

theorem placement_eq_baseline_relocate
    {m : ℕ} [NeZero m] (s : ResidueSection m)
    {U : Finset (Lattice 3)}
    {B : Set (Lattice 3)} {w : Lattice 3} (hB : Period B w)
    (q : (↥U × B) × Residue m) :
    s.placement w q = s.baseline (relocate hB q) := by
  classical
  rcases q with ⟨⟨u, b⟩, v⟩
  by_cases h : (u : Lattice 3) = 0 ∧ v = 0
  · simp only [placement, point, relocate, Equiv.coe_fn_mk, baseline,
      h.1, h.2, and_self, ite_true, periodEquiv_apply, zero_add, map_add, t0]
    abel
  · simp only [placement, point, h, ite_false, relocate, Equiv.coe_fn_mk, baseline,
      map_add]
    abel

theorem placement_bijective {U : Finset (Lattice 3)} {B : Set (Lattice 3)}
    {w : Lattice 3} (h : Tiles U B) (hB : Period B w) :
    Function.Bijective (s.placement (U := U) (B := B) w) := by
  have he : s.placement (U := U) (B := B) w = s.baseline ∘ relocate hB := by
    funext q
    exact s.placement_eq_baseline_relocate hB q
  rw [he]
  exact (s.baseline_bijective h).comp (relocate hB).bijective

theorem finalTile_tiles {U : Finset (Lattice 3)} {B : Set (Lattice 3)}
    {w : Lattice 3} (h : Tiles U B) (hB : Period B w) :
    Tiles (s.finalTile w U) ((scale m) '' B) := by
  classical
  have hp := s.placement_bijective h hB
  constructor
  · rintro ⟨⟨t, ht⟩, ⟨c, hc⟩⟩ ⟨⟨t', ht'⟩, ⟨c', hc'⟩⟩ he
    obtain ⟨u, hu, v, hv⟩ := s.mem_finalTile.mp ht
    obtain ⟨u', hu', v', hv'⟩ := s.mem_finalTile.mp ht'
    obtain ⟨b, hb, hbc⟩ := hc
    obtain ⟨b', hb', hbc'⟩ := hc'
    have hi : (((⟨u, hu⟩ : ↥U), (⟨b, hb⟩ : B)), v) =
        (((⟨u', hu'⟩ : ↥U), (⟨b', hb'⟩ : B)), v') := by
      apply hp.1
      change s.point w u v + scale m b = s.point w u' v' + scale m b'
      rw [hv, hv', hbc, hbc']
      exact he
    have htt : t = t' := by
      have hh := congrArg
        (fun q : (↥U × B) × Residue m => s.point w q.1.1 q.2) hi
      simpa only [hv, hv'] using hh
    have hcc : c = c' := by
      have hh := congrArg
        (fun q : (↥U × B) × Residue m => scale m q.1.2) hi
      simpa only [hbc, hbc'] using hh
    exact Prod.ext (Subtype.ext htt) (Subtype.ext hcc)
  · intro x
    obtain ⟨⟨⟨u, b⟩, v⟩, hx⟩ := hp.2 x
    refine ⟨(⟨s.point w u v, s.mem_finalTile.mpr ⟨u, u.property, v, rfl⟩⟩,
      ⟨scale m b, ⟨b, b.property, rfl⟩⟩), ?_⟩
    exact hx

theorem cyclic_finalTile_tiles (Q : ℕ) [NeZero Q]
    {F : Finset (CyclicQuotient.Group Q)} {A : Set (CyclicQuotient.Group Q)}
    (h : Tiles F A) :
    Tiles (s.finalTile (CyclicQuotient.kernelStep Q) (CyclicQuotient.representatives Q F))
      ((scale m) '' ((CyclicQuotient.projection Q) ⁻¹' A)) :=
  s.finalTile_tiles (CyclicQuotient.preimage_tiles Q h)
    (CyclicQuotient.period_preimage_kernelStep Q A)

end ResidueSection
end
end PeriodicTilingThree.MarkedTile

end OAI
