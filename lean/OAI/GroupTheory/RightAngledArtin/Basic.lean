import Mathlib.Tactic
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Finiteness
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea
/-- The defining commutators of the right-angled Artin group. -/
def artinRelations {V : Type*} (L : SimpleGraph V) : Set (FreeGroup V) :=
  {w | ∃ q r, L.Adj q r ∧
    w = FreeGroup.of q * FreeGroup.of r * (FreeGroup.of q)⁻¹ * (FreeGroup.of r)⁻¹}

abbrev ArtinGroup {V : Type*} (L : SimpleGraph V) := PresentedGroup (artinRelations L)

/-- Every standard generator has integral height one. -/
def height {V : Type*} (L : SimpleGraph V) : ArtinGroup L →* Multiplicative ℤ :=
  PresentedGroup.toGroup (f := fun _ : V => Multiplicative.ofAdd (1 : ℤ)) (by
    rintro w ⟨q, r, _, rfl⟩
    simp)


end EilenbergGanea

namespace EilenbergGanea


section FiniteGeneration
variable {V : Type*} (L : SimpleGraph V)

abbrev artinGenerator (v : V) : ArtinGroup L := PresentedGroup.of v

@[simp] theorem height_generator (v : V) :
    height L (artinGenerator L v) = Multiplicative.ofAdd (1 : ℤ) := by
  simp [height, artinGenerator]

theorem adjacent_generators_commute {v w : V} (h : L.Adj v w) :
    Commute (artinGenerator L v) (artinGenerator L w) := by
  have he := PresentedGroup.one_of_mem (rels := artinRelations L)
    (x := FreeGroup.of v * FreeGroup.of w * (FreeGroup.of v)⁻¹ * (FreeGroup.of w)⁻¹)
    ⟨v, w, h, rfl⟩
  simp only [map_mul, map_inv] at he
  change artinGenerator L v * artinGenerator L w =
    artinGenerator L w * artinGenerator L v
  apply mul_inv_eq_one.mp
  simpa only [artinGenerator, PresentedGroup.of, mul_inv_rev, mul_assoc] using he

def edgeDifferences : Set (ArtinGroup L) :=
  {x | ∃ v w, L.Adj v w ∧ x = artinGenerator L v * (artinGenerator L w)⁻¹}

def edgeGenerated : Subgroup (ArtinGroup L) := Subgroup.closure (edgeDifferences L)

theorem edge_difference_mem {v w : V} (h : L.Adj v w) :
    artinGenerator L v * (artinGenerator L w)⁻¹ ∈ edgeGenerated L :=
  Subgroup.subset_closure ⟨v, w, h, rfl⟩

theorem reachable_difference_mem {v w : V} (h : L.Reachable v w) :
    artinGenerator L v * (artinGenerator L w)⁻¹ ∈ edgeGenerated L := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
    simpa only [mul_assoc, inv_mul_cancel_left] using
      (edgeGenerated L).mul_mem (edge_difference_mem L huv) ih

theorem reachable_inv_difference_mem {v w : V} (h : L.Reachable v w) :
    (artinGenerator L v)⁻¹ * artinGenerator L w ∈ edgeGenerated L := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
    have hc := (adjacent_generators_commute L huv).inv_left
    have he : (artinGenerator L u)⁻¹ * artinGenerator L v ∈ edgeGenerated L := by
      rw [hc.eq]
      exact edge_difference_mem L huv.symm
    simpa only [mul_assoc, mul_inv_cancel_left] using (edgeGenerated L).mul_mem he ih


/-- A group-theoretic conjugation identity used with edge differences. -/
theorem conjugate_mem_of_difference {A : Type*} [Group A] (K : Subgroup A)
    {g a e : A} (hga : g * a⁻¹ ∈ K) (he : e ∈ K) (ha : Commute a e) :
    g * e * g⁻¹ ∈ K := by
  have hm := K.mul_mem (K.mul_mem hga he) (K.inv_mem hga)
  have hi : (g * a⁻¹) * e * (g * a⁻¹)⁻¹ = g * e * g⁻¹ := by
    calc
      (g * a⁻¹) * e * (g * a⁻¹)⁻¹ = g * (a⁻¹ * e * a) * g⁻¹ := by group
      _ = g * e * g⁻¹ := by rw [ha.inv_left.eq]; simp [mul_assoc]
  rwa [hi] at hm

theorem generator_conjugate_mem (hconn : L.Preconnected) (v : V)
    {x : ArtinGroup L} (hx : x ∈ edgeGenerated L) :
    artinGenerator L v * x * (artinGenerator L v)⁻¹ ∈ edgeGenerated L := by
  have hh : edgeGenerated L ≤ (edgeGenerated L).comap (MulAut.conj (artinGenerator L v)) := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨b, c, hbc, rfl⟩
    exact conjugate_mem_of_difference (edgeGenerated L)
      (reachable_difference_mem L (hconn v b)) (edge_difference_mem L hbc)
      ((Commute.refl _).mul_right (adjacent_generators_commute L hbc).inv_right)
  exact hh hx

theorem generator_inv_conjugate_mem (hconn : L.Preconnected) (v : V)
    {x : ArtinGroup L} (hx : x ∈ edgeGenerated L) :
    (artinGenerator L v)⁻¹ * x * artinGenerator L v ∈ edgeGenerated L := by
  have hh : edgeGenerated L ≤
      (edgeGenerated L).comap (MulAut.conj ((artinGenerator L v)⁻¹)) := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨b, c, hbc, rfl⟩
    change (artinGenerator L v)⁻¹ * (artinGenerator L b * (artinGenerator L c)⁻¹) *
      ((artinGenerator L v)⁻¹)⁻¹ ∈ edgeGenerated L
    apply conjugate_mem_of_difference (edgeGenerated L) (a := (artinGenerator L b)⁻¹)
    · simpa using reachable_inv_difference_mem L (hconn v b)
    · exact edge_difference_mem L hbc
    · exact ((Commute.refl _).mul_right
        (adjacent_generators_commute L hbc).inv_right).inv_left
  simpa using hh hx

theorem edgeGenerated_normal (hconn : L.Preconnected) : (edgeGenerated L).Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply (Subgroup.eq_top_iff' _).mpr
  apply PresentedGroup.generated_by
  intro v
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact generator_conjugate_mem L hconn v
  · intro hx
    simpa [mul_assoc] using generator_inv_conjugate_mem L hconn v hx

/-- For a connected defining graph, edge differences generate the full height kernel. -/
theorem edgeGenerated_eq_height_kernel (hconn : L.Preconnected) (v₀ : V) :
    edgeGenerated L = (height L).ker := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨v, w, _, rfl⟩
    simp [MonoidHom.mem_ker]
  · let _ := edgeGenerated_normal L hconn
    let q := QuotientGroup.mk' (edgeGenerated L)
    let z := zpowersHom _ (q (artinGenerator L v₀))
    have hq : q = z.comp (height L) := by
      apply PresentedGroup.ext
      intro v
      change q (artinGenerator L v) = z (height L (artinGenerator L v))
      rw [height_generator]
      change q (artinGenerator L v) = q (artinGenerator L v₀) ^ (1 : ℤ)
      rw [zpow_one]
      apply mul_inv_eq_one.mp
      rw [← map_inv, ← map_mul]
      exact (QuotientGroup.eq_one_iff _).mpr (reachable_difference_mem L (hconn v v₀))
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    change q x = 1
    rw [hq, MonoidHom.comp_apply, (MonoidHom.mem_ker.mp hx), map_one]

theorem height_kernel_fg [Finite V] (hconn : L.Preconnected) (v₀ : V) :
    Group.FG (height L).ker := by
  rw [Group.fg_iff_subgroup_fg, ← edgeGenerated_eq_height_kernel L hconn v₀]
  apply (Subgroup.fg_iff _).mpr
  refine ⟨edgeDifferences L, rfl, ?_⟩
  apply Set.Finite.subset
    (Set.finite_range (fun p : V × V => artinGenerator L p.1 * (artinGenerator L p.2)⁻¹))
  rintro x ⟨v, w, _, rfl⟩
  exact ⟨(v, w), rfl⟩

end FiniteGeneration

end EilenbergGanea

end

end OAI
