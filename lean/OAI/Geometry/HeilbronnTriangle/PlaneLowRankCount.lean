import OAI.Geometry.HeilbronnTriangle.FiniteIndexPlane
import OAI.Geometry.HeilbronnTriangle.PlaneTripleCount
import OAI.Geometry.HeilbronnTriangle.PlaneLineMatrices

namespace OAI


noncomputable section

open scoped LinearAlgebra.Projectivization

namespace Problem355.PlaneLowRankCount

variable {K V E : Type*} [Field K] [Finite K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def lineSublattice (L : Submodule ℤ E) (f : L →+ V) (p : ℙ K V) : Submodule ℤ E :=
  ((p.submodule.toAddSubgroup.comap f).toIntSubmodule).map L.subtype

omit [Finite K] [FiniteDimensional K V] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem lineSublattice_le (L : Submodule ℤ E) (f : L →+ V) (p : ℙ K V) :
    lineSublattice L f p ≤ L := Submodule.map_subtype_le _ _

omit [Finite K] [FiniteDimensional K V] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem mem_lineSublattice (L : Submodule ℤ E) (f : L →+ V)
    (p : ℙ K V) (u : L) :
    (u : E) ∈ lineSublattice L f p ↔ f u ∈ p.submodule := by
  change (u : E) ∈ ((p.submodule.toAddSubgroup.comap f).toIntSubmodule).map L.subtype ↔ _
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨v, hv, he⟩
    have h : v = u := Subtype.ext he
    subst v
    exact hv
  · intro hu
    exact ⟨u, hu, rfl⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
theorem lineSublattice_index (hV : Module.finrank K V = 2)
    (L : Submodule ℤ E) (f : L →+ V) (hf : Function.Surjective f) (p : ℙ K V) :
    (lineSublattice L f p).toAddSubgroup.relIndex L.toAddSubgroup = Nat.card K := by
  have he : (lineSublattice L f p).toAddSubgroup.addSubgroupOf L.toAddSubgroup =
      p.submodule.toAddSubgroup.comap f := by
    ext u
    exact mem_lineSublattice L f p u
  change ((lineSublattice L f p).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index = _
  rw [he]
  exact PlaneLines.line_preimage_index hV f hf p

theorem card_line_piece_le (hE : Module.finrank ℝ E = 2)
    (hV : Module.finrank K V = 2)
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : L →+ V) (hf : Function.Surjective f)
    (T : Finset (Fin 3 → L)) (R : ℝ) (hR : 0 ≤ R)
    (hnorm : ∀ u ∈ T, ∀ i, ‖(u i : E)‖ ≤ R)
    (hspan : ∀ u ∈ T, Submodule.span ℝ (Set.range (fun i => (u i : E))) = ⊤)
    (p : ℙ K V) :
    ((PlaneLineMatrices.familyPiece T (fun u i => f (u i)) p).card : ℝ) ≤
      (9 * Real.pi * R ^ 2 / ((Nat.card K : ℝ) * ZLattice.covolume L)) ^ 3 := by
  classical
  let Γ := lineSublattice L f p
  have hΓ : Γ ≤ L := lineSublattice_le L f p
  have hindex : Γ.toAddSubgroup.relIndex L.toAddSubgroup = Nat.card K :=
    lineSublattice_index hV L f hf p
  let : DiscreteTopology Γ := FiniteIndexPlane.discrete_of_le Γ L hΓ
  let : IsZLattice ℝ Γ := FiniteIndexPlane.isZLattice_of_relIndex_ne_zero Γ L
    (by rw [hindex]; exact Nat.card_pos.ne')
  let S := PlaneLineMatrices.familyPiece T (fun u i => f (u i)) p
  have hS (u : {u // u ∈ S}) : u.1 ∈ T ∧ ∀ i, f (u.1 i) ∈ p.submodule := by
    simpa only [S, PlaneLineMatrices.familyPiece, Finset.mem_filter] using u.2
  have hmem (u : {u // u ∈ S}) (i : Fin 3) : (u.1 i : E) ∈ Γ := by
    apply (mem_lineSublattice L f p (u.1 i)).mpr
    exact (hS u).2 i
  let g : {u // u ∈ S} → Fin 3 → Γ := fun u i => ⟨(u.1 i : E), hmem u i⟩
  have hg : Function.Injective g := by
    intro u v huv
    apply Subtype.ext
    funext i
    apply Subtype.ext
    exact congrArg (fun a : Fin 3 → Γ => (a i : E)) huv
  let U := S.attach.image g
  have hcard : U.card = S.card :=
    (Finset.card_image_of_injective _ hg).trans Finset.card_attach
  have hcount := PlaneTripleCount.card_spanning_triples_le Γ hE U R hR
    (by
      intro u hu i
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hu
      exact hnorm v.1 (hS v).1 i)
    (by
      intro u hu
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hu
      exact hspan v.1 (hS v).1)
  rw [hcard, FiniteIndexPlane.covolume_eq_index_mul Γ L hΓ, hindex] at hcount
  exact hcount

theorem card_low_rank_le (hE : Module.finrank ℝ E = 2)
    (hV : Module.finrank K V = 2)
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : L →+ V) (hf : Function.Surjective f)
    (T : Finset (Fin 3 → L)) (R : ℝ) (hR : 0 ≤ R)
    (hnorm : ∀ u ∈ T, ∀ i, ‖(u i : E)‖ ≤ R)
    (hspan : ∀ u ∈ T, Submodule.span ℝ (Set.range (fun i => (u i : E))) = ⊤)
    (hlow : ∀ u ∈ T, Module.finrank K
      (Submodule.span K (Set.range (fun i => f (u i)))) ≤ 1) :
    (T.card : ℝ) ≤ ((Nat.card K : ℝ) + 1) *
      (9 * Real.pi * R ^ 2 / ((Nat.card K : ℝ) * ZLattice.covolume L)) ^ 3 := by
  exact PlaneLineMatrices.card_family_le_lines_mul_real hV T (fun u i => f (u i)) _
    hlow (card_line_piece_le hE hV L f hf T R hR hnorm hspan)

end Problem355.PlaneLowRankCount

end

end OAI
