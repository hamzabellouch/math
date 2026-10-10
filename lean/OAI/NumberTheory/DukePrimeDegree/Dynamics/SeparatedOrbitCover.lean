import OAI.NumberTheory.DukePrimeDegree.Dynamics.CountableOrbitSection
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Separation.Hausdorff

namespace OAI

/-! # Countable separated covers for the diagonal-map section construction -/

noncomputable section
open Set MeasureTheory
namespace DukePrimeDegree

section Topology
variable {Y : Type*} [TopologicalSpace Y]

def finiteOrbitNeighbor (e : Y ≃ₜ Y) (N : ℕ) (x y : Y) : Prop :=
  x=y ∨ ∃ k : Fin N, (e^(k.val+1)) x=y ∨ (e^(k.val+1)) y=x

lemma finiteOrbitNeighbor_symm (e : Y ≃ₜ Y) (N : ℕ) :
    ∀ ⦃x y⦄, finiteOrbitNeighbor e N x y → finiteOrbitNeighbor e N y x := by
  intro x y h
  rcases h with h | ⟨k,h | h⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨k,Or.inr h⟩
  · exact Or.inr ⟨k,Or.inl h⟩

/-- The orbit relation is used only to say that the section meets each
orbit. Its finite-neighbor relation controls the measure of the section. -/
def homeomorphOrbitSetoid (e : Y ≃ₜ Y) : Setoid Y where
  r x y := ∃ k : ℤ, (e^k) x=y
  iseqv := {
    refl := fun x => ⟨0,by simp⟩
    symm := by
      rintro x y ⟨k,rfl⟩
      refine ⟨-k,?_⟩
      rw [←Homeomorph.mul_apply,←zpow_add]
      simp
    trans := by
      rintro x y z ⟨k,rfl⟩ ⟨l,rfl⟩
      refine ⟨l+k,?_⟩
      rw [zpow_add,Homeomorph.mul_apply] }

lemma finiteOrbitNeighbor_orbit (e : Y ≃ₜ Y) (N : ℕ) (x y : Y)
    (h : finiteOrbitNeighbor e N x y) : (homeomorphOrbitSetoid e).r x y := by
  rcases h with rfl | ⟨k,h | h⟩
  · exact (homeomorphOrbitSetoid e).refl x
  · exact ⟨(k.val+1:ℕ),by simpa only [zpow_natCast] using h⟩
  · apply (homeomorphOrbitSetoid e).symm
    exact ⟨(k.val+1:ℕ),by simpa only [zpow_natCast] using h⟩

lemma exists_open_finite_orbit_separated [T2Space Y] (e : Y ≃ₜ Y) (N : ℕ) (x : Y)
    (hfree : ∀ k : Fin N, (e^(k.val+1)) x ≠ x) :
    ∃ U : Set Y, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U, finiteOrbitNeighbor e N y z → y=z := by
  classical
  have hchoice (k : Fin N) := t2_separation (hfree k).symm
  choose U V hU hV hxU hxV hdis using hchoice
  let W := ⋂ k : Fin N, U k ∩ (e^(k.val+1)) ⁻¹' V k
  refine ⟨W,isOpen_iInter_of_finite (fun k =>
    (hU k).inter ((hV k).preimage (e^(k.val+1)).continuous)),?_,?_⟩
  · exact mem_iInter.mpr fun k => ⟨hxU k,hxV k⟩
  · intro y hy z hz h
    rcases h with h | ⟨k,h | h⟩
    · exact h
    · have hyk := mem_iInter.mp hy k
      have hzk := mem_iInter.mp hz k
      exact (Set.disjoint_left.mp (hdis k) hzk.1 (h ▸ hyk.2)).elim
    · have hyk := mem_iInter.mp hy k
      have hzk := mem_iInter.mp hz k
      exact (Set.disjoint_left.mp (hdis k) hyk.1 (h ▸ hzk.2)).elim

end Topology

section Measurable
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]

omit [T2Space Y] [SecondCountableTopology Y] in
lemma measurableSet_finiteOrbitNeighbor (e : Y ≃ₜ Y) (N : ℕ)
    {C : Set Y} (hC : MeasurableSet C) :
    MeasurableSet {x | ∃ y ∈ C, finiteOrbitNeighbor e N x y} := by
  have he : {x | ∃ y ∈ C, finiteOrbitNeighbor e N x y} =
      C ∪ ⋃ k : Fin N, ((e^(k.val+1)) ⁻¹' C ∪ (e^(k.val+1)) '' C) := by
    ext x
    constructor
    · rintro ⟨y,hy,h | ⟨k,h | h⟩⟩
      · exact Or.inl (h.symm ▸ hy)
      · exact Or.inr (mem_iUnion.mpr ⟨k,Or.inl (show (e^(k.val+1)) x ∈ C from h.symm ▸ hy)⟩)
      · exact Or.inr (mem_iUnion.mpr ⟨k,Or.inr ⟨y,hy,h⟩⟩)
    · rintro (hx | hx)
      · exact ⟨x,hx,Or.inl rfl⟩
      · obtain ⟨k,hk | hk⟩ := mem_iUnion.mp hx
        · exact ⟨(e^(k.val+1)) x,hk,Or.inr ⟨k,Or.inl rfl⟩⟩
        · obtain ⟨y,hy,he⟩ := hk
          exact ⟨y,hy,Or.inr ⟨k,Or.inr he⟩⟩
  rw [he]
  exact hC.union (MeasurableSet.iUnion fun k =>
    (hC.preimage (e^(k.val+1)).measurable).union
      ((e^(k.val+1)).measurableEmbedding.measurableSet_image.mpr hC))

/-- A countable separated cover exists inside any measurable set with
no short periodic points. The set need not be invariant or ergodic. -/
theorem exists_countable_finite_orbit_cover (e : Y ≃ₜ Y) (N : ℕ)
    {A : Set Y} (hA : MeasurableSet A)
    (hfree : ∀ x ∈ A, ∀ k : Fin N, (e^(k.val+1)) x ≠ x) :
    ∃ C : ℕ → Set Y, (∀ n, MeasurableSet (C n)) ∧ (⋃ n, C n)=A ∧
      ∀ n, ∀ x ∈ C n, ∀ y ∈ C n, finiteOrbitNeighbor e N x y → x=y := by
  classical
  by_cases hne : A.Nonempty
  · have : Nonempty A := hne.to_subtype
    choose U hU hxU hsep using fun x : A =>
      exists_open_finite_orbit_separated e N x.val (hfree x.val x.property)
    obtain ⟨f,hf⟩ := (HereditarilyLindelofSpace.isLindelof A).indexed_countable_subcover
      U hU (by
        intro x hx
        exact mem_iUnion.mpr ⟨⟨x,hx⟩,hxU ⟨x,hx⟩⟩)
    refine ⟨fun n => A ∩ U (f n),fun n => hA.inter (hU _).measurableSet,?_,?_⟩
    · ext x
      constructor
      · intro hx
        obtain ⟨n,hn⟩ := mem_iUnion.mp hx
        exact hn.1
      · intro hx
        obtain ⟨n,hn⟩ := mem_iUnion.mp (hf hx)
        exact mem_iUnion.mpr ⟨n,hx,hn⟩
    · intro n x hx y hy hxy
      exact hsep (f n) x hx.2 y hy.2 hxy
  · have hzero : A=∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst A
    exact ⟨fun _ => ∅,fun _ => MeasurableSet.empty,by simp,
      fun _ _ hx => hx.elim⟩

/-- A measurable separated section meets every orbit represented in A. -/
theorem exists_finite_orbit_section (e : Y ≃ₜ Y) (N : ℕ)
    {A : Set Y} (hA : MeasurableSet A)
    (hfree : ∀ x ∈ A, ∀ k : Fin N, (e^(k.val+1)) x ≠ x) :
    ∃ S : Set Y, MeasurableSet S ∧ S ⊆ A ∧
      (∀ x ∈ S, ∀ y ∈ S, finiteOrbitNeighbor e N x y → x=y) ∧
      ∀ x ∈ A, ∃ y ∈ S, (homeomorphOrbitSetoid e).r x y := by
  obtain ⟨C,hC,hcover,hsep⟩ := exists_countable_finite_orbit_cover e N hA hfree
  obtain ⟨S,hS,hSA,hind,hmeet⟩ := exists_measurable_orbit_section
    (homeomorphOrbitSetoid e) (finiteOrbitNeighbor e N) (finiteOrbitNeighbor_symm e N)
    (finiteOrbitNeighbor_orbit e N) C hC
    (fun n => measurableSet_finiteOrbitNeighbor e N (hC n)) hsep
  exact ⟨S,hS,by rwa [hcover] at hSA,hind,by rwa [hcover] at hmeet⟩

end Measurable
end DukePrimeDegree

end

end OAI
