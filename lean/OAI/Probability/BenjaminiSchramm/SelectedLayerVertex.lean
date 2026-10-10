import OAI.Probability.BenjaminiSchramm.LayerFreshSelection
import OAI.Probability.BenjaminiSchramm.SlabHit

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Encodable V] (G : BondGraph V E)

def firstLayerHitAt (I : Set E) (x : V) (A : Set V) (z : V) : Set (Set E) :=
  {ω | Conn G (ω ∩ I) x z ∧ z ∈ A ∧ ∀ w ∈ A,
    Conn G (ω ∩ I) x w → Encodable.encode z ≤ Encodable.encode w}

lemma firstLayerHitAt_pairwise (I : Set E) (x : V) (A : Set V) :
    Pairwise (fun u v => Disjoint (firstLayerHitAt G I x A u) (firstLayerHitAt G I x A v)) := by
  intro u v huv
  apply Set.disjoint_left.mpr
  rintro ω hu hv
  exact huv (Encodable.encode_injective (le_antisymm (hu.2.2 v hv.2.1 hv.1)
    (hv.2.2 u hu.2.1 hu.1)))

lemma iUnion_firstLayerHitAt (I : Set E) (x : V) (A : Set V) :
    (⋃ z, firstLayerHitAt G I x A z) = {ω | ∃ z ∈ A, Conn G (ω ∩ I) x z} := by
  ext ω
  constructor
  · intro h
    obtain ⟨z,hz⟩ := Set.mem_iUnion.mp h
    exact ⟨z,hz.2.1,hz.1⟩
  · rintro ⟨z,hz,hconn⟩
    have hex : ∃ n : ℕ, ∃ w : V, Encodable.encode w = n ∧ w ∈ A ∧ Conn G (ω ∩ I) x w :=
      ⟨Encodable.encode z,z,rfl,hz,hconn⟩
    obtain ⟨w,hwn,hw,hwconn⟩ := Nat.find_spec hex
    apply Set.mem_iUnion.mpr
    refine ⟨w,hwconn,hw,?_⟩
    intro v hv hvconn
    rw [hwn]
    exact Nat.find_min' hex ⟨v,rfl,hv,hvconn⟩

lemma firstLayerHitAt_dependsOn (I : Set E) (x : V) (A : Set V) (z : V) :
    DependsOn (fun ω => ω ∈ firstLayerHitAt G I x A z) I := by
  intro ω η hωη
  have he : Set.inter ω I = Set.inter η I := by
    ext e
    change (ω e ∧ e ∈ I) ↔ (η e ∧ e ∈ I)
    by_cases hi : e ∈ I
    · simp only [hi,and_true]
      exact Iff.of_eq (hωη e hi)
    · simp only [hi,and_false]
  change (Conn G (Set.inter ω I) x z ∧ z ∈ A ∧ ∀ w ∈ A,
      Conn G (Set.inter ω I) x w → Encodable.encode z ≤ Encodable.encode w) =
    (Conn G (Set.inter η I) x z ∧ z ∈ A ∧ ∀ w ∈ A,
      Conn G (Set.inter η I) x w → Encodable.encode z ≤ Encodable.encode w)
  rw [he]

lemma measurableSet_firstLayerHitAt [Countable E] (I : Set E) (x : V) (A : Set V) (z : V) :
    MeasurableSet (firstLayerHitAt G I x A z) := by
  have hm : Measurable (fun ω : Set E => ω ∩ I) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  have hc (y : V) : Measurable (fun ω : Set E => Conn G (ω ∩ I) x y) :=
    (measurableSet_conn G x y).mem.comp hm
  exact ((hc z).and (measurable_const.and (Measurable.forall fun w =>
    measurable_const.imp ((hc w).imp measurable_const)))).setOf

end Percolation.BenjaminiSchramm

end

end OAI
