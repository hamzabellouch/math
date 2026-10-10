import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairPattern
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportSources

namespace OAI

noncomputable section
namespace Ostmann.Construction.CanonicalOccurrenceTransport
open Arithmetic.HistoryOccurrenceVariables Arithmetic.HistoryPairPattern
open Arithmetic.HistorySymbolicEncoding

def sameFibersEquiv {A B C : Type} (f : A → B) (g : A → C)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (he : ∀ i j,f i=f j ↔ g i=g j) : B ≃ C := by
  let F : B → C := fun b => g (Classical.choose (hf b))
  have hF : ∀a,F (f a)=g a := by
    intro a
    exact (he _ a).mp (Classical.choose_spec (hf (f a)))
  apply Equiv.ofBijective F
  constructor
  · intro b b' hh
    have hx := (he (Classical.choose (hf b)) (Classical.choose (hf b'))).mpr hh
    simpa only [Classical.choose_spec (hf b),Classical.choose_spec (hf b')] using hx
  · intro c
    obtain ⟨a,rfl⟩ := hg c
    exact ⟨f a,hF a⟩

theorem sameFibersEquiv_apply {A B C : Type} (f : A → B) (g : A → C)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (he : ∀ i j,f i=f j ↔ g i=g j) (i : A) :
    sameFibersEquiv f g hf hg he (f i)=g i := by
  exact (he _ i).mp (Classical.choose_spec (hf (f i)))

abbrev PairCoordinate (seed : List SourceSlot) (l : ℕ) := Coordinate seed l ⊕ Coordinate seed l

def canonicalPairMap (seed : List SourceSlot) {l : ℕ} (h k : History l)
    (hh : TreeSourceLabels seed h) (hk : TreeSourceLabels seed k) :
    PairCoordinate seed l → PairKey h k :=
  Sum.elim (leftMap h k ∘ coordinateEquiv seed h hh) (rightMap h k ∘ coordinateEquiv seed k hk)

theorem canonicalPairMap_surjective (seed : List SourceSlot) {l : ℕ} (h k : History l)
    (hh : TreeSourceLabels seed h) (hk : TreeSourceLabels seed k) :
    Function.Surjective (canonicalPairMap seed h k hh hk) := by
  intro j
  obtain ⟨i,hi⟩ := unionMap_surjective h k j
  rcases i with i | i
  · refine ⟨.inl ((coordinateEquiv seed h hh).symm i),?_⟩
    simpa only [canonicalPairMap,unionMap,Function.comp_apply,Sum.elim_inl,Equiv.apply_symm_apply] using hi
  · refine ⟨.inr ((coordinateEquiv seed k hk).symm i),?_⟩
    simpa only [canonicalPairMap,unionMap,Function.comp_apply,Sum.elim_inr,Equiv.apply_symm_apply] using hi

def coordinatePattern (seed : List SourceSlot) {l : ℕ} (h : History l)
    (hh : TreeSourceLabels seed h) : Coordinate seed l → Bool ⊕ (ℕ×ℤ)
  | .inl b => .inl b
  | .inr i => .inr (coordinateLevel seed l (.inr i),coordinateSample seed h hh (.inr i))

def pairCoordinatePattern (seed : List SourceSlot) {l : ℕ} (h k : History l)
    (hh : TreeSourceLabels seed h) (hk : TreeSourceLabels seed k) :
    PairCoordinate seed l → Bool ⊕ (ℕ×ℤ) :=
  Sum.elim (coordinatePattern seed h hh) (coordinatePattern seed k hk)

lemma canonicalPairMap_val (seed : List SourceSlot) {l : ℕ} (h k : History l)
    (hh : TreeSourceLabels seed h) (hk : TreeSourceLabels seed k) (i : PairCoordinate seed l) :
    (canonicalPairMap seed h k hh hk i).val=pairCoordinatePattern seed h k hh hk i := by
  rcases i with i | i <;> rcases i with b | j | j
  · rfl
  · rfl
  · change Sum.inr (keyLevel h (coordinateEquiv seed h hh (.inr (.inr j))),_)=_
    rw [coordinateEquiv_level]
    rfl
  · rfl
  · rfl
  · change Sum.inr (keyLevel k (coordinateEquiv seed k hk (.inr (.inr j))),_)=_
    rw [coordinateEquiv_level]
    rfl

lemma canonicalPairMap_eq_iff (seed : List SourceSlot) {l : ℕ} (h k : History l)
    (hh : TreeSourceLabels seed h) (hk : TreeSourceLabels seed k) (i j : PairCoordinate seed l) :
    canonicalPairMap seed h k hh hk i=canonicalPairMap seed h k hh hk j ↔
      pairCoordinatePattern seed h k hh hk i=pairCoordinatePattern seed h k hh hk j := by
  constructor
  · intro he
    have hv := congrArg (fun x : PairKey h k => x.val) he
    simpa only [canonicalPairMap_val] using hv
  · intro he
    apply Subtype.ext
    simpa only [canonicalPairMap_val] using he

def SamePairPattern (seed : List SourceSlot) {l : ℕ} (h k h' k' : History l)
    (hh : TreeSourceLabels seed h) (hk : TreeSourceLabels seed k)
    (hh' : TreeSourceLabels seed h') (hk' : TreeSourceLabels seed k') : Prop :=
  ∀ i j, pairCoordinatePattern seed h k hh hk i=pairCoordinatePattern seed h k hh hk j ↔
    pairCoordinatePattern seed h' k' hh' hk' i=pairCoordinatePattern seed h' k' hh' hk' j

def pairKeyEquiv (seed : List SourceSlot) {l : ℕ} (h k h' k' : History l)
    (hh : TreeSourceLabels seed h) (hk : TreeSourceLabels seed k)
    (hh' : TreeSourceLabels seed h') (hk' : TreeSourceLabels seed k')
    (hp : SamePairPattern seed h k h' k' hh hk hh' hk') : PairKey h k ≃ PairKey h' k' :=
  sameFibersEquiv (canonicalPairMap seed h k hh hk) (canonicalPairMap seed h' k' hh' hk')
    (canonicalPairMap_surjective seed h k hh hk) (canonicalPairMap_surjective seed h' k' hh' hk')
    (fun i j => (canonicalPairMap_eq_iff seed h k hh hk i j).trans
      ((hp i j).trans (canonicalPairMap_eq_iff seed h' k' hh' hk' i j).symm))

@[simp] theorem pairKeyEquiv_map (seed : List SourceSlot) {l : ℕ} (h k h' k' : History l)
    (hh : TreeSourceLabels seed h) (hk : TreeSourceLabels seed k)
    (hh' : TreeSourceLabels seed h') (hk' : TreeSourceLabels seed k')
    (hp : SamePairPattern seed h k h' k' hh hk hh' hk') (i : PairCoordinate seed l) :
    pairKeyEquiv seed h k h' k' hh hk hh' hk' hp (canonicalPairMap seed h k hh hk i)=
      canonicalPairMap seed h' k' hh' hk' i :=
  sameFibersEquiv_apply _ _ _ _ _ i

end Ostmann.Construction.CanonicalOccurrenceTransport

end

end OAI
