import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportPair

namespace OAI

noncomputable section
namespace Ostmann.Construction.CanonicalOccurrenceTransport
open Arithmetic.HistoryOccurrenceVariables Arithmetic.HistoryPairPattern
open Arithmetic.HistorySymbolicEncoding Characters.RationalHistory

lemma canonicalPairMap_level (seed : List SourceSlot) {l : ℕ} (h k : History l)
    (hh : TreeSourceLabels seed h) (hk : TreeSourceLabels seed k) (i : PairCoordinate seed l) :
    pairLevel h k (canonicalPairMap seed h k hh hk i)=
      Sum.elim (coordinateLevel seed l) (coordinateLevel seed l) i := by
  rcases i with i | i
  · exact (leftMap_level h k _).trans (coordinateEquiv_level seed h hh i)
  · exact (rightMap_level h k _).trans (coordinateEquiv_level seed k hk i)

theorem pairKeyEquiv_level (seed : List SourceSlot) {l : ℕ} (h k h' k' : History l)
    (hh : TreeSourceLabels seed h) (hk : TreeSourceLabels seed k)
    (hh' : TreeSourceLabels seed h') (hk' : TreeSourceLabels seed k')
    (hp : SamePairPattern seed h k h' k' hh hk hh' hk') (i : PairKey h k) :
    pairLevel h' k' (pairKeyEquiv seed h k h' k' hh hk hh' hk' hp i)=pairLevel h k i := by
  obtain ⟨j,rfl⟩ := canonicalPairMap_surjective seed h k hh hk i
  rw [pairKeyEquiv_map,canonicalPairMap_level,canonicalPairMap_level]

@[simp] theorem pairKeyEquiv_left (seed : List SourceSlot) {l : ℕ} (h k h' k' : History l)
    (hh : TreeSourceLabels seed h) (hk : TreeSourceLabels seed k)
    (hh' : TreeSourceLabels seed h') (hk' : TreeSourceLabels seed k')
    (hp : SamePairPattern seed h k h' k' hh hk hh' hk') (i : Coordinate seed l) :
    pairKeyEquiv seed h k h' k' hh hk hh' hk' hp
      (leftMap h k (coordinateEquiv seed h hh i))=leftMap h' k' (coordinateEquiv seed h' hh' i) :=
  pairKeyEquiv_map seed h k h' k' hh hk hh' hk' hp (.inl i)

@[simp] theorem pairKeyEquiv_right (seed : List SourceSlot) {l : ℕ} (h k h' k' : History l)
    (hh : TreeSourceLabels seed h) (hk : TreeSourceLabels seed k)
    (hh' : TreeSourceLabels seed h') (hk' : TreeSourceLabels seed k')
    (hp : SamePairPattern seed h k h' k' hh hk hh' hk') (i : Coordinate seed l) :
    pairKeyEquiv seed h k h' k' hh hk hh' hk' hp
      (rightMap h k (coordinateEquiv seed k hk i))=rightMap h' k' (coordinateEquiv seed k' hk' i) :=
  pairKeyEquiv_map seed h k h' k' hh hk hh' hk' hp (.inr i)

lemma rename_shared_of_normalized {I A A' B B' : Type} (u : I≃A) (v : I≃A')
    (f : A→B) (g : A'→B') (E : B→B') (e : Expr A) (e' : Expr A')
    (hm : ∀i,E (f (u i))=g (v i)) (he : e.rename u.symm=e'.rename v.symm) :
    (e.rename f).rename E=e'.rename g := by
  calc
    _ = (e.rename u.symm).rename (g ∘ v) := by
      rw [Expr.rename_comp,Expr.rename_comp]
      apply congrArg (fun z => e.rename z)
      funext a
      obtain ⟨i,rfl⟩ := u.surjective a
      simpa only [Function.comp_apply,Equiv.symm_apply_apply] using hm i
    _ = (e'.rename v.symm).rename (g ∘ v) := congrArg (Expr.rename (g ∘ v)) he
    _ = e'.rename g := by
      rw [Expr.rename_comp]
      apply congrArg (fun z => e'.rename z)
      funext a
      simp

theorem rename_left_shared (seed : List SourceSlot) {l : ℕ} (h k h' k' : History l)
    (hh : TreeSourceLabels seed h) (hk : TreeSourceLabels seed k)
    (hh' : TreeSourceLabels seed h') (hk' : TreeSourceLabels seed k')
    (hp : SamePairPattern seed h k h' k' hh hk hh' hk') (e : Expr (Key h)) (e' : Expr (Key h'))
    (he : e.rename (coordinateEquiv seed h hh).symm=e'.rename (coordinateEquiv seed h' hh').symm) :
    (e.rename (leftMap h k)).rename (pairKeyEquiv seed h k h' k' hh hk hh' hk' hp)=
      e'.rename (leftMap h' k') :=
  rename_shared_of_normalized _ _ _ _ _ e e' (pairKeyEquiv_left seed h k h' k' hh hk hh' hk' hp) he

theorem rename_right_shared (seed : List SourceSlot) {l : ℕ} (h k h' k' : History l)
    (hh : TreeSourceLabels seed h) (hk : TreeSourceLabels seed k)
    (hh' : TreeSourceLabels seed h') (hk' : TreeSourceLabels seed k')
    (hp : SamePairPattern seed h k h' k' hh hk hh' hk') (e : Expr (Key k)) (e' : Expr (Key k'))
    (he : e.rename (coordinateEquiv seed k hk).symm=e'.rename (coordinateEquiv seed k' hk').symm) :
    (e.rename (rightMap h k)).rename (pairKeyEquiv seed h k h' k' hh hk hh' hk' hp)=
      e'.rename (rightMap h' k') :=
  rename_shared_of_normalized _ _ _ _ _ e e' (pairKeyEquiv_right seed h k h' k' hh hk hh' hk' hp) he

end Ostmann.Construction.CanonicalOccurrenceTransport

end

end OAI
