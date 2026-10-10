import Mathlib
import OAI.Geometry.HyperbolicGroups.DipoleChain
import OAI.Geometry.HyperbolicGroups.IndexedFace
import OAI.Geometry.HyperbolicGroups.MappedCancellation

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k

/-- Oriented, individually indexed polygon boundaries in a target cell
complex. In a lifted target, `S` includes the lift of the cell. Opposite
orientations have disjoint side cycles; the same indexed side is retained
when reversing. These data contain no diagram or normal-form assertion. -/
structure CellTarget (S : Type v) (L : Type w) (V : Type z) (A : Type k)
    [AddCommMonoid A] where
  next : Perm S
  opposite : Perm S
  opposite_sq : opposite * opposite = 1
  reverse_next : ∀ s, opposite (next s) = next⁻¹ (opposite s)
  opposite_cycle : ∀ s, ¬ next.SameCycle s (opposite s)
  edge : S → L
  start : L → V
  rev : L → L
  rev_rev : ∀ l, rev (rev l) = l
  edge_opposite : ∀ s, edge (opposite s) = rev (edge s)
  next_start : ∀ s, start (edge (next s)) = start (rev (edge s))
  apex : V → Bool
  radial : ∀ s, apex (start (edge s)) = true → apex (start (rev (edge s))) = false
  weight : S → A
  weight_next : ∀ s, weight (next s) = weight s
  weight_opposite : ∀ s, weight s + weight (opposite s) = 0

variable {S : Type v} {L : Type w} {V : Type z} {A : Type k} [AddCommMonoid A]

/-- A finite genus-zero side pairing with actual indexed cellular face maps.
This describes a raw picture, without any reducedness or link bounds. -/
structure CellPicture (T : CellTarget S L V A) where
  Dart : Type u
  [finite : Fintype Dart]
  [decEq : DecidableEq Dart]
  pairing : PictureMap Dart
  index : Dart → S
  mapped : IndexedFaceMap pairing.face T.next index
  respects : pairing.Respects (T.edge ∘ index) T.start T.rev
  genusZero : pairing.GenusZero

attribute [instance] CellPicture.finite CellPicture.decEq

namespace CellPicture
variable {T : CellTarget S L V A} (P : CellPicture.{u} T)

def chain : A := faceChain P.pairing.face (T.weight ∘ P.index)
  (fun x => by change T.weight (P.index (P.pairing.face x)) = _; rw [P.mapped.commute,T.weight_next]; rfl)

def Reduced : Prop := ∀ x, P.index (P.pairing.edge x) ≠ T.opposite (P.index x)

def RadialInjective : Prop := ∀ a b,
  T.apex (T.start (T.edge (P.index a))) = true → P.pairing.vertex.SameCycle a b →
    T.edge (P.index a) = T.edge (P.index b) → a = b

/-- Retention maps leave every retained face and its individual side indices
unchanged. They may discard whole faces; switches only change side pairings. -/
structure Retains (Q : CellPicture.{u} T) where
  map : Q.Dart → P.Dart
  injective : Function.Injective map
  face : ∀ x, map (Q.pairing.face x) = P.pairing.face (map x)
  index : ∀ x, Q.index x = P.index (map x)

/-- Finite normalization producing BOTH forbidden-adjacency cancellation and
radial-label injectivity, while preserving the EXACT signed cellular chain.
After every cancellation there are fewer darts, so re-normalizing radial links
cannot cause an infinite cancel/switch loop. No minimal-picture conclusion is
assumed. The initial picture existence/realization theorem is separate. -/
theorem normalize : ∃ Q : CellPicture.{u} T,
    Nonempty (P.Retains Q) ∧ Q.Reduced ∧ Q.RadialInjective ∧ Q.chain = P.chain := by
  classical
  have produce : ∀ n, ∀ P : CellPicture.{u} T, Fintype.card P.Dart = n →
      ∃ Q : CellPicture.{u} T,
        Nonempty (P.Retains Q) ∧ Q.Reduced ∧ Q.RadialInjective ∧ Q.chain = P.chain := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro P hcard
      obtain ⟨N,hf,hN,hG,hinj⟩ := PictureMap.normalize_radial T.apex P.respects P.genusZero
        (fun d => T.radial (P.index d))
      let P' : CellPicture.{u} T := {
        Dart := P.Dart
        pairing := N
        index := P.index
        mapped := by rw [hf]; exact P.mapped
        respects := hN
        genusZero := hG }
      have hc : P'.chain = P.chain := by simp only [chain,P',hf]
      by_cases hred : P'.Reduced
      · refine ⟨P',⟨⟨id,Function.injective_id,?_,fun _ => rfl⟩⟩,hred,hinj,hc⟩
        intro x
        exact congrArg (fun p : Perm P.Dart => p x) hf
      · obtain ⟨a,ha⟩ := not_forall.mp hred
        have ha : P'.index (N.edge a) = T.opposite (P'.index a) := of_not_not ha
        obtain ⟨q,b,hF,hb,hmap⟩ := P'.mapped.opposite_faces T.opposite T.opposite_sq
          T.reverse_next T.opposite_cycle a (N.edge a) ha
        let i₀ : {x : P.Dart // N.face.SameCycle a x} := ⟨a,SameCycle.rfl⟩
        have wnext : ∀ x, (T.weight ∘ P'.index) (N.face x) = (T.weight ∘ P'.index) x := by
          intro x
          change T.weight (P'.index (N.face x)) = _
          rw [P'.mapped.commute,T.weight_next]
          rfl
        have hw : (T.weight ∘ P'.index) (Subtype.val i₀) +
            (T.weight ∘ P'.index) (b i₀) = 0 := by
          change T.weight (P'.index i₀.val) + T.weight (P'.index (b i₀)) = 0
          rw [hmap]
          exact T.weight_opposite _
        obtain ⟨R,hRG,hRM,hRF,hRC,hRW,hRchain⟩ := N.cancel_mapped_dipole hF i₀ hb.symm
          P'.respects P'.genusZero T.rev_rev
          (fun i => by change T.edge (P'.index (b i)) = _; rw [hmap,T.edge_opposite]; rfl)
          (T.weight ∘ P'.index) wnext hw
        let Q₀ : CellPicture.{u} T := {
          Dart := {x : P.Dart // ¬ PictureMap.InDipole Subtype.val b x}
          pairing := R
          index := P'.index ∘ Subtype.val
          mapped := {
            commute := fun x => by
              change P'.index (R.face x).val = _
              rw [hRF]
              exact P'.mapped.commute x.val
            injective := fun {x y} hxy he => Subtype.ext
              (P'.mapped.injective (semiconj_perm_sameCycle hRF hxy) he) }
          respects := hRM
          genusZero := hRG }
        have hsmall : Fintype.card Q₀.Dart < n := by
          rw [← hcard]
          exact Fintype.card_subtype_lt (x := a) (by
            intro h
            exact h (Or.inl ⟨i₀,rfl⟩))
        obtain ⟨Q,hret,hred,hrad,hchain⟩ := ih (Fintype.card Q₀.Dart) hsmall Q₀ rfl
        obtain ⟨ret⟩ := hret
        refine ⟨Q,⟨⟨Subtype.val ∘ ret.map,Subtype.val_injective.comp ret.injective,?_,?_⟩⟩,
          hred,hrad,?_⟩
        · intro x
          change (ret.map (Q.pairing.face x)).val = P.pairing.face (ret.map x).val
          rw [ret.face]
          exact (hRF _).trans (congrArg (fun p : Perm P.Dart => p (ret.map x).val) hf)
        · intro x
          exact ret.index x
        · have hzero : Q₀.chain = P'.chain := by exact hRchain
          exact hchain.trans (hzero.trans hc)
  exact produce (Fintype.card P.Dart) P rfl

end CellPicture
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
