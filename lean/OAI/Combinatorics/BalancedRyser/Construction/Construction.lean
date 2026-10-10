import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Basic.Real.Basic
import OAI.Combinatorics.BalancedRyser.Incidence.Affine

namespace OAI

namespace Balanced

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Slot (F : Type*) := Direction F × Bool
abbrev MergedPairs (F : Type*) := Direction F → Bool → F

structure FourTuple (F : Type*) where
  generator : Fin 4 → Direction F
  side : Fin 4 → Bool
  deriving DecidableEq

structure SplitChoice (F : Type*) where
  line : Line F
  tuple : FourTuple F
  deriving DecidableEq

structure Configuration (F : Type*) where
  merged : MergedPairs F
  choice : Slot F → SplitChoice F
  deriving DecidableEq

instance {F : Type*} [Fintype F] : Fintype (FourTuple F) :=
  Fintype.ofEquiv ((Fin 4 → Direction F) × (Fin 4 → Bool))
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun t => (t.generator, t.side)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance {F : Type*} [Fintype F] : Fintype (SplitChoice F) :=
  Fintype.ofEquiv (Line F × FourTuple F)
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun t => (t.line, t.tuple)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance {F : Type*} [Fintype F] : Fintype (Configuration F) :=
  Fintype.ofEquiv (MergedPairs F × (Slot F → SplitChoice F))
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun t => (t.merged, t.choice)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def constituent (M : MergedPairs F) (d : Direction F) (s : Bool) : Line F := (d, M d s)

def DistinctConstituents (M : MergedPairs F) : Prop :=
  ∀ d, M d false ≠ M d true

def constituentLines (M : MergedPairs F) : Finset (Line F) :=
  Finset.univ.image (fun ds : Direction F × Bool => constituent M ds.1 ds.2)

def mergedPoints (M : MergedPairs F) (d : Direction F) : Finset (Point F) :=
  linePoints (constituent M d false) ∪ linePoints (constituent M d true)

def tuplePoint (M : MergedPairs F) (T : FourTuple F) (i : Fin 4) : Point F :=
  lineIntersection (constituent M (T.generator i) (T.side i))
    (constituent M (T.generator (i + 1)) (!(T.side (i + 1))))

def designated (M : MergedPairs F) (C : SplitChoice F) : Finset (Point F) :=
  Finset.univ.image (tuplePoint M C.tuple)

def generatorSet (T : FourTuple F) : Finset (Direction F) :=
  Finset.univ.image T.generator

def Adjacent (M : MergedPairs F) (S : Line F) (p r : Point F) : Prop :=
  OnLine p S ∧ OnLine r S ∧ p ≠ r ∧ ∃ d : Direction F, d ≠ S.1 ∧
    ((OnLine p (constituent M d false) ∧ OnLine r (constituent M d true)) ∨
     (OnLine p (constituent M d true) ∧ OnLine r (constituent M d false)))

noncomputable def ValidChoice (M : MergedPairs F) (g : Direction F)
    (C : SplitChoice F) : Prop :=
  C.line.1 = g ∧ C.line ∉ constituentLines M ∧
  Function.Injective C.tuple.generator ∧ (∀ i, C.tuple.generator i ≠ g) ∧
  Function.Injective (tuplePoint M C.tuple) ∧
  (∀ i, OnLine (tuplePoint M C.tuple i) C.line) ∧
  ¬ Adjacent M C.line (tuplePoint M C.tuple 0) (tuplePoint M C.tuple 2) ∧
  ¬ Adjacent M C.line (tuplePoint M C.tuple 1) (tuplePoint M C.tuple 3) ∧
  ∀ p, OnLine p C.line → p ∉ designated M C →
    (Finset.univ.filter (fun i : Fin 4 => Adjacent M C.line p (tuplePoint M C.tuple i))).card ≤ 1

namespace Configuration

variable (C : Configuration F)

noncomputable def Valid : Prop :=
  DistinctConstituents C.merged ∧ ∀ s, ValidChoice C.merged s.1 (C.choice s)

noncomputable def Compatible : Prop :=
  (∀ i j, i ≠ j → ∀ p ∈ designated C.merged (C.choice j), ¬ OnLine p (C.choice i).line) ∧
  (∀ i j, i ≠ j →
    ((generatorSet (C.choice i).tuple) ∩ (generatorSet (C.choice j).tuple)).card ≤ 1) ∧
  (∀ i j, i ≠ j → i.1 = j.1 → ∀ d,
    ¬ (2 ≤ ((designated C.merged (C.choice i)) ∩ mergedPoints C.merged d).card ∧
       1 ≤ ((designated C.merged (C.choice j)) ∩ mergedPoints C.merged d).card))

def splitLines : Finset (Line F) := Finset.univ.image (fun s => (C.choice s).line)

def deletedLines : Finset (Line F) :=
  C.splitLines ∪ Finset.univ.image (fun d => constituent C.merged d true)

def core : Finset (Point F) :=
  Finset.univ.filter (fun p => ∀ l ∈ C.deletedLines, ¬ OnLine p l)

def retained : Finset (Point F) :=
  Finset.univ.filter (fun p => ∀ l ∈ C.splitLines, ¬ OnLine p l)

def points : Finset (Point F) :=
  C.retained ∪ Finset.univ.biUnion (fun s => designated C.merged (C.choice s))

def splitLinesAt (p : Point F) : Finset (Line F) :=
  C.splitLines.filter (OnLine p)

def splitMultiplicity (p : Point F) : ℕ := (C.splitLinesAt p).card

def designatedAt (p : Point F) : Finset (Point F) :=
  (Finset.univ.filter (fun s => OnLine p (C.choice s).line)).biUnion
    (fun s => designated C.merged (C.choice s))

def partnerSet (p : Point F) : Finset (Point F) :=
  (C.designatedAt p).filter (fun x => ∃ ds : Direction F × Bool,
    OnLine p (constituent C.merged ds.1 ds.2) ∧
    OnLine x (constituent C.merged ds.1 (!ds.2)))

def Occupancy (ρ : ℝ) (B : ℕ) : Prop :=
  (∀ p, ((constituentLines C.merged).filter (OnLine p)).card ≤ B) ∧
  (∀ l, l ∉ C.deletedLines → ρ * Fintype.card F ≤ ((linePoints l ∩ C.core).card : ℝ)) ∧
  (∀ d, ρ * Fintype.card F ≤
    ((linePoints (constituent C.merged d true) ∩ C.retained).card : ℝ))

def CoreConcentration (ρ : ℝ) : Prop :=
  ∀ L : Finset (Line F), (∀ l ∈ L, l ∉ C.deletedLines) →
    L.card ≤ Fintype.card F → CoversPoints L C.core →
    ∃ P : ProjectivePoint F,
      (1 - ρ / 4) * Fintype.card F ≤ ((L.filter (fun l => ThroughProjective l P)).card : ℝ)

end Configuration

abbrev LocalPiece (F : Type*) := Finset (Point F) ⊕ (Line F ⊕ Direction F)

namespace Configuration

variable (C : Configuration F)

def localPiecePoints : LocalPiece F → Finset (Point F)
  | Sum.inl U => U
  | Sum.inr (Sum.inl l) => linePoints l
  | Sum.inr (Sum.inr d) => mergedPoints C.merged d

def AllowedLocalPiece (p : Point F) : LocalPiece F → Prop
  | Sum.inl U => U.card ≤ 2
  | Sum.inr (Sum.inl l) => l ∉ C.splitLinesAt p ∪ constituentLines C.merged
  | Sum.inr (Sum.inr _) => True

def LocalCondition : Prop :=
  ∀ p, 3 ≤ C.splitMultiplicity p →
    ¬ ∃ A : Finset (LocalPiece F), A.card ≤ C.splitMultiplicity p - 1 ∧
      (∀ a ∈ A, C.AllowedLocalPiece p a) ∧
      C.designatedAt p ⊆ C.partnerSet p ∪ A.biUnion C.localPiecePoints

abbrev BlockLabel (F : Type*) := Line F ⊕ (Direction F ⊕ (Slot F × Bool))

def blockDirection : BlockLabel F → Direction F
  | Sum.inl l => l.1
  | Sum.inr (Sum.inl d) => d
  | Sum.inr (Sum.inr (s, _)) => s.1

def blockPoints : BlockLabel F → Finset (Point F)
  | Sum.inl l => linePoints l ∩ C.points
  | Sum.inr (Sum.inl d) => mergedPoints C.merged d ∩ C.points
  | Sum.inr (Sum.inr (s, false)) =>
      {tuplePoint C.merged (C.choice s).tuple 0, tuplePoint C.merged (C.choice s).tuple 2}
  | Sum.inr (Sum.inr (s, true)) =>
      {tuplePoint C.merged (C.choice s).tuple 1, tuplePoint C.merged (C.choice s).tuple 3}

def IsBlockLabel : BlockLabel F → Prop
  | Sum.inl l => l ∉ C.splitLines ∪ constituentLines C.merged
  | Sum.inr _ => True

noncomputable def blockLabels : Finset (BlockLabel F) :=
  Finset.univ.filter C.IsBlockLabel

noncomputable def labelsInDirection (d : Direction F) : Finset (BlockLabel F) :=
  C.blockLabels.filter (fun b => blockDirection b = d)

end Configuration
end
end Balanced

end OAI
