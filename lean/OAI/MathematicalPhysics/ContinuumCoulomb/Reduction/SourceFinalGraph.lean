import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceContactCorrectness
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorSimple

namespace OAI

/-! The exact final graph indexed by the literal output vertex count.
Changing only the proof of that count preserves every bond and weight. -/

noncomputable section
namespace ContinuumCoulomb.MediatorIteration

def Bonds.castSites {n n' r : ℕ} (h : n=n') (F : Bonds n r) : Bonds n' r := h ▸ F

@[simp] theorem Bonds.castSites_toList {n n' r : ℕ} (h : n=n') (F : Bonds n r) :
    (F.castSites h).toList=F.toList := by cases h; rfl

@[simp] theorem Bonds.castSites_weight {n n' r : ℕ} (h : n=n') (F : Bonds n r) :
    (F.castSites h).weight=F.weight := by cases h; rfl

@[simp] theorem Bonds.castSites_left {n n' r : ℕ} (h : n=n') (F : Bonds n r) (e : Fin r) :
    (F.castSites h).left e=Fin.cast h (F.left e) := by cases h; rfl

@[simp] theorem Bonds.castSites_right {n n' r : ℕ} (h : n=n') (F : Bonds n r) (e : Fin r) :
    (F.castSites h).right e=Fin.cast h (F.right e) := by cases h; rfl

theorem Bonds.castSites_noLoops {n n' r : ℕ} (h : n=n') (F : Bonds n r) (hF : F.NoLoops) :
    (F.castSites h).NoLoops := by cases h; exact hF

theorem Bonds.castSites_simple {n n' r : ℕ} (h : n=n') (F : Bonds n r) (hF : F.Simple) :
    (F.castSites h).Simple := by cases h; exact hF

end ContinuumCoulomb.MediatorIteration

namespace ContinuumCoulomb.SourcePositiveProgram
open MediatorIteration SourceMetadataProgram ContactMediator

abbrev graphEdgeCount (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) : ℕ :=
  (geometricSource s d hd).edges +
    (((geometricSource s d hd).edges * 2 + (geometricSource s d hd).edges * 2 * 2) +
      ((geometricSource s d hd).edges * 2 + (geometricSource s d hd).edges * 2 * 2) * 2)

def graph (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    Bonds (output s d).vertices (graphEdgeCount s d hd) :=
  (finalGraph (sourceFamily s d hd) (sourceBound s d) (size d^s)).castSites
    (by simpa only [BinaryHeisenberg.toSource] using (vertices_eq s d hd).symm)

theorem graph_toList (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    (graph s d hd).toList=(output s d).bonds := by
  unfold graph
  erw [Bonds.castSites_toList]
  exact (bonds_eq s d hd).symm

theorem graph_weight (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    (graph s d hd).weight=SourceContactProgram.weights s d hd := by
  unfold graph
  erw [Bonds.castSites_weight]
  rfl

theorem graph_noLoops (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    (graph s d hd).NoLoops :=
  Bonds.castSites_noLoops _ _ (finalGraph_noLoops _ _ _)

theorem graph_simple (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    (graph s d hd).Simple :=
  Bonds.castSites_simple _ _ (finalGraph_simple _ _ _)

theorem hubbardGraph_exists (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid)
    {m : ℕ} (hm : (output s d).vertices=m+1) :
    ∃ F : Bonds (m+1) (graphEdgeCount s d hd),
      F.toList=(output s d).bonds ∧ F.NoLoops ∧ F.Simple ∧
      F.weight=SourceContactProgram.weights s d hd := by
  refine ⟨(graph s d hd).castSites hm,?_,?_,?_,?_⟩
  · rw [Bonds.castSites_toList,graph_toList]
  · exact Bonds.castSites_noLoops hm _ (graph_noLoops s d hd)
  · exact Bonds.castSites_simple hm _ (graph_simple s d hd)
  · rw [Bonds.castSites_weight,graph_weight]

end ContinuumCoulomb.SourcePositiveProgram

end

end OAI
