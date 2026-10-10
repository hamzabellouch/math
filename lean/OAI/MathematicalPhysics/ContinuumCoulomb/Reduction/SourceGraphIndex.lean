import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceFinalGraph
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PrefactorSourceContactCorrectness

namespace OAI

/-! The actual contact-site enumeration and the finite Hubbard graph use
one common electron index. Relabeling changes no bond or coordinate order. -/

noncomputable section
namespace ContinuumCoulomb.SourcePositiveProgram
open MediatorIteration ContactMediator SourceMetadataProgram

private theorem rawSiteCount (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    (geometricSource s d hd).vertices+(geometricSource s d hd).edges*2+
      (geometricSource s d hd).edges*2*2+
        ((geometricSource s d hd).edges*2+(geometricSource s d hd).edges*2*2)*2 =
      (output s d).vertices := by
  simpa only [geometricSource,SourceNormalizedSpectrum.lattice,BinaryHeisenberg.toSource]
    using (vertices_eq s d hd).symm

def siteEquiv (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    GlobalSite (geometricSource s d hd) ≃ Fin (output s d).vertices :=
  finCongr (rawSiteCount s d hd)

@[irreducible] def indexedGraph (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) {m : ℕ}
    (hm : (output s d).vertices=m+1) : Bonds (m+1) (graphEdgeCount s d hd) :=
  (graph s d hd).castSites hm

def indexedSites (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) {m : ℕ}
    (hm : (output s d).vertices=m+1) : GlobalSite (geometricSource s d hd) ≃ Fin (m+1) :=
  (siteEquiv s d hd).trans (finCongr hm)

theorem graph_left (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid)
    (a : GlobalEdge (geometricSource s d hd)) :
    (graph s d hd).left a = siteEquiv s d hd
      ((finalGraph (geometricSource s d hd).bonds (sourceBound s d) (size d^s)).left a) := by
  unfold graph
  erw [Bonds.castSites_left]
  rfl

theorem graph_right (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid)
    (a : GlobalEdge (geometricSource s d hd)) :
    (graph s d hd).right a = siteEquiv s d hd
      ((finalGraph (geometricSource s d hd).bonds (sourceBound s d) (size d^s)).right a) := by
  unfold graph
  erw [Bonds.castSites_right]
  rfl

theorem indexedGraph_left (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) {m : ℕ}
    (hm : (output s d).vertices=m+1) (a : GlobalEdge (geometricSource s d hd)) :
    (indexedGraph s d hd hm).left a = indexedSites s d hd hm
      ((finalGraph (geometricSource s d hd).bonds (sourceBound s d) (size d^s)).left a) := by
  unfold indexedGraph
  erw [Bonds.castSites_left,graph_left]
  rfl

theorem indexedGraph_right (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) {m : ℕ}
    (hm : (output s d).vertices=m+1) (a : GlobalEdge (geometricSource s d hd)) :
    (indexedGraph s d hd hm).right a = indexedSites s d hd hm
      ((finalGraph (geometricSource s d hd).bonds (sourceBound s d) (size d^s)).right a) := by
  unfold indexedGraph
  erw [Bonds.castSites_right,graph_right]
  rfl

theorem indexedGraph_toList (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) {m : ℕ}
    (hm : (output s d).vertices=m+1) :
    (indexedGraph s d hd hm).toList=(output s d).bonds := by
  rw [indexedGraph,Bonds.castSites_toList,graph_toList]

theorem indexedGraph_weight (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) {m : ℕ}
    (hm : (output s d).vertices=m+1) :
    (indexedGraph s d hd hm).weight=SourceContactProgram.weights s d hd := by
  rw [indexedGraph,Bonds.castSites_weight,graph_weight]

theorem indexedGraph_noLoops (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) {m : ℕ}
    (hm : (output s d).vertices=m+1) : (indexedGraph s d hd hm).NoLoops := by
  unfold indexedGraph
  exact Bonds.castSites_noLoops hm _ (graph_noLoops s d hd)

theorem indexedGraph_simple (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) {m : ℕ}
    (hm : (output s d).vertices=m+1) : (indexedGraph s d hd hm).Simple := by
  unfold indexedGraph
  exact Bonds.castSites_simple hm _ (graph_simple s d hd)

private theorem ofFn_finCongr {α : Type*} {n m : ℕ} (h : n=m) (f : Fin n → α) :
    List.ofFn (fun i => f ((finCongr h).symm i)) = List.ofFn f := by
  subst m
  rfl

theorem indexedSites_ofFn {α : Type*} (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) {m : ℕ}
    (hm : (output s d).vertices=m+1) (f : GlobalSite (geometricSource s d hd) → α) :
    List.ofFn (fun i => f ((indexedSites s d hd hm).symm i))=List.ofFn f := by
  unfold indexedSites siteEquiv
  change List.ofFn (fun i => f ((finCongr (rawSiteCount s d hd)).symm
    ((finCongr hm).symm i)))=List.ofFn f
  exact (ofFn_finCongr hm (fun i => f ((finCongr (rawSiteCount s d hd)).symm i))).trans
    (ofFn_finCongr (rawSiteCount s d hd) f)

end ContinuumCoulomb.SourcePositiveProgram

end

end OAI
