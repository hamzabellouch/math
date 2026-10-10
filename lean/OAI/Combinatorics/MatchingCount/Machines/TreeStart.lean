import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeColor

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

def evenTest : Realizer (fun n : ℕ=>decide (n%2=0)) :=
  composition (pair (composition (pair identity (constant 2)) remainder) (constant 0)) natEqual
lemma polynomial_evenTest : PolynomialTime evenTest := by
  unfold evenTest
  have := polynomial_remainder
  tree_cost

def mateIndex (n : ℕ) : ℕ := if n%2=0 then n+1 else n-1
def mateIndexRealizer : Realizer mateIndex := (choose evenTest
  (composition (pair identity (constant 1)) TreeTyped.add)
  (composition (pair identity (constant 1)) subtract)).congr (by intro n; simp only [mateIndex,Function.comp_apply,id_eq,decide_eq_true_eq])
lemma polynomial_mateIndex : PolynomialTime mateIndexRealizer := by
  unfold mateIndexRealizer
  apply polynomial_congr
  have := polynomial_evenTest
  tree_cost
lemma mateIndex_source {n : ℕ} (he : Even n) (i : Fin n) :
    mateIndex i.val=(RationalSource.pairIndex he i).val := by
  simp only [mateIndex,RationalSource.pairIndex]
  split_ifs <;> rfl

def startSelected (e : RawReal) : Bool :=
  Subdivision.alternating (decide (mateIndex e.1.1=e.1.2)) e.2
def startSelectedRealizer : Realizer startSelected :=
  (choose (composition second evenTest)
    (composition (pair (composition first.fst mateIndexRealizer) first.snd) natEqual)
    (composition (composition (pair (composition first.fst mateIndexRealizer) first.snd) natEqual) boolNot)).congr
    (by intro e; simp only [startSelected,Subdivision.alternating,Function.comp_apply,decide_eq_true_eq])
lemma polynomial_startSelected : PolynomialTime startSelectedRealizer := by
  unfold startSelectedRealizer
  dsimp only [Realizer.fst,Realizer.snd]
  apply polynomial_congr
  have := polynomial_evenTest
  have := polynomial_mateIndex
  tree_cost
lemma startSelected_source {n : ℕ} (K : ℕ) (he : Even n) (e : SourceRealEdge (Fin n) K) :
    startSelected (realRepr e)=Subdivision.alternating
      (RationalSource.selectMate (RationalSource.orderedMate he) e.1) e.2.val := by
  unfold startSelected realRepr logicalRepr
  rw [mateIndex_source he]
  congr 1
  change decide ((RationalSource.pairIndex he _).val=_)=decide (RationalSource.pairIndex he _=_)
  congr 1
  exact propext Fin.val_inj

def exactStart (x : BagBuildInput) : Finset ℕ :=
  (((realEdges (x.1.2,x.1.1.2)).filter startSelected).map
    (fun e=>sourceRealIndex (x,e))).toFinset
def exactStartRealizer : Realizer exactStart := (composition
  (composition (pair identity (composition (composition
    (pair first.snd first.fst.snd) realEdgesRealizer) (filter startSelectedRealizer)))
    (mapWith sourceRealIndexRealizer)) (listFinset natEqual leNat)).congr (fun _=>rfl)
lemma polynomial_exactStart : PolynomialTime exactStartRealizer := by
  unfold exactStartRealizer
  dsimp only [Realizer.fst,Realizer.snd]
  apply polynomial_congr
  have := polynomial_realEdges
  have := polynomial_filter polynomial_startSelected
  have := polynomial_mapWith polynomial_sourceRealIndex
  have := polynomial_listFinset polynomial_natEqual polynomial_leNat
  tree_cost

lemma numbered_map_image {A B : Type} [Fintype A] [LinearOrder A] [DecidableEq B]
    (f : B↪A) (s : Finset B) : Numbered.set (s.map f)=s.image (fun b=>index (f b)) := by
  unfold Numbered.set
  rw [Finset.map_map]
  exact Finset.map_eq_image _ _

lemma startMatching_set {n : ℕ} [Nontrivial (Fin n)] (w : Fin n→Fin n→ℚ)
    (K : ℕ) (he : Even n) :
    Numbered.set (RationalSource.startMatching w K he).val=
      (RationalSource.startSet K he).image (fun a=>index (RationalSource.coloredReal w K a)) :=
  numbered_map_image _ _

lemma exactStart_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n) (he : Even n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ) :
    exactStart (((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false)=
      Numbered.set (RationalSource.startMatching w K he).val := by
  rw [startMatching_set]
  ext i
  change i∈(((realEdges (List.range n,List.replicate (2*K+2) false)).filter startSelected).map
    (fun e=>sourceRealIndex ((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),e))).toFinset ↔ _
  simp only [List.mem_toFinset,List.mem_map,List.mem_filter,Finset.mem_image,
    RationalSource.startSet,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨e,⟨he',hsel⟩,hi⟩
    have hre : e∈(realEdges (List.range n,List.replicate (2*K+2) false)).toFinset:=List.mem_toFinset.mpr he'
    rw [realEdges_finset n K _ (List.length_replicate ..)] at hre
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hre
    refine ⟨a,?_,?_⟩
    · exact (startSelected_source K he a).symm.trans hsel
    · exact (sourceRealIndex_source hn w hw K a).symm.trans hi
  · rintro ⟨a,ha,hai⟩
    refine ⟨realRepr a,⟨?_,?_⟩,?_⟩
    · apply List.mem_toFinset.mp
      rw [realEdges_finset n K _ (List.length_replicate ..)]
      exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
    · exact (startSelected_source K he a).trans ha
    · exact (sourceRealIndex_source hn w hw K a).trans hai

open TreePost Turing

theorem exactStart_post : ∃ p : Polynomial ℕ,∀ x : BagBuildInput,∀ t : ℕ,
    p.eval (packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (machine exactStartRealizer.program) (packed x) coins).state=none ∧
      (run (machine exactStartRealizer.program) (packed x) coins).tape.right₀=
        ListBlank.mk (packed (exactStart x)) :=
  polynomial_compiles exactStartRealizer polynomial_exactStart
end MatchingFPRAS.ExecutableSource

end OAI
