import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListIteration

namespace OAI

/-! The literal odd subdivision that initializes the bounded-degree compiler.
Each edge owns two consecutive mediator sites, and each original vertex keeps
the increasing list of its incident mediator ports. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram

def initialBond (bs : List Bond) (j : ℕ) : Bond :=
  (bs.drop (j/2)).headD (0,0,0)

def initialEndpoint (bs : List Bond) (j : ℕ) : ℕ :=
  if j%2=0 then (initialBond bs j).1 else (initialBond bs j).2.1

def initialWeight (bs : List Bond) (R : ℚ) (j : ℕ) : ℚ :=
  if j%2=0 then R else 2*R*(initialBond bs j).2.2

def initialIndices (bs : List Bond) (i : ℕ) : List ℕ :=
  (List.range (2*bs.length)).filter (fun j => decide (initialEndpoint bs j=i))

def initialGroup (n : ℕ) (bs : List Bond) (R : ℚ) (i : ℕ) : List Port :=
  (initialIndices bs i).map (fun j => (n+j,initialWeight bs R j))

def initialScale (N : ℚ) (bs : List Bond) (c : ℚ) : ℚ :=
  let A := 3*(bs.map (fun b => 1+2*|b.2.2|)).sum
  let B := |c|+4*(bs.map (fun b => (1+|b.2.2|)^2)).sum
  16*(A+B+1)^3*N+4*(A+B+1)+1

def initial (n : ℕ) (bs : List Bond) (c N : ℚ) : State :=
  let R := initialScale N bs c
  (n+2*bs.length,
    (List.range bs.length).map (fun e => (n+2*e,n+2*e+1,R^2)),
    c+(bs.map (fun b => 3/4+3*b.2.2^2)).sum+3*(bs.length:ℚ)*R^2,
    (List.range n).map (initialGroup n bs R))

theorem initialGroup_portAt (n : ℕ) (bs : List Bond) (R : ℚ) (i j : ℕ)
    (hj : j < (initialIndices bs i).length) :
    portAt (initialGroup n bs R i) j=
      (n+(initialIndices bs i)[j],initialWeight bs R (initialIndices bs i)[j]) := by
  rw [portAt_eq_getElem _ _ (by simpa only [initialGroup,List.length_map] using hj)]
  simp only [initialGroup,List.getElem_map]

theorem initialIndices_mem (bs : List Bond) (i j : ℕ) (hj : j ∈ initialIndices bs i) :
    j < 2*bs.length ∧ initialEndpoint bs j=i := by
  simpa only [initialIndices,List.mem_filter,List.mem_range,decide_eq_true_eq] using hj

theorem initialIndices_nodup (bs : List Bond) (i : ℕ) : (initialIndices bs i).Nodup :=
  (List.nodup_range : (List.range (2*bs.length)).Nodup).filter _

theorem initialGroup_bounded (n : ℕ) (bs : List Bond) (R : ℚ) (i j : ℕ)
    (hj : j < (initialGroup n bs R i).length) :
    (portAt (initialGroup n bs R i) j).1 < n+2*bs.length := by
  have hj' : j < (initialIndices bs i).length := by
    simpa only [initialGroup,List.length_map] using hj
  rw [initialGroup_portAt n bs R i j hj']
  have hm := initialIndices_mem bs i _ (List.getElem_mem hj')
  dsimp only
  omega

theorem initialGroup_disjoint (n : ℕ) (bs : List Bond) (R : ℚ) (k i j : ℕ)
    (hk : k < n) (hj : j < (initialGroup n bs R i).length) :
    k ≠ (portAt (initialGroup n bs R i) j).1 := by
  have hj' : j < (initialIndices bs i).length := by
    simpa only [initialGroup,List.length_map] using hj
  rw [initialGroup_portAt n bs R i j hj']
  dsimp only
  omega

theorem initialGroup_injective (n : ℕ) (bs : List Bond) (R : ℚ) (i k j l : ℕ)
    (hj : j < (initialGroup n bs R i).length)
    (hl : l < (initialGroup n bs R k).length)
    (he : (portAt (initialGroup n bs R i) j).1=
      (portAt (initialGroup n bs R k) l).1) : i=k ∧ j=l := by
  have hj' : j < (initialIndices bs i).length := by
    simpa only [initialGroup,List.length_map] using hj
  have hl' : l < (initialIndices bs k).length := by
    simpa only [initialGroup,List.length_map] using hl
  rw [initialGroup_portAt n bs R i j hj',initialGroup_portAt n bs R k l hl'] at he
  have he' : (initialIndices bs i)[j]=(initialIndices bs k)[l] := by
    dsimp only at he
    omega
  have hmj := (initialIndices_mem bs i _ (List.getElem_mem hj')).2
  have hml := (initialIndices_mem bs k _ (List.getElem_mem hl')).2
  have hik : i=k := by rw [he',hml] at hmj; exact hmj.symm
  refine ⟨hik,?_⟩
  subst k
  exact (initialIndices_nodup bs i).eq_of_getElem_eq hj' hl' he'

theorem initial_validPorts (n : ℕ) (bs : List Bond) (c N : ℚ) :
    ValidPorts (initial n bs c N).1 (initial n bs c N).2.2.2 := by
  have hg (i : ℕ) (hi : i < n) :
      groupAt (initial n bs c N).2.2.2 i=initialGroup n bs (initialScale N bs c) i := by
    change groupAt ((List.range n).map (initialGroup n bs (initialScale N bs c))) i=_
    rw [groupAt,List.headD_eq_head?_getD,List.head?_drop,
      List.getElem?_eq_getElem (by simpa using hi)]
    simp only [Option.getD_some,List.getElem_map,List.getElem_range]
  have hlen : (initial n bs c N).2.2.2.length=n := by simp only [initial,List.length_map,List.length_range]
  constructor
  · rw [hlen]
    exact Nat.le_add_right _ _
  · intro i j
    have hi : i.val < n := by simpa only [hlen] using i.isLt
    have hj : j.val < (initialGroup n bs (initialScale N bs c) i.val).length := by
      simpa only [hg i.val hi] using j.isLt
    change (portAt (groupAt (initial n bs c N).2.2.2 i.val) j.val).1 < n+2*bs.length
    simpa only [hg i.val hi] using initialGroup_bounded n bs _ i.val j.val hj
  · intro i k j
    have hi : i.val < n := by simpa only [hlen] using i.isLt
    have hk : k.val < n := by simpa only [hlen] using k.isLt
    have hj : j.val < (initialGroup n bs (initialScale N bs c) k.val).length := by
      simpa only [hg k.val hk] using j.isLt
    simpa only [hg k.val hk] using initialGroup_disjoint n bs _ i.val k.val j.val hi hj
  · intro i k j l he
    have hi : i.val < n := by simpa only [hlen] using i.isLt
    have hk : k.val < n := by simpa only [hlen] using k.isLt
    have hj : j.val < (initialGroup n bs (initialScale N bs c) i.val).length := by
      simpa only [hg i.val hi] using j.isLt
    have hl : l.val < (initialGroup n bs (initialScale N bs c) k.val).length := by
      simpa only [hg k.val hk] using l.isLt
    have he' : (portAt (initialGroup n bs (initialScale N bs c) i.val) j.val).1=
        (portAt (initialGroup n bs (initialScale N bs c) k.val) l.val).1 := by
      simpa only [hg i.val hi,hg k.val hk] using he
    obtain ⟨hik,hjl⟩ := initialGroup_injective n bs _ i.val k.val j.val l.val hj hl he'
    exact ⟨Fin.ext hik,hjl⟩

end ContinuumCoulomb.QuantumForkList

end

end OAI
