import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawCompiler
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRationalDegreeReduction

namespace OAI

/-! Ordered rational data for the degree-three fork compiler. Original centers
retain their numbers. Each pair of active ports receives two consecutive new
spin numbers, and an unpaired port remains active at its original center. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram

abbrev Port := ℕ × ℚ
abbrev Pair := Port × Port
abbrev Groups := List (List Port)
abbrev State := ℕ × (List Bond × (ℚ × Groups))
abbrev TaggedPair := ℕ × Pair

def portAt (ps : List Port) (i : ℕ) : Port := (ps.drop i).headD (0,0)
def groupAt (gs : Groups) (i : ℕ) : List Port := (gs.drop i).headD []

def pairs (ps : List Port) : List Pair :=
  (List.range (ps.length/2)).map (fun i => (portAt ps (2*i),portAt ps (2*i+1)))

def unpaired (ps : List Port) : List Port := ps.drop (2*(ps.length/2))

def catalog (gs : Groups) : List TaggedPair :=
  ((List.range gs.length).map (fun i => (pairs (groupAt gs i)).map (fun p => (i,p)))).flatten

def pairCount (gs : Groups) : ℕ := (gs.map (fun ps => ps.length/2)).sum
def pairStart (gs : Groups) (i : ℕ) : ℕ := pairCount (gs.take i)

def pairLinear (p : Pair) : ℚ := 1+2*|p.1.2|+2*|p.2.2|
def pairSquare (p : Pair) : ℚ := (1+|p.1.2|+|p.2.2|)^2
def pairOffset (p : Pair) : ℚ := 3/4+3*p.1.2^2+3*p.2.2^2

def retained (s : State) : List ℚ :=
  s.2.1.map (fun b => b.2.2) ++ ((s.2.2.2.map unpaired).flatten.map Prod.snd)

def scale (N : ℚ) (s : State) : ℚ :=
  let ps := (catalog s.2.2.2).map Prod.snd
  let B := 3*(retained s |>.map abs).sum+|s.2.2.1|
  let A := 3*(ps.map pairLinear).sum
  let D := B+12*(ps.map pairSquare).sum
  16*(A+D+1)^3*N+4*(A+D+1)+1

def pairBonds (n i : ℕ) (R : ℚ) (p : Pair) : List Bond :=
  [(p.1.1,p.2.1,2*p.1.2*p.2.2),
   (n+2*i,n+2*i+1,R^2),
   (p.1.1,n+2*i+1,2*R*p.1.2),
   (p.2.1,n+2*i+1,2*R*p.2.2)]

def addedBonds (s : State) (R : ℚ) : List Bond :=
  let ps := catalog s.2.2.2
  ((List.range ps.length).map (fun i => pairBonds s.1 i R
    ((ps.drop i).headD (0,((0,0),(0,0)))).2)).flatten

def nextGroup (n : ℕ) (R : ℚ) (gs : Groups) (i : ℕ) : List Port :=
  let ps := groupAt gs i
  (List.range (ps.length/2)).map (fun j => (n+2*(pairStart gs i+j),R)) ++ unpaired ps

def next (N : ℚ) (s : State) : State :=
  let R := scale N s
  let ps := (catalog s.2.2.2).map Prod.snd
  (s.1+2*pairCount s.2.2.2,
    s.2.1++addedBonds s R,
    s.2.2.1+(ps.map pairOffset).sum+3*(pairCount s.2.2.2:ℚ)*R^2,
    (List.range s.2.2.2.length).map (nextGroup s.1 R s.2.2.2))

def iterate (N : ℚ) : ℕ → State → State
  | 0,s => s
  | k+1,s => next N (iterate N k s)

theorem pairs_length (ps : List Port) : (pairs ps).length=ps.length/2 := by
  simp [pairs]

theorem unpaired_length (ps : List Port) : (unpaired ps).length=ps.length%2 := by
  simp only [unpaired,List.length_drop]
  omega

theorem unpaired_length_le (ps : List Port) : (unpaired ps).length ≤ 1 := by
  rw [unpaired_length]
  omega

theorem pairCount_cons (ps : List Port) (gs : Groups) :
    pairCount (ps::gs)=ps.length/2+pairCount gs := rfl

theorem groupAt_cons_zero (ps : List Port) (gs : Groups) : groupAt (ps::gs) 0=ps := rfl

theorem groupAt_cons_succ (ps : List Port) (gs : Groups) (i : ℕ) :
    groupAt (ps::gs) (i+1)=groupAt gs i := by
  simp [groupAt,List.drop_succ_cons]

theorem catalog_length (gs : Groups) : (catalog gs).length=pairCount gs := by
  unfold catalog
  rw [List.length_flatten,List.map_map]
  simp only [Function.comp_def,List.length_map,pairs_length]
  change ((List.range gs.length).map (fun i => ((gs.drop i).headD []).length/2)).sum = _
  rw [ExactQuantumFactoring.BitStackProgram.map_range_getD gs [] (fun ps => ps.length/2)]
  rfl

theorem pairBonds_length (n i : ℕ) (R : ℚ) (p : Pair) :
    (pairBonds n i R p).length=4 := rfl

theorem nextGroup_length (n : ℕ) (R : ℚ) (gs : Groups) (i : ℕ) :
    (nextGroup n R gs i).length=(groupAt gs i).length/2+(groupAt gs i).length%2 := by
  simp [nextGroup,unpaired_length]

theorem next_centers (N : ℚ) (s : State) : (next N s).2.2.2.length=s.2.2.2.length := by
  simp [next]

theorem next_count (N : ℚ) (s : State) : (next N s).1=s.1+2*pairCount s.2.2.2 := rfl

theorem iterate_centers (N : ℚ) (s : State) (k : ℕ) :
    (iterate N k s).2.2.2.length=s.2.2.2.length := by
  induction k with
  | zero => rfl
  | succ k ih => exact (next_centers N (iterate N k s)).trans ih

theorem next_group_length (N : ℚ) (s : State) (i : ℕ) (hi : i < s.2.2.2.length) :
    (groupAt (next N s).2.2.2 i).length=
      (groupAt s.2.2.2 i).length/2+(groupAt s.2.2.2 i).length%2 := by
  change (groupAt ((List.range s.2.2.2.length).map
    (nextGroup s.1 (scale N s) s.2.2.2)) i).length=_
  rw [groupAt,List.headD_eq_head?_getD,List.head?_drop,
    List.getElem?_eq_getElem (by simpa using hi)]
  simp only [Option.getD_some,List.getElem_map,List.getElem_range,nextGroup_length]

theorem iterate_group_length (N : ℚ) (s : State) (k i : ℕ) (hi : i < s.2.2.2.length) :
    (groupAt (iterate N k s).2.2.2 i).length=
      qmaForkDegreeAfter (groupAt s.2.2.2 i).length k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate,next_group_length N (iterate N k s) i (by rwa [iterate_centers]),ih]
    rfl

theorem addedBonds_length (s : State) (R : ℚ) :
    (addedBonds s R).length=4*pairCount s.2.2.2 := by
  unfold addedBonds
  rw [List.length_flatten,List.map_map]
  simp only [Function.comp_def,pairBonds_length,List.map_const',List.length_range,
    List.sum_replicate,smul_eq_mul,catalog_length]
  omega

theorem next_bonds_length (N : ℚ) (s : State) :
    (next N s).2.1.length=s.2.1.length+4*pairCount s.2.2.2 := by
  change (s.2.1++addedBonds s (scale N s)).length=_
  rw [List.length_append,addedBonds_length]

theorem iterate_group_bound (N : ℚ) (s : State) (D i : ℕ)
    (hi : i < s.2.2.2.length) (hD : (groupAt s.2.2.2 i).length ≤ D) :
    (groupAt (iterate N D s).2.2.2 i).length ≤ 1 := by
  rw [iterate_group_length N s D i hi]
  exact qmaForkDegreeAfter_constant _ D hD

end ContinuumCoulomb.QuantumForkList

end

end OAI
