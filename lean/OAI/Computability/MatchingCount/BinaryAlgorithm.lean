import OAI.Computability.MatchingCount.OddMincut

namespace OAI

section

namespace BinaryMatching.Algorithm
open Finset
variable {n : ℕ}

abbrev Table (n : ℕ) (α : Type) := Vector (Vector α n) n

def tabulate {α : Type} (f : Fin n → Fin n → α) : Table n α :=
  Vector.ofFn (fun i => Vector.ofFn (f i))

def entry {α : Type} (a : Table n α) (e : Pair n) : α := a[e.val.1][e.val.2]

@[simp] theorem at_tabulate {α : Type} (f : Fin n → Fin n → α) (e : Pair n) :
    entry (tabulate f) e=f e.val.1 e.val.2 := by simp [entry,tabulate]

def toTable {α : Type} [Zero α] (f : Pair n → α) : Table n α :=
  tabulate (fun i j => if h : i < j then f ⟨(i,j),h⟩ else 0)

@[simp] theorem at_toTable {α : Type} [Zero α] (f : Pair n → α) (e : Pair n) :
    entry (toTable f) e=f e := by simp [at_tabulate,toTable,e.property]

def capacities (a : Table n ℤ) (i j : Fin n) : ℕ :=
  if i < j then (a[i][j]).toNat else if j < i then (a[j][i]).toNat else 0

def q (n : ℕ) : ℕ := Fintype.card (Pair n)
def K (n : ℕ) : ℕ := Nat.clog 2 (q n)
def B (G : Input) : ℕ := (G.records.map (fun e => Nat.log2 e.multiplicity)).foldl max 0
def L (G : Input) : ℕ := 100*(G.n+B G+1)^3
def A₀ (n : ℕ) : ℕ := 10*n^2
def M₀ (G : Input) : ℕ := q G.n*(K G.n+L G)*(2+A₀ G.n)
def D₀ (G : Input) : ℕ := q G.n*(K G.n+L G+M₀ G)^2

def beta (G : Input) (e : Pair G.n) : ℤ :=
  if multiplicity G e=0 then -(L G:ℤ) else (Nat.log2 (multiplicity G e):ℤ)

structure Piece where
  slope : ℤ
  constant : ℚ
  deriving Inhabited, DecidableEq

def Piece.eval (p : Piece) (t : ℚ) : ℚ := p.slope*t+p.constant

def pieces (k : ℕ) : List Piece :=
  (List.range k).map (fun j => ⟨(j:ℤ)-1,(2:ℚ)⁻¹^j⟩) ++ [⟨k,0⟩]

def selectedPiece (k : ℕ) (t : ℚ) : Piece :=
  ((pieces k).argmin (fun p => p.eval t)).getD ⟨k,0⟩

def psi (k : ℕ) (t : ℚ) : ℚ := (selectedPiece k t).eval t

def slope (k : ℕ) (t : ℚ) : ℤ := (selectedPiece k t).slope

structure Affine (n : ℕ) where
  coeff : Pair n → ℤ
  constant : ℤ

def Affine.eval (a : Affine n) (x : Pair n → ℚ) : ℚ :=
  (∑ e, (a.coeff e:ℚ)*x e)+a.constant

def zeroRow : Affine n := ⟨fun _ => 0,0⟩
def degreeRow (v : Fin n) (positive : Bool) : Affine n :=
  ⟨fun e => if e.val.1=v ∨ e.val.2=v then (if positive then 1 else -1) else 0,
    if positive then -1 else 1⟩
def cutRow (S : Finset (Fin n)) : Affine n :=
  ⟨fun e => if (e.val.1∈S ∧ e.val.2∉S) ∨ (e.val.2∈S ∧ e.val.1∉S) then -1 else 0,1⟩

def activeRows (a : Table n ℤ) : List (Affine n) :=
  zeroRow :: ((List.finRange n).flatMap (fun v => [degreeRow v true,degreeRow v false])) ++
    [cutRow (OddMincut.oddCut (capacities a) univ)]

def coordinates (D : ℕ) (a : Table n ℤ) (e : Pair n) : ℚ := entry a e/(D:ℚ)

def activeRow (D : ℕ) (a : Table n ℤ) : Affine n :=
  ((activeRows a).argmax (fun r => r.eval (coordinates D a))).getD zeroRow

def trialValue (G : Input) (a : Table G.n ℤ) (r : Affine G.n) : ℚ :=
  (∑ e, (psi (K G.n) (coordinates (D₀ G) a e)+(beta G e:ℚ)*coordinates (D₀ G) a e)) -
    (M₀ G:ℚ)*r.eval (coordinates (D₀ G) a)

def gradient (G : Input) (a : Table G.n ℤ) (r : Affine G.n) (e : Pair G.n) : ℤ :=
  slope (K G.n) (coordinates (D₀ G) a e)+beta G e-(M₀ G:ℤ)*r.coeff e

def update (G : Input) (a : Table G.n ℤ) (r : Affine G.n) : Table G.n ℤ :=
  toTable (fun e => min (D₀ G:ℤ) (max 0 (entry a e+gradient G a r e)))

structure State (n : ℕ) where
  numerators : Table n ℤ
  best : Option ℚ

def step (G : Input) (s : State G.n) : State G.n :=
  let r := activeRow (D₀ G) s.numerators
  let value := trialValue G s.numerators r
  ⟨update G s.numerators r, some (s.best.elim value (max value))⟩

def initial (n : ℕ) : State n := ⟨tabulate (fun _ _ => 0),none⟩

def iterate (G : Input) : ℕ → State G.n
  | 0 => initial G.n
  | t+1 => step G (iterate G t)

def R (G : Input) : ℤ := ⌊((iterate G (q G.n*D₀ G)).best).getD 0⌋

def estimate (G : Input) : ℕ :=
  let r := R G
  if r < -10*(G.n:ℤ) then 0 else 2^(r-5*(G.n:ℤ)).toNat

def covered (G : Input) : Finset ℕ :=
  ((G.records.filter (fun e => 0<e.multiplicity)).flatMap (fun e => [e.left,e.right])).toFinset

def rawMultiplicity (G : Input) (i j : ℕ) : ℕ :=
  ((G.records.find? (fun r => r.left=i && r.right=j)).map Record.multiplicity).getD 0

def approximate (G : Input) : ℕ :=
  if G.n=0 then 1 else
  if Odd G.n then 0 else
  if G.n=2 then rawMultiplicity G 0 1 else
  if (covered G).card<G.n then 0 else estimate G

end BinaryMatching.Algorithm
end

end OAI
