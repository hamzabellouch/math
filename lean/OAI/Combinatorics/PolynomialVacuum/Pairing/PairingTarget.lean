import OAI.Combinatorics.PolynomialVacuum.Algebra.Target

namespace OAI

namespace PolynomialVacuumCylinder
open PolynomialVacuumAlgebra

inductive Vertex (L : ℕ) where
  | up (i : ZMod L) (j : ℤ)
  | down (i : ZMod L) (j : ℤ)
  deriving DecidableEq

abbrev Germ (L : ℕ) := Vertex L × Fin 3
abbrev Face (L : ℕ) := ZMod L × ℤ
abbrev Edge (L : ℕ) := Face L × Fin 3

def neighbor {L : ℕ} (v : Vertex L) (k : Fin 3) : Vertex L :=
  match v with
  | .up i j => if k=0 then .down i (j-1) else if k=1 then .down i j else .down (i-1) j
  | .down i j => if k=0 then .up i (j+1) else if k=1 then .up i j else .up (i+1) j

def edgeOf {L : ℕ} : Germ L → Edge L
  | (.up i j,k) => ((i,j),k)
  | (.down i j,k) => if k=0 then ((i,j+1),k) else if k=1 then ((i,j),k) else ((i+1,j),k)

def edgeVertices {L : ℕ} (e : Edge L) : Finset (Vertex L) :=
  {.up e.1.1 e.1.2, neighbor (.up e.1.1 e.1.2) e.2}

def outgoingSlot {L : ℕ} (g : Germ L) (b : Bool) : Fin 3 := g.2+(if b then 2 else 1)
def advance {L : ℕ} (g : Germ L) (b : Bool) : Germ L :=
  (neighbor g.1 (outgoingSlot g b),outgoingSlot g b)

def traced {L : ℕ} : Germ L → List Bool → List (Vertex L)
  | _,[] => []
  | g,b::w => g.1::traced (advance g b) w

def terminalGerm {L : ℕ} : Germ L → List Bool → Germ L
  | g,[] => g
  | g,b::w => terminalGerm (advance g b) w

def tracedEdges {L : ℕ} : Germ L → List Bool → Finset (Edge L)
  | _,[] => ∅
  | g,b::w => insert (edgeOf (g.1,outgoingSlot g b)) (tracedEdges (advance g b) w)

def IsPolygon {L : ℕ} (E : Finset (Edge L)) : Prop := ∃ (g : Germ L) (w : List Bool),
  w≠[] ∧ (traced g w).Nodup ∧ terminalGerm g w=g ∧ tracedEdges g w=E
abbrev Polygon (L : ℕ) := {E : Finset (Edge L) // IsPolygon E}

def Polygon.vertices {L : ℕ} (P : Polygon L) : Finset (Vertex L) := P.val.biUnion edgeVertices

def leftFace {L : ℕ} : Germ L → Face L
  | (.up i j,k) => if k=0 then (i,j) else if k=1 then (i-1,j+1) else (i-1,j)
  | (.down i j,k) => if k=0 then (i-1,j+1) else if k=1 then (i,j) else (i,j+1)

def reverseGerm {L : ℕ} (g : Germ L) : Germ L := (neighbor g.1 g.2,g.2)
def rightFace {L : ℕ} (g : Germ L) : Face L := leftFace (reverseGerm g)

def DualAdjacent {L : ℕ} (E : Finset (Edge L)) (a b : Face L) : Prop :=
  ∃ e : Edge L, e∉E ∧
    ((leftFace (.up e.1.1 e.1.2,e.2)=a ∧ rightFace (.up e.1.1 e.1.2,e.2)=b) ∨
     (leftFace (.up e.1.1 e.1.2,e.2)=b ∧ rightFace (.up e.1.1 e.1.2,e.2)=a))

def Separates {L : ℕ} (P : Polygon L) (a b : Face L) : Prop :=
  ¬ Relation.ReflTransGen (DualAdjacent P.val) a b

def AllowedSystem (n : ℕ) (S : Finset (Polygon (2*n))) : Prop :=
  (∀ P∈S, Separates P (0,0) ((n : ZMod (2*n)),0)) ∧
  (S : Set (Polygon (2*n))).Pairwise (fun P Q => Disjoint P.vertices Q.vertices)
abbrev System (n : ℕ) := {S : Finset (Polygon (2*n)) // AllowedSystem n S}

noncomputable def systemWeight {n : ℕ} (η : ℂ) (S : System n) : ℂ :=
  η^S.val.card * xStar^(∑ P∈S.val, P.vertices.card)
noncomputable def separatorPolynomial (n : ℕ) (η : ℂ) : ℂ := ∑' S : System n, systemWeight η S

noncomputable def emptyCoefficient (ψ : Family) (N : ℕ) : ℂ :=
  MvPolynomial.eval (fun _ => 1) (ψ N (fun _ => Spin.zero))
noncomputable def normalizedState (ψ : Family) (N : ℕ) (s : Fin N → Spin) : ℂ :=
  MvPolynomial.eval (fun _ => 1) (ψ N s) / emptyCoefficient ψ N
noncomputable def blockCharge (n : ℕ) (s : Fin (2*n) → Spin) : ℤ :=
  ∑ j : Fin n, charge (s ⟨j.val,by omega⟩)
noncomputable def homogeneousContraction (ψ : Family) (n : ℕ) (κ : ℂ) : ℂ :=
  ∑ s : Fin (2*n) → Spin,
    normalizedState ψ (2*n) s * (κ/zeta)^blockCharge n s * normalizedState ψ (2*n) s

 

abbrev AnalyticFamily := (N : ℕ) → (Fin N → ℂ) → (Fin N → Spin) → ℂ

def AnalyticNormalization (ψ : Family) (Ω : AnalyticFamily) : Prop :=
  (∀ N, ψ N (fun _ => Spin.zero) ≠ 0) ∧
  (∀ N s, AnalyticAt ℂ (fun X => Ω N X s) (fun _ => 1)) ∧
  (∀ N s, ∀ᶠ X in nhds (fun _ : Fin N => (1 : ℂ)),
    MvPolynomial.eval X (ψ N (fun _ => Spin.zero)) ≠ 0 →
      Ω N X s = MvPolynomial.eval X (ψ N s) /
        MvPolynomial.eval X (ψ N (fun _ => Spin.zero))) ∧
  (∀ N, Ω N (fun _ => 1) (fun _ => Spin.zero) = 1)

noncomputable def analyticHomogeneousContraction (Ω : AnalyticFamily)
    (n : ℕ) (κ : ℂ) : ℂ :=
  ∑ s : Fin (2*n) → Spin,
    Ω (2*n) (fun _ => 1) s * (κ/zeta)^blockCharge n s * Ω (2*n) (fun _ => 1) s

 

def PhysicalSeparatorPairing : Prop := ∃ (ψ : Family) (Ω : AnalyticFamily),
  IsPolynomialVacuum ψ ∧ AnalyticNormalization ψ Ω ∧
  (∀ n, 1≤n → ∀ η : ℂ, Summable (systemWeight (n:=n) η)) ∧
  (∀ n, 1≤n → ∀ κ : ℂ, κ≠0 →
    analyticHomogeneousContraction Ω n κ=separatorPolynomial n (κ+κ⁻¹))

end PolynomialVacuumCylinder

end OAI
