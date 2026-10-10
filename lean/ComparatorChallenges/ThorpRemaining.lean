import Mathlib

namespace OAI

universe u v

noncomputable section
open scoped BigOperators
open Filter

namespace Thorp

abbrev Position (d : ℕ) := Fin d → Bool
abbrev State (d : ℕ) := Equiv.Perm (Position d)

def Coins : ℕ → Type
  | 0 => Unit
  | d + 1 => Position d → Bool

instance coinsFintype (d : ℕ) : Fintype (Coins d) := by
  cases d <;> simp only [Coins] <;> infer_instance

instance coinsInhabited (d : ℕ) : Inhabited (Coins d) := by
  cases d <;> simp only [Coins] <;> infer_instance

def pairSwitch (d : ℕ) (c : Position d → Bool) : Equiv.Perm (Bool × Position d) where
  toFun p := (p.1 ^^ c p.2, p.2)
  invFun p := (p.1 ^^ c p.2, p.2)
  left_inv p := by
    rcases p with ⟨b, s⟩
    cases b <;> cases h : c s <;> simp [h]
  right_inv p := by
    rcases p with ⟨b, s⟩
    cases b <;> cases h : c s <;> simp [h]

def rotate (d : ℕ) : State d :=
  Equiv.piCongrLeft (fun _ : Fin d => Bool) (finRotate d).symm

def step : (d : ℕ) → Coins d → State d
  | 0, _ => Equiv.refl _
  | d + 1, c =>
    (((Fin.consEquiv (fun _ : Fin (d + 1) => Bool)).symm.trans
      (pairSwitch d c)).trans
      (Fin.consEquiv (fun _ : Fin (d + 1) => Bool))).trans (rotate (d + 1))

abbrev History (d t : ℕ) := Fin t → Coins d

def run (d t : ℕ) (ω : History d t) : State d :=
  ((List.ofFn fun i : Fin t => step d (ω i)).reverse).prod

def fairMass {Ω : Type u} {α : Type v} [Fintype Ω] (f : Ω → α) (a : α) : ℝ := by
  classical
  exact (∑ ω : Ω, if f ω = a then (1 : ℝ) else 0) / Fintype.card Ω

def law (d t : ℕ) : State d → ℝ := fairMass (run d t)

def uniform (d : ℕ) (_ : State d) : ℝ := 1 / Fintype.card (State d)

def tv {α : Type u} [Fintype α] (μ ν : α → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ a : α, |μ a - ν a|

def distance (d t : ℕ) : ℝ := tv (law d t) (uniform d)

def lawFrom (d t : ℕ) (g₀ : State d) : State d → ℝ :=
  fairMass (fun ω : History d t => run d t ω * g₀)

abbrev LabelList (d k : ℕ) := Fin k ↪ Position d

def coordinateRun (d t : ℕ) (ω : History d t) : State d :=
  (rotate d)⁻¹ ^ t * run d t ω

def images {d k : ℕ} (t : ℕ) (start : State d) (labels : LabelList d k)
    (ω : History d t) : LabelList d k :=
  labels.trans ((coordinateRun d t ω * start).toEmbedding)

def listTV {d k : ℕ} (t : ℕ) (start : State d) (labels : LabelList d k) : ℝ :=
  tv (fairMass (images t start labels)) (fun _ => 1 / Fintype.card (LabelList d k))

def mixingTime (d : ℕ) : ℕ := sInf {t : ℕ | distance d t ≤ 1 / 4}

end Thorp

namespace ThorpNine.Harmonic

namespace Thorp
open scoped BigOperators
open Filter

abbrev Card (d : ℕ) := Fin d → Bool

def switchFun {d : ℕ} (ξ : Card d → Bool) (x : Card (d + 1)) : Card (d + 1) :=
  Fin.cons (Bool.xor (x 0) (ξ (Fin.tail x))) (Fin.tail x)

theorem switchFun_involutive {d : ℕ} (ξ : Card d → Bool) :
    Function.Involutive (switchFun ξ) := by
  intro x
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [switchFun, Fin.cons_zero, Fin.tail_cons]
    cases x 0 <;> cases ξ (Fin.tail x) <;> rfl
  · simp [switchFun, Fin.tail]

def pairSwitch {d : ℕ} (ξ : Card d → Bool) : Equiv.Perm (Card (d + 1)) :=
  { toFun := switchFun ξ
    invFun := switchFun ξ
    left_inv := switchFun_involutive ξ
    right_inv := switchFun_involutive ξ }

end Thorp

namespace Thorp
run_cmd do
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
  let matcherCache := Lean.mkIdent
    (Lean.mkPrivateNameCore `Lean.Meta.Match.Match `Lean.Meta.Match.matcherExt)
  Lean.Elab.Command.elabCommand (← `(command|
    run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState $matcherCache env {}))

open scoped BigOperators Classical
def Coins : ℕ → Type
  | 0 => Unit
  | d + 1 => Card d → Bool

instance (d : ℕ) : Fintype (Coins d) := by
  cases d <;> dsimp [Coins] <;> infer_instance

instance (d : ℕ) : Nonempty (Coins d) := by
  cases d <;> dsimp [Coins] <;> infer_instance

def rotate (d : ℕ) : Equiv.Perm (Card d) where
  toFun x i := x (finRotate d i)
  invFun x i := x ((finRotate d).symm i)
  left_inv x := by funext i; simp only [Equiv.apply_symm_apply]
  right_inv x := by funext i; simp only [Equiv.symm_apply_apply]

def step : (d : ℕ) → Coins d → Equiv.Perm (Card d)
  | 0, _ => 1
  | d + 1, ξ => rotate (d + 1) * pairSwitch ξ

def run (d : ℕ) : (t : ℕ) → (Fin t → Coins d) → Equiv.Perm (Card d)
  | 0, _ => 1
  | t + 1, ω => step d (ω (Fin.last t)) * run d t (fun i => ω i.castSucc)

noncomputable def law (d t : ℕ) (g : Equiv.Perm (Card d)) : ℝ :=
  (Fintype.card {ω : Fin t → Coins d // run d t ω = g} : ℝ) /
    (Fintype.card (Fin t → Coins d) : ℝ)

lemma card_positions (d : ℕ) : Fintype.card (Card d) = 2 ^ d := by
  simp [Card]

end Thorp
namespace Thorp.Specht
open scoped BigOperators Classical

abbrev Cell (μ : YoungDiagram) := {x : ℕ × ℕ // x ∈ μ.cells}

def row {μ : YoungDiagram} (x : Cell μ) : ℕ := x.1.1

def col {μ : YoungDiagram} (x : Cell μ) : ℕ := x.1.2

lemma row_lt_colLen {μ : YoungDiagram} (x : Cell μ) : row x < μ.colLen (col x) :=
  YoungDiagram.mem_iff_lt_colLen.mp x.2

noncomputable def rowIndex {μ : YoungDiagram} (x : Cell μ) : Fin (μ.colLen 0) :=
  ⟨row x, (row_lt_colLen x).trans_le (μ.colLen_anti 0 (col x) (Nat.zero_le _))⟩

abbrev Tabloid (μ : YoungDiagram) :=
  {f : Cell μ → Fin (μ.colLen 0) // ∃ p : Equiv.Perm (Cell μ), f = rowIndex ∘ p}

noncomputable instance (μ : YoungDiagram) : Fintype (Tabloid μ) := Fintype.ofFinite _

noncomputable def baseTabloid (μ : YoungDiagram) : Tabloid μ := ⟨rowIndex, 1, rfl⟩

noncomputable def tabloidAct {μ : YoungDiagram} (p : Equiv.Perm (Cell μ)) :
    Equiv.Perm (Tabloid μ) where
  toFun f := ⟨fun x => f.1 (p⁻¹ x), by
    obtain ⟨q,hq⟩ := f.2
    refine ⟨q*p⁻¹, ?_⟩
    funext x
    simp only [hq,Function.comp_apply,Equiv.Perm.mul_apply]⟩
  invFun f := ⟨fun x => f.1 (p x), by
    obtain ⟨q,hq⟩ := f.2
    refine ⟨q*p, ?_⟩
    funext x
    simp only [hq,Function.comp_apply,Equiv.Perm.mul_apply]⟩
  left_inv f := by apply Subtype.ext; funext x; simp
  right_inv f := by apply Subtype.ext; funext x; simp

@[simp] lemma tabloidAct_apply {μ : YoungDiagram} (p : Equiv.Perm (Cell μ))
    (f : Tabloid μ) (x : Cell μ) : (tabloidAct p f).1 x = f.1 (p⁻¹ x) := rfl

@[simp] lemma tabloidAct_one (μ : YoungDiagram) : tabloidAct (1 : Equiv.Perm (Cell μ)) = 1 := by
  ext f x
  rfl

@[simp] lemma tabloidAct_mul {μ : YoungDiagram} (p q : Equiv.Perm (Cell μ)) :
    tabloidAct (p*q) = tabloidAct p * tabloidAct q := by
  ext f x
  simp only [tabloidAct_apply, mul_inv_rev,Equiv.Perm.mul_apply]

noncomputable def tabloidRep (μ : YoungDiagram) :
    Representation ℂ (Equiv.Perm (Cell μ)) (Tabloid μ → ℂ) where
  toFun p :=
    { toFun := fun v f => v (tabloidAct p⁻¹ f)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext v f; simp
  map_mul' p q := by
    ext v f
    simp only [mul_inv_rev,tabloidAct_mul,Equiv.Perm.mul_apply]
    rfl

noncomputable def delta {μ : YoungDiagram} (f : Tabloid μ) : Tabloid μ → ℂ :=
  fun g => if g=f then 1 else 0

noncomputable def colGroup (μ : YoungDiagram) : Subgroup (Equiv.Perm (Cell μ)) where
  carrier := {p | ∀ x, col (p x) = col x}
  one_mem' := by intro x; rfl
  mul_mem' := by intro p q hp hq x; exact (hp (q x)).trans (hq x)
  inv_mem' := by intro p hp x; simpa using (hp (p⁻¹ x)).symm

noncomputable def permSign {α : Type*} [Fintype α] [DecidableEq α] (p : Equiv.Perm α) : ℂ :=
  ((Equiv.Perm.sign p : ℤ) : ℂ)

section
variable {α V : Type*} [Fintype α] [DecidableEq α] [AddCommGroup V] [Module ℂ V]

noncomputable def alternator (C : Subgroup (Equiv.Perm α))
    (ρ : Representation ℂ (Equiv.Perm α) V) : Module.End ℂ V := by
  classical
  exact ∑ c : C, permSign (c : Equiv.Perm α) • ρ c

end

noncomputable def polytabloid (μ : YoungDiagram) : Tabloid μ → ℂ :=
  alternator (colGroup μ) (tabloidRep μ) (delta (baseTabloid μ))

noncomputable def space (μ : YoungDiagram) : Submodule ℂ (Tabloid μ → ℂ) :=
  Submodule.span ℂ (Set.range (fun p : Equiv.Perm (Cell μ) => tabloidRep μ p (polytabloid μ)))

lemma orbit_mem_space (μ : YoungDiagram) (p : Equiv.Perm (Cell μ)) :
    tabloidRep μ p (polytabloid μ) ∈ space μ := Submodule.subset_span ⟨p,rfl⟩

lemma action_mem_space (μ : YoungDiagram) (p : Equiv.Perm (Cell μ))
    (v : Tabloid μ → ℂ) (hv : v ∈ space μ) : tabloidRep μ p v ∈ space μ := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨q,rfl⟩ := hv
    change ((tabloidRep μ p)*(tabloidRep μ q)) (polytabloid μ) ∈ space μ
    rw [←map_mul]
    exact orbit_mem_space μ (p*q)
  | zero => simp
  | add v w hv hw ihv ihw => simpa using (space μ).add_mem ihv ihw
  | smul a v hv ih => simpa using (space μ).smul_mem a ih

noncomputable def subrepresentation (μ : YoungDiagram) : Subrepresentation (tabloidRep μ) :=
  ⟨space μ, fun p v hv => action_mem_space μ p v hv⟩

noncomputable def representation (μ : YoungDiagram) :
    Representation ℂ (Equiv.Perm (Cell μ)) (space μ) :=
  (subrepresentation μ).toRepresentation

end Thorp.Specht

namespace Thorp.PermutationHilbert
open scoped BigOperators ComplexConjugate Classical
open Complex
variable {X : Type*} [Fintype X]

abbrev H (X : Type*) [Fintype X] := EuclideanSpace ℂ X

end Thorp.PermutationHilbert

namespace Thorp.Specht
open scoped BigOperators Classical

noncomputable def hilbertEquiv (μ : YoungDiagram) :
    (Tabloid μ → ℂ) ≃ₗ[ℂ] PermutationHilbert.H (Tabloid μ) :=
  (WithLp.linearEquiv 2 ℂ (Tabloid μ → ℂ)).symm

noncomputable def hilbertSpace (μ : YoungDiagram) :
    Submodule ℂ (PermutationHilbert.H (Tabloid μ)) := (space μ).map (hilbertEquiv μ).toLinearMap

end Thorp.Specht

namespace Thorp.UnitaryFinite

section
open scoped BigOperators ComplexConjugate Classical
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

noncomputable def continuousRepresentation (ρ : Representation ℂ G V) : G →* (V →L[ℂ] V) where
  toFun g := (ρ g).toContinuousLinearMap
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

end
open scoped BigOperators Classical
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

noncomputable def sampleOperator (ρ : Representation ℂ G V) (P : Ω → G) : V →L[ℂ] V :=
  (Fintype.card Ω:ℂ)⁻¹ • ∑ ω,continuousRepresentation ρ (P ω)

end Thorp.UnitaryFinite

namespace Thorp.Specht
open scoped BigOperators Classical

noncomputable def spaceHilbertEquiv (μ : YoungDiagram) : space μ ≃ₗ[ℂ] hilbertSpace μ :=
  (hilbertEquiv μ).submoduleMap (space μ)

noncomputable def unitaryRepresentation (μ : YoungDiagram) :
    Representation ℂ (Equiv.Perm (Cell μ)) (hilbertSpace μ) :=
  ((spaceHilbertEquiv μ).conjAlgEquiv ℂ).toMonoidHom.comp (representation μ)

variable {α ι : Type*} [Fintype α] [Fintype ι]

noncomputable def relabelledUnitary (μ : YoungDiagram) (e : α ≃ Cell μ) :
    Representation ℂ (Equiv.Perm α) (hilbertSpace μ) :=
  (unitaryRepresentation μ).comp e.permCongrHom.toMonoidHom

end Thorp.Specht

namespace Thorp.Specht
open scoped BigOperators Classical
@[simp] lemma card_cell (μ : YoungDiagram) : Fintype.card (Cell μ) = μ.card := by
  simp [Cell, YoungDiagram.card]

noncomputable def cellRowsEquiv (μ : YoungDiagram) :
    Cell μ ≃ (i : Fin (μ.colLen 0)) × Fin (μ.rowLen i) where
  toFun x := ⟨rowIndex x,⟨col x,YoungDiagram.mem_iff_lt_rowLen.mp x.2⟩⟩
  invFun p := ⟨(p.1,p.2),YoungDiagram.mem_iff_lt_rowLen.mpr p.2.2⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv p := by rcases p with ⟨⟨i,hi⟩,⟨j,hj⟩⟩; rfl

lemma card_eq_sum_rowLen (μ : YoungDiagram) : μ.card = ∑ i : Fin (μ.colLen 0), μ.rowLen i := by
  rw [←card_cell,Fintype.card_congr (cellRowsEquiv μ),Fintype.card_sigma]
  simp only [Fintype.card_fin]

lemma sum_rowLens (μ : YoungDiagram) : μ.rowLens.sum = μ.card := by
  rw [card_eq_sum_rowLen,YoungDiagram.rowLens]
  rw [Fin.sum_univ_eq_sum_range]
  have hh (n : ℕ) : (List.map μ.rowLen (List.range n)).sum = ∑ i ∈ Finset.range n, μ.rowLen i := by
    induction n with
    | zero => simp
    | succ n ih => simp [List.range_succ,List.map_append,Finset.sum_range_succ,ih]
  exact hh _

noncomputable def diagramPartition (μ : YoungDiagram) : Nat.Partition μ.card where
  parts := μ.rowLens
  parts_pos := fun {i} hi => μ.pos_of_mem_rowLens i (by simpa using hi)
  parts_sum := by simp

noncomputable def partitionDiagram {N : ℕ} (p : Nat.Partition N) : YoungDiagram :=
  YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·)) (Multiset.pairwise_sort _ _).sortedGE

lemma partitionDiagram_rowLens {N : ℕ} (p : Nat.Partition N) :
    (partitionDiagram p).rowLens = p.parts.sort (· ≥ ·) := by
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  intro x hx
  exact p.parts_pos ((Multiset.mem_sort _).mp hx)

lemma partitionDiagram_card {N : ℕ} (p : Nat.Partition N) : (partitionDiagram p).card = N := by
  rw [←sum_rowLens,partitionDiagram_rowLens]
  change (↑(p.parts.sort (· ≥ ·)) : Multiset ℕ).sum = N
  rw [Multiset.sort_eq,p.parts_sum]

lemma partitionDiagram_diagramPartition (μ : YoungDiagram) :
    partitionDiagram (diagramPartition μ) = μ := by
  apply YoungDiagram.equivListRowLens.injective
  apply Subtype.ext
  change (partitionDiagram (diagramPartition μ)).rowLens = μ.rowLens
  rw [partitionDiagram_rowLens]
  change (↑μ.rowLens : Multiset ℕ).sort (· ≥ ·) = μ.rowLens
  rw [Multiset.coe_sort,List.mergeSort_eq_self _ μ.rowLens_sorted.pairwise]

abbrev Shapes (N : ℕ) := {μ : YoungDiagram // μ.card = N}

noncomputable def shapePartitionEquiv (N : ℕ) : Shapes N ≃ Nat.Partition N where
  toFun μ := { parts := μ.1.rowLens
               parts_pos := fun {i} hi => μ.1.pos_of_mem_rowLens i (by simpa using hi)
               parts_sum := by simpa using (sum_rowLens μ.1).trans μ.2 }
  invFun p := ⟨partitionDiagram p,partitionDiagram_card p⟩
  left_inv μ := by
    apply Subtype.ext
    obtain ⟨μ,rfl⟩ := μ
    exact partitionDiagram_diagramPartition μ
  right_inv p := by
    apply Nat.Partition.ext
    change ((partitionDiagram p).rowLens : Multiset ℕ) = p.parts
    rw [partitionDiagram_rowLens,Multiset.sort_eq]

noncomputable instance (N : ℕ) : Fintype (Shapes N) := Fintype.ofEquiv _ (shapePartitionEquiv N).symm

noncomputable def labels {N : ℕ} (μ : Shapes N) : Cell μ.1 ≃ Fin N :=
  (Fintype.equivFin (Cell μ.1)).trans (finCongr ((card_cell μ.1).trans μ.2))

noncomputable def cardLabels (d : ℕ) (μ : Shapes (2^d)) : Card d ≃ Cell μ.1 :=
  ((Fintype.equivFin (Card d)).trans (finCongr (card_positions d))).trans (labels μ).symm

noncomputable def cardRepresentation (d : ℕ) (μ : Shapes (2^d)) :
    Representation ℂ (Equiv.Perm (Card d)) (hilbertSpace μ.1) :=
  relabelledUnitary μ.1 (cardLabels d μ)

end Thorp.Specht
namespace Thorp.LowPlanes
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

open scoped BigOperators Classical
open Specht UnitaryFinite

noncomputable local instance hsNorm (μ : YoungDiagram) : NormedAddCommGroup (hilbertSpace μ) := inferInstance
noncomputable local instance hsInner (μ : YoungDiagram) : InnerProductSpace ℂ (hilbertSpace μ) := inferInstance
noncomputable local instance hsFinite (μ : YoungDiagram) : FiniteDimensional ℂ (hilbertSpace μ) := inferInstance

noncomputable def Q (d : ℕ) (μ : Shapes (2^d)) :
    hilbertSpace μ.1 →L[ℂ] hilbertSpace μ.1 :=
  sampleOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) (run d d)

noncomputable def absoluteTrace {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (A : V →L[ℂ] V) (P : ℝ) : ℝ :=
  (LinearMap.trace ℂ V (CFC.rpow (CFC.sqrt (star A * A)) P).toLinearMap).re

noncomputable def regularTrace (d : ℕ) (P : ℝ) : ℝ :=
  ∑ μ : Shapes (2^d), (Module.finrank ℂ (hilbertSpace μ.1) : ℝ) *
    absoluteTrace (V := hilbertSpace μ.1) (Q d μ) P

noncomputable def sweepDistance (d v : ℕ) (σ : Equiv.Perm (Card d)) : ℝ :=
  (1/2:ℝ) * ∑ g : Equiv.Perm (Card d),
    |law d (v*d) (g*σ⁻¹) - 1/(Nat.factorial (2^d):ℝ)|

end Thorp.LowPlanes
end ThorpNine.Harmonic

namespace ThorpNine.Harmonic.Thorp.LowPlanes
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

open scoped BigOperators
open Specht UnitaryFinite
attribute [local instance] hsNorm hsInner hsFinite
def weightedMoment (d r : ℕ) (μ : Shapes (2 ^ d)) : ℝ :=
  (Module.finrank ℂ (hilbertSpace μ.1) : ℝ) *
    (LinearMap.trace ℂ (hilbertSpace μ.1)
      ((star (Q d μ) * Q d μ) ^ r).toLinearMap).re

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

def signedEntropy (α β : YoungDiagram) : ℝ :=
  (∑ x : Cell α, Real.log ((α.card + β.card : ℕ) / (α.rowLen (row x) : ℝ))) +
  (∑ x : Cell β, Real.log ((α.card + β.card : ℕ) / (β.rowLen (row x) : ℝ)))

def budgetCoefficient (a : ℝ) (d : ℕ) : ℝ :=
  a * (1 - 1 / (2 * Real.sqrt d))

def remainderBudget (κ : ℝ) (d l : ℕ) : ℝ :=
  if l = 0 then 0 else
    max 0 (budgetCoefficient κ d * l * Real.log (2 ^ d : ℝ) -
      l * Real.log ((2 ^ d : ℝ) / l))

def logWeightedMoment (d r : ℕ) (μ : Shapes (2 ^ d)) : EReal :=
  (ENNReal.ofReal (weightedMoment d r μ)).log

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

def densityL2Squared (d t : ℕ) : ℝ :=
  (Nat.factorial (2 ^ d) : ℝ) * ∑ g : Equiv.Perm (Card d),
    (law d t g - 1 / (Nat.factorial (2 ^ d) : ℝ)) ^ 2

def densityL2SquaredFrom (d t : ℕ) (σ : Equiv.Perm (Card d)) : ℝ :=
  (Nat.factorial (2 ^ d) : ℝ) * ∑ g : Equiv.Perm (Card d),
    (law d t (g * σ⁻¹) - 1 / (Nat.factorial (2 ^ d) : ℝ)) ^ 2

end ThorpNine.Harmonic.Thorp.LowPlanes

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

namespace ThorpResults
open ThorpNine.Harmonic.Thorp
open ThorpNine.Harmonic.Thorp.Specht
open ThorpNine.Harmonic.Thorp.LowPlanes

attribute [local instance] hsNorm hsInner hsFinite

def FrameMain : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ d : ℕ in atTop, ∀ start : _root_.OAI.Thorp.State d,
    _root_.OAI.Thorp.tv (_root_.OAI.Thorp.lawFrom d (32800 * d) start) (_root_.OAI.Thorp.uniform d) < ε

def InformationMain : Prop :=
  (∀ ε : ℝ, 0 < ε → ∀ᶠ d : ℕ in atTop,
    ∀ k : ℕ, 8 * k ≤ 7 * 2 ^ d →
    ∀ (start : _root_.OAI.Thorp.State d) (labels : _root_.OAI.Thorp.LabelList d k),
      _root_.OAI.Thorp.listTV (256 * d) start labels < ε) ∧
  (∀ᶠ d : ℕ in atTop,
    ∀ k : ℕ, 16 * k ≤ 15 * 2 ^ d →
    ∀ (start : _root_.OAI.Thorp.State d) (labels : _root_.OAI.Thorp.LabelList d k),
      _root_.OAI.Thorp.listTV (1024 * d) start labels ≤
        Real.rpow ((2 : ℝ) ^ d) (-(3 : ℝ) / 2)) ∧
  (Tendsto (fun d : ℕ => _root_.OAI.Thorp.distance d (2048 * d)) atTop (nhds 0) ∧
    ∀ (d : ℕ) (start : _root_.OAI.Thorp.State d),
      _root_.OAI.Thorp.tv (_root_.OAI.Thorp.lawFrom d (2048 * d) start) (_root_.OAI.Thorp.uniform d) =
        _root_.OAI.Thorp.distance d (2048 * d))

def SpectrumMain : Prop :=
  ∃ p : ℝ, 0 < p ∧ ∀ d : ℕ, 1 ≤ d →
    regularTrace d (2 * p) ≤ 1 + 1 / 16 ∧
    ∀ M : ℕ, p ≤ M → ∀ σ : Equiv.Perm (Card d), sweepDistance d M σ ≤ 1 / 8

def SignedMain : Prop :=
  ∀ η κ : ℝ, 0 < η → ∃ r : ℕ, 1 ≤ r ∧ ∀ d : ℕ, 1 ≤ d →
    ∀ (μ : Shapes (2 ^ d)) (α β γ : YoungDiagram),
      α.card + β.card + γ.card = 2 ^ d →
      logWeightedMoment d r μ ≤
        ((budgetCoefficient η d * signedEntropy α β +
          remainderBudget κ d γ.card : ℝ) : EReal)

def DegreeSavingMain : Prop :=
  ∃ r : ℕ, Even r ∧ 2 ≤ r ∧ ∃ η : ℝ, 0 < η ∧
    ∀ d (μ : Shapes (2 ^ d)),
      (Module.finrank ℂ (hilbertSpace μ.1) : ℝ) *
        (LinearMap.trace ℂ (hilbertSpace μ.1)
          ((Q d μ * star (Q d μ)) ^ r).toLinearMap).re ≤
        (Module.finrank ℂ (hilbertSpace μ.1) : ℝ) ^ (1 - η)

def FullDensityMain : Prop :=
  ∃ v : ℕ, 1 ≤ v ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ d : ℕ in atTop,
    ∀ σ : Equiv.Perm (Card d), densityL2SquaredFrom d (v * d) σ < ε

def ForwardMixingMain : Prop :=
  ∃ v : ℕ, 1 ≤ v ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ d : ℕ in atTop,
    ∀ σ : Equiv.Perm (Card d), sweepDistance d v σ < ε

def OptimalOrderMain : Prop :=
  Asymptotics.IsTheta atTop (fun d : ℕ => (_root_.OAI.Thorp.mixingTime d : ℝ))
    (fun d : ℕ => Real.log (2 ^ d : ℝ))

end ThorpResults

namespace ThorpResults
theorem remaining_main :
    FrameMain ∧ InformationMain ∧ SpectrumMain ∧ SignedMain ∧
      DegreeSavingMain ∧ FullDensityMain ∧ ForwardMixingMain ∧ OptimalOrderMain := by
  sorry
end ThorpResults
end

end OAI
