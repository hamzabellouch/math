import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.Source
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.Extraction
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.InverseLinearRecovery
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.Replication
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.TerminalProducts

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldFiniteFamily

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

variable {F : Type*} [Field F]

structure LocalMap {X Y Z X' Y' Z' : Type}
    [Fintype X] [Fintype Y] [Fintype Z]
    (source : Tensor F X Y Z) (target : Tensor F X' Y' Z') where
  x : X' → X → F
  y : Y' → Y → F
  z : Z' → Z → F
  coefficient : Tensor.restrict x y z source = target

namespace LocalMap

variable {X Y Z X' Y' Z' X'' Y'' Z'' : Type}
  [Fintype X] [Fintype Y] [Fintype Z]
  [Fintype X'] [Fintype Y'] [Fintype Z']
  {source : Tensor F X Y Z} {middle : Tensor F X' Y' Z'}
  {target : Tensor F X'' Y'' Z''}

def identity (source : Tensor F X Y Z) : LocalMap source source where
  x := fun x s => if s = x then 1 else 0
  y := fun y s => if s = y then 1 else 0
  z := fun z s => if s = z then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    rfl

def delete (source : Tensor F X Y Z) (px : X → Prop) (py : Y → Prop) (pz : Z → Prop) :
    LocalMap source (ExactRecovery.delete source px py pz) where
  x := fun x s => if s = x ∧ px x then 1 else 0
  y := fun y s => if s = y ∧ py y then 1 else 0
  z := fun z s => if s = z ∧ pz z then 1 else 0
  coefficient := by
    funext x y z
    by_cases hx : px x <;> by_cases hy : py y <;> by_cases hz : pz z <;>
      simp [Tensor.restrict, ExactRecovery.delete, hx, hy, hz, ite_mul, mul_ite]

def product {U V W U' V' W' : Type}
    [Fintype U] [Fintype V] [Fintype W]
    {other : Tensor F U V W} {otherTarget : Tensor F U' V' W'}
    (first : LocalMap source middle) (second : LocalMap other otherTarget) :
    LocalMap (Tensor.product source other) (Tensor.product middle otherTarget) where
  x := fun x s => first.x x.1 s.1 * second.x x.2 s.2
  y := fun y s => first.y y.1 s.1 * second.y y.2 s.2
  z := fun z s => first.z z.1 s.1 * second.z z.2 s.2
  coefficient := by
    rw [Tensor.restrict_product, first.coefficient, second.coefficient]

def comp (first : LocalMap source middle) (second : LocalMap middle target) :
    LocalMap source target where
  x := Tensor.composeRestrictionMatrix second.x first.x
  y := Tensor.composeRestrictionMatrix second.y first.y
  z := Tensor.composeRestrictionMatrix second.z first.z
  coefficient := by
    rw [← Tensor.restrict_restrict, first.coefficient, second.coefficient]

def withSource (map : LocalMap source middle) (newSource : Tensor F X Y Z)
    (same : newSource = source) : LocalMap newSource middle where
  x := map.x
  y := map.y
  z := map.z
  coefficient := by rw [same]; exact map.coefficient

def ofExists
    (h : ∃ (a : X' → X → F) (b : Y' → Y → F) (c : Z' → Z → F),
      Tensor.restrict a b c source = middle) : LocalMap source middle := by
  choose a b c habc using h
  exact ⟨a, b, c, habc⟩

def parallelCopies (map : LocalMap source middle) (R : Type) [Fintype R] :
    LocalMap (Tensor.directSum (fun _ : R => source))
      (Tensor.directSum (fun _ : R => middle)) where
  x := fun x s => if x.1 = s.1 then map.x x.2 s.2 else 0
  y := fun y s => if y.1 = s.1 then map.y y.2 s.2 else 0
  z := fun z s => if z.1 = s.1 then map.z z.2 s.2 else 0
  coefficient := by
    have h := Replication.restrict_directSum (fun _ : R => source)
      (fun _ => map.x) (fun _ => map.y) (fun _ => map.z)
    simpa only [map.coefficient] using h

def directSum {I : Type} [Fintype I]
    (T : I → Tensor F X Y Z) (Q : I → Tensor F X' Y' Z')
    (maps : ∀ i, LocalMap (T i) (Q i)) :
    LocalMap (Tensor.directSum T) (Tensor.directSum Q) where
  x := fun x s => if x.1 = s.1 then (maps x.1).x x.2 s.2 else 0
  y := fun y s => if y.1 = s.1 then (maps y.1).y y.2 s.2 else 0
  z := fun z s => if z.1 = s.1 then (maps z.1).z z.2 s.2 else 0
  coefficient := by
    have h := Replication.restrict_directSum T
      (fun i => (maps i).x) (fun i => (maps i).y) (fun i => (maps i).z)
    simpa only [fun i => (maps i).coefficient] using h

def selectBranches {I J : Type} [Fintype I] [Fintype J]
    (T : I → Tensor F X Y Z) (select : J → I) (injective : Function.Injective select) :
    LocalMap (Tensor.directSum T) (Tensor.directSum (fun j => T (select j))) where
  x := fun x s => if s = (select x.1, x.2) then 1 else 0
  y := fun y s => if s = (select y.1, y.2) then 1 else 0
  z := fun z s => if s = (select z.1, z.2) then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    simp only [Tensor.pullback, Tensor.directSum, injective.eq_iff]

def unflatten (source : Tensor F X Y Z) (R I : Type) [Fintype R] [Fintype I] :
    LocalMap (Tensor.directSum (fun _ : R × I => source))
      (Tensor.directSum (fun _ : R => Tensor.directSum (fun _ : I => source))) where
  x := fun x s => if s = ((x.1, x.2.1), x.2.2) then 1 else 0
  y := fun y s => if s = ((y.1, y.2.1), y.2.2) then 1 else 0
  z := fun z s => if s = ((z.1, z.2.1), z.2.2) then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    simp only [Tensor.pullback, Tensor.directSum, Prod.ext_iff]
    split_ifs <;> aesop

def flatten (source : Tensor F X Y Z) (I J : Type) [Fintype I] [Fintype J] :
    LocalMap (Tensor.directSum (fun _ : I => Tensor.directSum (fun _ : J => source)))
      (Tensor.directSum (fun _ : I × J => source)) where
  x := fun x s => if s = (x.1.1, (x.1.2, x.2)) then 1 else 0
  y := fun y s => if s = (y.1.1, (y.1.2, y.2)) then 1 else 0
  z := fun z s => if s = (z.1.1, (z.1.2, z.2)) then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    simp only [Tensor.pullback, Tensor.directSum, Prod.ext_iff]
    split_ifs <;> aesop

def replicationProduct {U V W : Type} [Fintype U] [Fintype V] [Fintype W]
    (active : Tensor F X Y Z) (finished : Tensor F U V W)
    (R : Type) [Fintype R] :
    LocalMap (Tensor.directSum (fun _ : R => Tensor.product active finished))
      (Tensor.product (Tensor.directSum (fun _ : R => active)) finished) where
  x := fun x s => if s = (x.1.1, (x.1.2, x.2)) then 1 else 0
  y := fun y s => if s = (y.1.1, (y.1.2, y.2)) then 1 else 0
  z := fun z s => if s = (z.1.1, (z.1.2, z.2)) then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    simp [Tensor.pullback, Tensor.directSum, Tensor.product, ite_mul]

def extract (T : Tensor F X Y Z) {I : Type} [Fintype I]
    (assignment : JointExtraction.Assignment X Y Z I)
    (coherent : JointExtraction.Coherent T assignment) :
    LocalMap T (Tensor.directSum (JointExtraction.branch T assignment)) where
  x := JointExtraction.assignmentMatrix assignment.x
  y := JointExtraction.assignmentMatrix assignment.y
  z := JointExtraction.assignmentMatrix assignment.z
  coefficient := JointExtraction.restrict_assignments_eq_directSum T assignment coherent

def repairBranches {I : Type} [Fintype I]
    (T Q : I → Tensor F X Y Z) (L : ℕ)
    (repair : ∀ i, InverseLinearRecovery.RecoveredBy (Q i) (T i) L) :
    LocalMap
      (Tensor.directSum (fun _ : InverseLinearRecovery.MaskRectangles L => Tensor.directSum T))
      (Tensor.directSum Q) := by
  choose a b c h using repair
  exact ofExists (Replication.repair_branches T Q a b c h)

end LocalMap

structure Execution {SX SY SZ X Y Z : Type}
    [Fintype SX] [Fintype SY] [Fintype SZ]
    (source : Tensor F SX SY SZ) (target : Tensor F X Y Z) where
  Copies : Type
  [copies_finite : Fintype Copies]
  copies_positive : 0 < Fintype.card Copies
  map : LocalMap (Tensor.directSum (fun _ : Copies => source)) target

attribute [instance] Execution.copies_finite

namespace Execution

variable {SX SY SZ X Y Z X' Y' Z' : Type}
  [Fintype SX] [Fintype SY] [Fintype SZ]
  [Fintype X] [Fintype Y] [Fintype Z]
  {source : Tensor F SX SY SZ} {current : Tensor F X Y Z}

def initial (source : Tensor F SX SY SZ) : Execution source source where
  Copies := PUnit
  copies_positive := by simp
  map := {
    x := fun x s => if s = (PUnit.unit, x) then 1 else 0
    y := fun y s => if s = (PUnit.unit, y) then 1 else 0
    z := fun z s => if s = (PUnit.unit, z) then 1 else 0
    coefficient := by
      rw [← Tensor.pullback_eq_restrict]
      funext x y z
      simp [Tensor.pullback, Tensor.directSum]
  }

def restrict (E : Execution source current) (target : Tensor F X' Y' Z')
    (map : LocalMap current target) : Execution source target where
  Copies := E.Copies
  copies_positive := E.copies_positive
  map := E.map.comp map

def replicate (E : Execution source current) (R : Type) [Fintype R]
    (positive : 0 < Fintype.card R) :
    Execution source (Tensor.directSum (fun _ : R => current)) where
  Copies := R × E.Copies
  copies_positive := by simpa using Nat.mul_pos positive E.copies_positive
  map := ((LocalMap.unflatten source R E.Copies).comp (E.map.parallelCopies R)).withSource _
    (by funext x y z; simp only [Tensor.directSum])

def step (E : Execution source current) (R : Type) [Fintype R]
    (positive : 0 < Fintype.card R) (target : Tensor F X' Y' Z')
    (map : LocalMap (Tensor.directSum (fun _ : R => current)) target) :
    Execution source target :=
  (E.replicate R positive).restrict target map

def stepOnLeft {U V W : Type} [Fintype U] [Fintype V] [Fintype W]
    (active : Tensor F X Y Z) (finished : Tensor F U V W)
    (E : Execution source (Tensor.product active finished))
    (R : Type) [Fintype R] (positive : 0 < Fintype.card R)
    (target : Tensor F X' Y' Z')
    (map : LocalMap (Tensor.directSum (fun _ : R => active)) target) :
    Execution source (Tensor.product target finished) :=
  E.step R positive _ ((LocalMap.replicationProduct active finished R).comp
    (map.product (LocalMap.identity finished)))

def branchOperation {I J R : Type} [Fintype I] [Fintype J] [Fintype R]
    (current : Tensor F X Y Z) (next : Tensor F X' Y' Z')
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (E : Execution source (Tensor.directSum (fun _ : I => current)))
    (positive : 0 < Fintype.card R)
    (map : LocalMap (Tensor.directSum (fun _ : R => current))
      (Tensor.directSum (fun _ : J => next))) :
    Execution source (Tensor.directSum (fun _ : I × J => next)) :=
  E.step R positive _ ((LocalMap.ofExists
    (Replication.repair_branches (fun _ : I => current)
      (fun _ : I => Tensor.directSum (fun _ : J => next))
      (fun _ => map.x) (fun _ => map.y) (fun _ => map.z)
      (fun _ => map.coefficient))).comp (LocalMap.flatten next I J))

@[simp] theorem branchOperation_copies {I J R : Type}
    [Fintype I] [Fintype J] [Fintype R]
    (current : Tensor F X Y Z) (next : Tensor F X' Y' Z')
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (E : Execution source (Tensor.directSum (fun _ : I => current)))
    (positive : 0 < Fintype.card R)
    (map : LocalMap (Tensor.directSum (fun _ : R => current))
      (Tensor.directSum (fun _ : J => next))) :
    Fintype.card (branchOperation current next E positive map).Copies =
      Fintype.card R * Fintype.card E.Copies := by
  change Fintype.card (R × E.Copies) = _
  exact Fintype.card_prod R E.Copies

@[simp] theorem step_copies (E : Execution source current) (R : Type) [Fintype R]
    (positive : 0 < Fintype.card R) (target : Tensor F X' Y' Z')
    (map : LocalMap (Tensor.directSum (fun _ : R => current)) target) :
    Fintype.card (E.step R positive target map).Copies =
      Fintype.card R * Fintype.card E.Copies := by
  change Fintype.card (R × E.Copies) = _
  exact Fintype.card_prod R E.Copies

def extractAndRepair (E : Execution source current) {I : Type} [Fintype I]
    (assignment : JointExtraction.Assignment X Y Z I)
    (coherent : JointExtraction.Coherent current assignment)
    (ideal : I → Tensor F X Y Z) (L : ℕ)
    (repair : ∀ i, InverseLinearRecovery.RecoveredBy (ideal i)
      (JointExtraction.branch current assignment i) L) :
    Execution source (Tensor.directSum ideal) := by
  let extracted := E.restrict _ (LocalMap.extract current assignment coherent)
  exact extracted.step (InverseLinearRecovery.MaskRectangles L)
    (by simp [InverseLinearRecovery.MaskRectangles]) _
    ((LocalMap.repairBranches (JointExtraction.branch current assignment) ideal L repair).withSource _
      (by funext x y z; simp only [Tensor.directSum]; split_ifs <;> rfl))

@[simp] theorem extractAndRepair_copies (E : Execution source current)
    {I : Type} [Fintype I]
    (assignment : JointExtraction.Assignment X Y Z I)
    (coherent : JointExtraction.Coherent current assignment)
    (ideal : I → Tensor F X Y Z) (L : ℕ)
    (repair : ∀ i, InverseLinearRecovery.RecoveredBy (ideal i)
      (JointExtraction.branch current assignment i) L) :
    Fintype.card (E.extractAndRepair assignment coherent ideal L repair).Copies =
      2 ^ (3 * L) * Fintype.card E.Copies := by
  change Fintype.card (InverseLinearRecovery.MaskRectangles L × E.Copies) = _
  rw [Fintype.card_prod, ExactRecovery.card_mask_rectangles, Fintype.card_fin]

def extractSelectedAndRepair (E : Execution source current)
    {I J : Type} [Fintype I] [Fintype J]
    (assignment : JointExtraction.Assignment X Y Z I)
    (coherent : JointExtraction.Coherent current assignment)
    (select : J → I) (injective : Function.Injective select)
    (ideal : J → Tensor F X Y Z) (L : ℕ)
    (repair : ∀ j, InverseLinearRecovery.RecoveredBy (ideal j)
      (JointExtraction.branch current assignment (select j)) L) :
    Execution source (Tensor.directSum ideal) := by
  let extracted := E.restrict _ (LocalMap.extract current assignment coherent)
  let selected := extracted.restrict _
    (LocalMap.selectBranches (JointExtraction.branch current assignment) select injective)
  exact selected.step (InverseLinearRecovery.MaskRectangles L)
    (by simp [InverseLinearRecovery.MaskRectangles]) _
    ((LocalMap.repairBranches (fun j => JointExtraction.branch current assignment (select j))
      ideal L repair).withSource _
      (by funext x y z; simp only [Tensor.directSum]; split_ifs <;> rfl))

@[simp] theorem extractSelectedAndRepair_copies (E : Execution source current)
    {I J : Type} [Fintype I] [Fintype J]
    (assignment : JointExtraction.Assignment X Y Z I)
    (coherent : JointExtraction.Coherent current assignment)
    (select : J → I) (injective : Function.Injective select)
    (ideal : J → Tensor F X Y Z) (L : ℕ)
    (repair : ∀ j, InverseLinearRecovery.RecoveredBy (ideal j)
      (JointExtraction.branch current assignment (select j)) L) :
    Fintype.card
      (E.extractSelectedAndRepair assignment coherent select injective ideal L repair).Copies =
      2 ^ (3 * L) * Fintype.card E.Copies := by
  change Fintype.card (InverseLinearRecovery.MaskRectangles L × E.Copies) = _
  rw [Fintype.card_prod, ExactRecovery.card_mask_rectangles, Fintype.card_fin]

end Execution

section Schedule

variable {SX SY SZ : Type} [Fintype SX] [Fintype SY] [Fintype SZ]
  {X Y Z : ℕ → Type} [∀ n, Fintype (X n)] [∀ n, Fintype (Y n)] [∀ n, Fintype (Z n)]
  (source : Tensor F SX SY SZ) (tensor : ∀ n, Tensor F (X n) (Y n) (Z n))
  (start : Execution source (tensor 0))
  (Copies : ℕ → Type) [∀ n, Fintype (Copies n)]
  (positive : ∀ n, 0 < Fintype.card (Copies n))
  (maps : ∀ n, LocalMap (Tensor.directSum (fun _ : Copies n => tensor n)) (tensor (n + 1)))

def run : (n : ℕ) → Execution source (tensor n)
  | 0 => start
  | n + 1 => (run n).step (Copies n) (positive n) (tensor (n + 1)) (maps n)

theorem run_copies (n : ℕ) :
    Fintype.card (run source tensor start Copies positive maps n).Copies =
      Fintype.card start.Copies * ∏ j ∈ Finset.range n, Fintype.card (Copies j) := by
  induction n with
  | zero => simp [run]; rfl
  | succ n ih =>
      rw [run, Execution.step_copies, ih, Finset.prod_range_succ]
      ring

end Schedule

section CWSource

variable {K N a b c L : ℕ}

abbrev cwSource (F : Type*) [Field F] (K N : ℕ) :=
  Tensor.power (FieldCW.tensor F 5) (8 * K * N)

def startCW (F : Type*) [Field F] (K N : ℕ) :
    Execution (cwSource F K N) (cwSource F K N) :=
  Execution.initial _

def Execution.toWitness
    (E : Execution (cwSource F K N) (AllFieldSource.matrixTarget F a b c L))
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hL : 0 < L) : AllFieldWitness F :=
  AllFieldSource.ofRestriction E.map.x E.map.y E.map.z
    (fun x y z => congrFun (congrFun (congrFun E.map.coefficient x) y) z)
    E.copies_positive ha hb hc hL

@[simp] theorem Execution.toWitness_rankBound
    (E : Execution (cwSource F K N) (AllFieldSource.matrixTarget F a b c L))
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hL : 0 < L) :
    (E.toWitness ha hb hc hL).rankBound =
      Fintype.card E.Copies * ((3 * (8 * K * N) + 1) ^ 2 * 7 ^ (8 * K * N)) := rfl

end CWSource

end MatrixMultiplication.AllFieldFiniteFamily

end

end OAI
