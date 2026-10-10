import Mathlib
import OAI.CategoryTheory.Thomason.TwoCellComparison

namespace OAI

/-! Prism Basis. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.CylinderTables
open Table OmegaCategory
variable {M : DirectedComplex.{u}}

lemma cylinder_truncated {n : ℕ} (hM : PositiveAcyclic M)
    (hn : M.nu.IsTruncated n) : M.cylinder.nu.IsTruncated (n+1) := by
  intro t
  change truncate (n+1) false t = t
  rcases endpoint_or_crossing hM t with ⟨a, he⟩ | ⟨hs,ht⟩
  · rw [he, ← Hom.table_truncate]
    exact congrArg (M.cylinderEndpoint a).table
      (M.nu.source_fixed_upwards (by omega : n ≤ n+1) (hn (project t)))
  · apply dimension_of_rows_above_zero
    intro p hp b
    have hz (q : ℕ) (hq : n < q) (e : Bool) : cross t q e = 0 :=
      row_above_fixed (crossingProfile t hs ht) (hn _) hq e
    have hl : side t false p b = 0 := by
      have h := row_above_fixed (leftProfile t hs ht) (hn _) (by omega : n < p) b
      change leftProfileRow t p b = 0 at h
      simpa only [leftProfileRow,hz p (by omega) b,ite_self,add_zero] using h
    have hr : side t true p b = 0 := by
      have h := row_above_fixed (rightProfile t hs ht) (hn _) (by omega : n < p) b
      change rightProfileRow t p b = 0 at h
      simpa only [rightProfileRow,hz p (by omega) b,ite_self,add_zero] using h
    cases p with
    | zero => omega
    | succ q => exact Prod.ext hl (Prod.ext hr (hz q (by omega) b))

end Thomason.DirectedComplex.CylinderTables

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex Table OmegaCategory
variable {M : DirectedComplex.{u}}

def chainComparisonOneIso (hM : PositiveAcyclic M) (h₁ : M.nu.IsTruncated 1) :
    tensorFunctor.obj M.nu ≅ M.cylinder.nu := by
  have hs : (tensorFunctor.obj M.nu).IsTruncated 2 := tensor_truncated h₁
  have ht : M.cylinder.nu.IsTruncated 2 := CylinderTables.cylinder_truncated hM h₁
  apply OmegaCategory.isoOfBijective (chainComparison M)
  constructor
  · intro x y h
    exact chainComparison_twocells_injective x y (hs x) (hs y) h
  · intro y
    obtain ⟨x, hx⟩ := (chainComparison_twocells_bijective hM).2 ⟨y,ht y⟩
    exact ⟨x.val,congrArg Subtype.val hx⟩

lemma chainComparisonOneIso_hom (hM : PositiveAcyclic M) (h₁ : M.nu.IsTruncated 1) :
    (chainComparisonOneIso hM h₁).hom = chainComparison M := rfl

lemma chainComparisonOne_isIso (hM : PositiveAcyclic M) (h₁ : M.nu.IsTruncated 1) :
    IsIso (chainComparison M) := (chainComparisonOneIso hM h₁).isIso_hom

lemma chainComparison_posetOne_isIso (P : Type u) [PartialOrder P]
    (h₁ : (NormalizedChains.complex P).nu.IsTruncated 1) :
    IsIso (chainComparison (NormalizedChains.complex P)) :=
  chainComparisonOne_isIso (NormalizedChains.complexPositiveAcyclic P) h₁
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains.Prism
open DirectedComplex DirectedComplex.Table

def Word (N : ℕ) := {w : NormalizedChains.Word (Fin (N+1)) // w.val ≠ []}

namespace Word
variable {N : ℕ}
def dim (w : Word N) : ℕ := w.val.val.length - 1
def rank (w : Word N) : ℤ := simplexRank w.val.val

def atom (w : Word N) : Table (complex (Fin (N+1))) := by
  obtain ⟨⟨l,h⟩,hne⟩ := w
  cases l with
  | nil => exact False.elim (hne rfl)
  | cons a l => exact (simplexAtom a l (h.imp le_of_lt)).table

lemma atom_dim (w : Word N) : truncate w.dim false w.atom = w.atom := by
  obtain ⟨⟨l,h⟩,hne⟩ := w
  cases l with
  | nil => exact False.elim (hne rfl)
  | cons a l => exact (simplexAtom a l (h.imp le_of_lt)).dimension

lemma atom_top (w : Word N) (b : Bool) :
    (w.atom.row w.dim b).val = Finsupp.single w.val 1 := by
  obtain ⟨⟨l,h⟩,hne⟩ := w
  cases l with
  | nil => exact False.elim (hne rfl)
  | cons a l =>
    exact ((simplexAtom a l (h.imp le_of_lt)).top b).trans (bracket_of_pairwise h)

lemma atom_rank (w : Word N) (p : ℕ) (hp : p < w.dim) (b : Bool)
    (v : Word N) (hv : (w.atom.row p b).val v.val ≠ 0) :
    if b then v.rank < w.rank else w.rank < v.rank := by
  obtain ⟨⟨l,h⟩,hne⟩ := w
  cases l with
  | nil => exact False.elim (hne rfl)
  | cons a l => exact simplexAtom_rank a l h p hp b v.val hv

lemma dim_eq_of_coefficient {p : ℕ} (x : (complex (Fin (N+1))).Chain p)
    (w : Word N) (hw : x.val w.val ≠ 0) : w.dim = p := by
  have h := (mem_grade_iff (p+1) x.val).mp x.property w.val hw
  simp only [dim,h,Nat.add_sub_cancel]

lemma atom_top_support (w v : Word N) (b : Bool)
    (h : (w.atom.row w.dim b).val v.val ≠ 0) : v = w := by
  rw [w.atom_top b] at h
  by_contra he
  have hne : w.val ≠ v.val := fun e => he (Subtype.ext e.symm)
  exact h (Finsupp.single_eq_of_ne (Ne.symm hne))

end Word

inductive Basis (N : ℕ)
  | endpoint (a : Bool) (w : Word N)
  | vertical (w : Word N)

namespace Basis
local instance (N : ℕ) : DecidableEq (Basis N) := Classical.decEq _
variable {N : ℕ}

def dim : Basis N → ℕ
  | .endpoint _ w => w.dim
  | .vertical w => w.dim + 1

def endpointOffset (p : ℕ) (a : Bool) : ℤ :=
  if Even p then (if a then -1 else 1) else (if a then 1 else -1)

lemma endpointOffset_bounds (p : ℕ) (a : Bool) :
    -1 ≤ endpointOffset p a ∧ endpointOffset p a ≤ 1 := by
  unfold endpointOffset
  split_ifs <;> omega

def rank : Basis N → ℤ
  | .endpoint a w => 3 * w.rank + endpointOffset w.dim a
  | .vertical w => 3 * w.rank

def atom : Basis N → Table (complex (Fin (N+1))).cylinder
  | .endpoint a w => ((complex (Fin (N+1))).cylinderEndpoint a).table w.atom
  | .vertical w => verticalTable w.atom

def coefficient (b : Basis N) (p : ℕ) :
    (complex (Fin (N+1))).cylinder.Chain p →+ ℤ where
  toFun x := match b, p, x with
    | .endpoint a w, 0, x => if a then x.2.val w.val else x.1.val w.val
    | .endpoint a w, _+1, x => if a then x.2.1.val w.val else x.1.val w.val
    | .vertical _, 0, _ => 0
    | .vertical w, _+1, x => x.2.2.val w.val
  map_zero' := by cases b <;> cases p <;> simp <;> rfl
  map_add' x y := by
    cases b with
    | endpoint a w => cases p <;> cases a <;> rfl
    | vertical w => cases p <;> rfl

lemma coefficient_nonneg (b : Basis N) (p : ℕ)
    (x : (complex (Fin (N+1))).cylinder.Chain p)
    (hx : x ∈ (complex (Fin (N+1))).cylinder.positive p) :
    0 ≤ b.coefficient p x := by
  cases b with
  | endpoint a w =>
    cases p with
    | zero => cases a; exact hx.1 w.val; exact hx.2 w.val
    | succ p => cases a; exact hx.1 w.val; exact hx.2.1 w.val
  | vertical w =>
    cases p with
    | zero => exact le_rfl
    | succ p => exact hx.2.2 w.val

lemma coefficient_endpoint (b : Basis N) (p : ℕ) (a : Bool)
    (x : (complex (Fin (N+1))).Chain p) :
    b.coefficient p (((complex (Fin (N+1))).cylinderEndpoint a).map p x) =
      match b with
      | .endpoint a' w => if a = a' then x.val w.val else 0
      | .vertical _ => 0 := by
  cases b with
  | endpoint a' w => cases p <;> cases a <;> cases a' <;> rfl
  | vertical w => cases p <;> cases a <;> rfl

lemma atom_bounded (b : Basis N) : truncate b.dim false b.atom = b.atom := by
  cases b with
  | endpoint a w =>
    change truncate w.dim false (((complex (Fin (N+1))).cylinderEndpoint a).table w.atom) = _
    rw [← Hom.table_truncate,w.atom_dim]
    rfl
  | vertical w => exact GrayRecursive.vertical_fixed _ w.atom_dim

def boundarySide (p : ℕ) (b : Bool) : Bool := if Even p then b else !b

lemma endpointOffset_boundarySide (p : ℕ) (b : Bool) :
    endpointOffset p (boundarySide p b) = if b then -1 else 1 := by
  unfold boundarySide endpointOffset
  by_cases hp : Even p <;> cases b <;> simp [hp]

lemma coefficient_vertical_endpoint (p : ℕ) (a b : Bool) (w : Word N)
    (x : Table (complex (Fin (N+1)))) :
    (endpoint a w).coefficient p ((verticalTable x).row p b) =
      if a = boundarySide p b then (x.row p b).val w.val else 0 := by
  cases p with
  | zero => cases a <;> cases b <;> rfl
  | succ p =>
    by_cases hp : Even (p+1) <;> cases a <;> cases b <;>
      simp [coefficient,verticalTable,verticalRow,boundarySide,hp] <;> rfl

lemma coefficient_vertical_vertical (p : ℕ) (b : Bool) (w : Word N)
    (x : Table (complex (Fin (N+1)))) :
    (vertical w).coefficient (p+1) ((verticalTable x).row (p+1) b) =
      (x.row p b).val w.val := by
  by_cases hp : Even (p+1) <;> cases b <;>
    simp [coefficient,verticalTable,verticalRow,hp]

lemma atom_top_coefficient (b c : Basis N) (e : Bool) :
    c.coefficient b.dim (b.atom.row b.dim e) = if b = c then 1 else 0 := by
  classical
  cases b with
  | endpoint a w =>
    change c.coefficient w.dim ((((complex (Fin (N+1))).cylinderEndpoint a).table w.atom).row w.dim e) = _
    rw [Hom.table_row,coefficient_endpoint]
    cases c with
    | endpoint a' v =>
      rw [w.atom_top e]
      by_cases ha : a = a'
      · subst a'
        by_cases hw : w = v
        · subst v; simp
        · have hv : w.val ≠ v.val := fun h => hw (Subtype.ext h)
          simp [hw,Ne.symm hv]
      · simp [ha]
    | vertical v => simp
  | vertical w =>
    change c.coefficient (w.dim+1) ((verticalTable w.atom).row (w.dim+1) e) = _
    cases c with
    | endpoint a v =>
      rw [coefficient_vertical_endpoint, row_above_fixed w.atom w.atom_dim (by omega : w.dim < w.dim+1)]
      simp
      intro _
      rfl
    | vertical v =>
      rw [coefficient_vertical_vertical,w.atom_top e]
      by_cases hw : w = v
      · subst v; simp
      · have hv : w.val ≠ v.val := fun h => hw (Subtype.ext h)
        simp [hw,Ne.symm hv]

theorem atom_rank (b : Basis N) (p : ℕ) (hp : p < b.dim) (e : Bool)
    (c : Basis N) (hc : c.coefficient p (b.atom.row p e) ≠ 0) :
    if e then c.rank < b.rank else b.rank < c.rank := by
  cases b with
  | endpoint a w =>
    change c.coefficient p ((((complex (Fin (N+1))).cylinderEndpoint a).table w.atom).row p e) ≠ 0 at hc
    rw [Hom.table_row,coefficient_endpoint] at hc
    cases c with
    | vertical v => exact False.elim (hc rfl)
    | endpoint a' v =>
      change (if a = a' then (w.atom.row p e).val v.val else 0) ≠ 0 at hc
      by_cases ha : a = a'
      · subst a'
        rw [ite_eq_left rfl] at hc
        have hr := w.atom_rank p hp e v hc
        have hw := endpointOffset_bounds w.dim a
        have hv := endpointOffset_bounds v.dim a
        cases e <;> simp only [Bool.false_eq_true,ite_false,ite_true,rank] at hr ⊢ <;> omega
      · exact False.elim (hc (ite_eq_right ha))
  | vertical w =>
    cases c with
    | endpoint a v =>
      change (endpoint a v).coefficient p ((verticalTable w.atom).row p e) ≠ 0 at hc
      rw [coefficient_vertical_endpoint] at hc
      by_cases ha : a = boundarySide p e
      · rw [ite_eq_left ha] at hc
        by_cases hlt : p < w.dim
        · have hr := w.atom_rank p hlt e v hc
          have hv := endpointOffset_bounds v.dim a
          cases e <;> simp only [Bool.false_eq_true,ite_false,ite_true,rank] at hr ⊢ <;> omega
        · have he : p = w.dim := by change p < w.dim+1 at hp; omega
          subst p
          have he := w.atom_top_support v e hc
          subst v
          rw [ha]
          simp only [rank,endpointOffset_boundarySide]
          cases e <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
      · exact False.elim (hc (ite_eq_right ha))
    | vertical v =>
      cases p with
      | zero => exact False.elim (hc rfl)
      | succ p =>
        change (vertical v).coefficient (p+1) ((verticalTable w.atom).row (p+1) e) ≠ 0 at hc
        rw [coefficient_vertical_vertical] at hc
        have hlt : p < w.dim := by change p+1 < w.dim+1 at hp; omega
        have hr := w.atom_rank p hlt e v hc
        cases e <;> simp only [Bool.false_eq_true,ite_false,ite_true,rank] at hr ⊢ <;> omega

end Basis
end Thomason.NormalizedChains.Prism

end

end OAI
