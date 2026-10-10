import OAI.CategoryTheory.Thomason.Chains.FinalPositiveSimplexSupport
import OAI.CategoryTheory.Thomason.Strict.StrictCompositeListReplacement
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sort

namespace OAI

section

/-! # The finite coefficient interface needed for ordered atom generation

This interface is shared by the normalized simplex complexes and the finite
pasted-globe cylinder complexes. It records concrete basis coordinates,
actual positive cells, and their disjoint ordered boundaries; generation is
a theorem proved from these data, rather than a field of the interface.
-/

namespace Thomason.Construction.DirectedComplex

open scoped BigOperators

structure OrderedAtomBasis (K : DirectedComplex.{0}) where
  Index : ℕ → Type
  coordinates (p : ℕ) : K.group p ≃+ (Index p →₀ ℤ)
  positive_iff (p : ℕ) (x : K.group p) :
    x ∈ K.positive p ↔ ∀ b, 0 ≤ coordinates p x b
  augmentation (x : K.group 0) :
    K.augmentation x = (coordinates 0 x).sum (fun _ z => z)
  atom (p : ℕ) (b : Index p) : Cell K
  atom_top (p : ℕ) (b : Index p) (side : Bool) :
    coordinates p ((atom p b).table side p) = Finsupp.single b 1
  atom_above (p : ℕ) (b : Index p) (q : ℕ) :
    p < q → ∀ side, (atom p b).table side q = 0
  height (p : ℕ) (b : Index p) : ℤ
  disjoint {p q r : ℕ} (b : Index p) (c : Index q) :
    r < p → r < q → height p b ≤ height q c → ∀ e : Index r,
      coordinates r ((atom p b).table false r) e = 0 ∨
        coordinates r ((atom q c).table true r) e = 0

namespace OrderedAtomBasis

variable {K : DirectedComplex.{0}} (B : OrderedAtomBasis K)

theorem coordinate_nonnegative (p : ℕ) (x : K.group p) (hx : x ∈ K.positive p)
    (b : B.Index p) : 0 ≤ B.coordinates p x b := (B.positive_iff p x).mp hx b

include B in
theorem positive_augmentation_zero (z : K.group 0) (hz : z ∈ K.positive 0)
    (he : K.augmentation z = 0) : z = 0 := by
  classical
  apply (B.coordinates 0).injective
  rw [map_zero]
  have hs : ∑ b ∈ (B.coordinates 0 z).support, B.coordinates 0 z b = 0 := by
    simpa only [B.augmentation, Finsupp.sum] using he
  apply Finsupp.ext
  intro b
  by_cases hb : b ∈ (B.coordinates 0 z).support
  · have hle := Finset.single_le_sum
      (fun c (_ : c ∈ (B.coordinates 0 z).support) => B.coordinate_nonnegative 0 z hz c) hb
    rw [hs] at hle
    exact le_antisymm hle (B.coordinate_nonnegative 0 z hz b)
  · exact Finsupp.notMem_support_iff.mp hb

theorem positive_augmentation_one (z : K.group 0) (hz : z ∈ K.positive 0)
    (he : K.augmentation z = 1) :
    ∃ b : B.Index 0, B.coordinates 0 z = Finsupp.single b 1 := by
  classical
  let v := B.coordinates 0 z
  have hv : ∀ b, 0 ≤ v b := B.coordinate_nonnegative 0 z hz
  have hs : ∑ b ∈ v.support, v b = 1 := by
    simpa only [B.augmentation, Finsupp.sum] using he
  have hne : v ≠ 0 := by
    intro heq
    simp [heq] at hs
  obtain ⟨b, hb⟩ := Finsupp.ne_iff.mp hne
  change v b ≠ 0 at hb
  have hmem : b ∈ v.support := Finsupp.mem_support_iff.mpr hb
  have hle : v b ≤ 1 := (Finset.single_le_sum (fun c (_ : c ∈ v.support) => hv c) hmem).trans_eq hs
  have hone : v b = 1 := by have hh := hv b; omega
  have hrest : ∑ c ∈ v.support.erase b, v c = 0 := by
    have hh := Finset.sum_erase_add v.support (fun c => v c) hmem
    rw [hs, hone] at hh
    omega
  refine ⟨b, ?_⟩
  apply Finsupp.ext
  intro c
  by_cases hcb : c = b
  · subst c
    simp [v, hone]
  · rw [Finsupp.single_eq_of_ne hcb]
    by_cases hc : v c = 0
    · exact hc
    · have hm : c ∈ v.support.erase b :=
        Finset.mem_erase.mpr ⟨hcb, Finsupp.mem_support_iff.mpr hc⟩
      have hcl := (Finset.single_le_sum (fun d (_ : d ∈ v.support.erase b) => hv d) hm).trans_eq hrest
      exact le_antisymm hcl (hv c)

/-- The equality of residuals uses only the cell boundary equations. -/
theorem residual_sides (X A : Cell K) (r : ℕ)
    (he : X.table false (r+1) = A.table false (r+1)) :
    X.table false r - A.table false r = X.table true r - A.table true r := by
  have hd := congrArg (K.differential r) he
  rw [X.boundary, A.boundary] at hd
  apply sub_eq_zero.mp
  calc
    _ = (A.table true r - A.table false r) -
        (X.table true r - X.table false r) := by abel
    _ = 0 := by rw [hd, sub_self]

/-- Disjoint atom sides make every common upper-table residual positive. -/
theorem residual_positive (X : Cell K) {p : ℕ} (b : B.Index p) (r : ℕ)
    (hr : r < p) (he : X.table false (r+1) = (B.atom p b).table false (r+1)) :
    X.table false r - (B.atom p b).table false r ∈ K.positive r := by
  apply (B.positive_iff r _).mpr
  intro c
  rcases B.disjoint b b hr hr le_rfl c with hn | hp
  · simpa only [map_sub, Finsupp.sub_apply, hn, sub_zero] using
      B.coordinate_nonnegative r (X.table false r) (X.positive false r) c
  · rw [residual_sides X (B.atom p b) r he]
    simpa only [map_sub, Finsupp.sub_apply, hp, sub_zero] using
      B.coordinate_nonnegative r (X.table true r) (X.positive true r) c

/-- At degree zero augmentation one eliminates the residual. -/
theorem eq_atom_of_above_zero (X : Cell K) {p : ℕ} (b : B.Index p) (hp : 0 < p)
    (he : ∀ n, 0 < n → ∀ side, X.table side n = (B.atom p b).table side n) :
    X = B.atom p b := by
  have hr := B.residual_positive X b 0 hp (he 1 (by omega) false)
  have haug : K.augmentation (X.table false 0 - (B.atom p b).table false 0) = 0 := by
    rw [map_sub, X.augmentation, (B.atom p b).augmentation, sub_self]
  have hz := B.positive_augmentation_zero _ hr haug
  have hf := sub_eq_zero.mp hz
  have ht : X.table true 0 = (B.atom p b).table true 0 := by
    apply sub_eq_zero.mp
    rw [← residual_sides X (B.atom p b) 0 (he 1 (by omega) false), hz]
  apply Cell.ext
  funext side n
  cases n with
  | zero => cases side <;> assumption
  | succ n => exact he (n+1) (by omega) side

end OrderedAtomBasis
end Thomason.Construction.DirectedComplex

end

section

/-! # Finite positive sums in the ordered-atom coefficient interface -/

namespace Thomason.Construction.DirectedComplex.OrderedAtomBasis

open scoped BigOperators

variable {K : DirectedComplex.{0}} (B : OrderedAtomBasis K)

abbrev AtomIndex := Σ p, B.Index p

def atomCell (a : B.AtomIndex) : Cell K := B.atom a.1 a.2

def atomHeight (a : B.AtomIndex) : ℤ := B.height a.1 a.2

noncomputable def chainAtomIndices (p : ℕ) (z : K.group p) : List B.AtomIndex :=
  (B.coordinates p z).support.toList.flatMap (fun b =>
    List.replicate (B.coordinates p z b).toNat ⟨p,b⟩)

theorem chainAtomIndices_degree (p : ℕ) (z : K.group p)
    (a : B.AtomIndex) (ha : a ∈ B.chainAtomIndices p z) : a.1 = p := by
  obtain ⟨b, _, hb⟩ := List.mem_flatMap.mp ha
  obtain ⟨_, he⟩ := List.mem_replicate.mp hb
  subst a
  rfl

theorem coordinates_ofCells (as : List B.AtomIndex) (side : Bool) (p : ℕ) :
    B.coordinates p ((Cell.PositiveTable.ofCells (as.map B.atomCell)).table side p) =
      (as.map (fun a => B.coordinates p ((B.atomCell a).table side p))).sum := by
  induction as with
  | nil => exact map_zero _
  | cons a as ih =>
    change B.coordinates p ((B.atomCell a).table side p +
      (Cell.PositiveTable.ofCells (as.map B.atomCell)).table side p) = _
    rw [map_add, ih]
    rfl

private theorem sum_map_flatMap {α β M : Type*} [AddMonoid M]
    (as : List α) (f : α → List β) (g : β → M) :
    ((as.flatMap f).map g).sum = (as.map (fun a => ((f a).map g).sum)).sum := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, ih]

theorem chainAtomIndices_table (p : ℕ) (z : K.group p) (hz : z ∈ K.positive p)
    (side : Bool) :
    (Cell.PositiveTable.ofCells ((B.chainAtomIndices p z).map B.atomCell)).table side p = z := by
  classical
  apply (B.coordinates p).injective
  rw [B.coordinates_ofCells]
  unfold chainAtomIndices
  rw [sum_map_flatMap]
  simp only [List.map_replicate, List.sum_replicate]
  change ((B.coordinates p z).support.toList.map (fun b =>
    (B.coordinates p z b).toNat • B.coordinates p ((B.atom p b).table side p))).sum = _
  simp_rw [B.atom_top]
  rw [Finset.sum_map_toList]
  calc
    ∑ b ∈ (B.coordinates p z).support,
        (B.coordinates p z b).toNat • Finsupp.single b (1 : ℤ) =
      ∑ b ∈ (B.coordinates p z).support, Finsupp.single b (B.coordinates p z b) := by
      apply Finset.sum_congr rfl
      intro b _
      simp only [Finsupp.smul_single, nsmul_eq_mul, mul_one,
        Int.toNat_of_nonneg (B.coordinate_nonnegative p z hz b)]
    _ = B.coordinates p z := Finsupp.sum_single _

theorem chainAtomIndices_above (p : ℕ) (z : K.group p) (n : ℕ) (hn : p < n)
    (side : Bool) :
    (Cell.PositiveTable.ofCells ((B.chainAtomIndices p z).map B.atomCell)).table side n = 0 := by
  rw [Cell.PositiveTable.ofCells_table, List.map_map]
  apply List.sum_eq_zero
  intro v hv
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
  exact B.atom_above a.1 a.2 n
    (by rw [B.chainAtomIndices_degree p z a ha]; exact hn) side

noncomputable def sortAtoms (as : List B.AtomIndex) : List B.AtomIndex :=
  as.mergeSort (fun a b => decide (B.atomHeight a ≤ B.atomHeight b))

theorem sortAtoms_perm (as : List B.AtomIndex) : (B.sortAtoms as).Perm as :=
  List.mergeSort_perm _ _

theorem sortAtoms_pairwise (as : List B.AtomIndex) :
    (B.sortAtoms as).Pairwise (fun a b => B.atomHeight a ≤ B.atomHeight b) := by
  simpa only [sortAtoms, decide_eq_true_eq] using
    (List.pairwise_mergeSort
      (le := fun a b : B.AtomIndex => decide (B.atomHeight a ≤ B.atomHeight b))
      (fun a b c hab hbc => by
        simpa only [decide_eq_true_eq] using le_trans
          (of_decide_eq_true hab) (of_decide_eq_true hbc))
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _) as)

theorem sortAtoms_table (as : List B.AtomIndex) (side : Bool) (n : ℕ) :
    (Cell.PositiveTable.ofCells ((B.sortAtoms as).map B.atomCell)).table side n =
      (Cell.PositiveTable.ofCells (as.map B.atomCell)).table side n := by
  simp only [Cell.PositiveTable.ofCells_table, List.map_map]
  exact ((B.sortAtoms_perm as).map (fun a => (B.atomCell a).table side n)).sum_eq

/-- Coefficientwise positivity constructs the exact binary splitting. -/
theorem split_of_disjoint (X : Cell K) (A D : Cell.PositiveTable K) (r : ℕ)
    (he : ∀ n, r < n → ∀ side, X.table side n = A.table side n + D.table side n)
    (hd : ∀ b, B.coordinates r (A.table false r) b = 0 ∨
      B.coordinates r (D.table true r) b = 0) :
    ∃ (Y Z : Cell K) (hyz : Y.face true r = Z.face false r),
      Cell.comp Y Z r hyz = X ∧
      (∀ n, r < n → ∀ side, Y.table side n = A.table side n) ∧
      (∀ n, r < n → ∀ side, Z.table side n = D.table side n) := by
  apply Cell.exists_comp_of_positive_middle X A D r he
  apply (B.positive_iff r _).mpr
  intro b
  have hmiddle := congrArg (fun x => B.coordinates r x b)
    (Cell.replacement_middle_eq X A D r (he (r+1) (by omega) false))
  simp only [map_sub, map_add, Finsupp.add_apply, Finsupp.sub_apply] at hmiddle ⊢
  have hx := B.coordinate_nonnegative r (X.table false r) (X.positive false r) b
  have hy := B.coordinate_nonnegative r (X.table true r) (X.positive true r) b
  have ha := B.coordinate_nonnegative r (A.table true r) (A.positive true r) b
  have hd' := B.coordinate_nonnegative r (D.table false r) (D.positive false r) b
  rcases hd b with hz | hz <;> omega

end Thomason.Construction.DirectedComplex.OrderedAtomBasis

end

section

/-! # Generation from actual ordered atoms

This is the finite positive-table argument used for the pasted-globe
parameters of the Gray construction. The hypotheses describe explicit
coordinates and cells; no generation or freeness assertion is assumed.
-/

namespace Thomason.Construction.DirectedComplex.OrderedAtomBasis

open CategoryTheory

variable {K : DirectedComplex.{0}} (B : OrderedAtomBasis K)

theorem sumCells_coordinate_zero (as : List (Cell K)) (side : Bool) (n : ℕ)
    (b : B.Index n) (hz : ∀ A ∈ as, B.coordinates n (A.table side n) b = 0) :
    B.coordinates n ((Cell.PositiveTable.ofCells as).table side n) b = 0 := by
  induction as with
  | nil => simp only [Cell.PositiveTable.ofCells, Cell.PositiveTable.zero, map_zero, Finsupp.zero_apply]
  | cons A as ih =>
    change B.coordinates n (A.table side n +
      (Cell.PositiveTable.ofCells as).table side n) b = 0
    rw [map_add, Finsupp.add_apply, hz A (by simp),
      ih (fun C hC => hz C (by simp [hC])), zero_add]

theorem ordered_sum_induction (r : ℕ) (P : Cell K → Prop)
    (hzero : ∀ X, (∀ n, r < n → ∀ side, X.table side n = 0) → P X)
    (hcomp : ∀ (Y Z : Cell K) (hyz), P Y → P Z → P (Cell.comp Y Z r hyz))
    (as : List (Cell K))
    (hsep : as.Pairwise (fun A D => ∀ b : B.Index r,
      B.coordinates r (A.table false r) b = 0 ∨ B.coordinates r (D.table true r) b = 0))
    (hone : ∀ A ∈ as, ∀ X : Cell K,
      (∀ n, r < n → ∀ side, X.table side n = A.table side n) → P X)
    (X : Cell K)
    (he : ∀ n, r < n → ∀ side,
      X.table side n = (Cell.PositiveTable.ofCells as).table side n) : P X := by
  induction as generalizing X with
  | nil => exact hzero X he
  | cons A as ih =>
    obtain ⟨hfirst, htail⟩ := List.pairwise_cons.mp hsep
    have hd : ∀ b : B.Index r, B.coordinates r (A.table false r) b = 0 ∨
        B.coordinates r ((Cell.PositiveTable.ofCells as).table true r) b = 0 := by
      intro b
      by_cases hb : B.coordinates r (A.table false r) b = 0
      · exact Or.inl hb
      · right
        exact B.sumCells_coordinate_zero as true r b
          (fun C hC => (hfirst C hC b).resolve_left hb)
    have hs : ∀ n, r < n → ∀ side,
        X.table side n = A.table side n + (Cell.PositiveTable.ofCells as).table side n := he
    obtain ⟨Y, Z, hyz, hYZ, hY, hZ⟩ := B.split_of_disjoint X
      (Cell.PositiveTable.ofCell A) (Cell.PositiveTable.ofCells as) r hs hd
    have hp := hcomp Y Z hyz (hone A (by simp) Y hY)
      (ih htail (fun C hC => hone C (by simp [hC])) Z hZ)
    rwa [hYZ] at hp

def AboveAtomOrZero (r : ℕ) (X : Cell K) : Prop :=
  (∀ n, r < n → ∀ side, X.table side n = 0) ∨
  ∃ a : B.AtomIndex, r < a.1 ∧
    ∀ n, r < n → ∀ side, X.table side n = (B.atomCell a).table side n

theorem eq_zero_atom_of_above_zero (X : Cell K)
    (hz : ∀ n, 0 < n → ∀ side, X.table side n = 0) :
    ∃ b : B.Index 0, X = B.atom 0 b := by
  obtain ⟨b, hb⟩ := B.positive_augmentation_one (X.table false 0)
    (X.positive false 0) (X.augmentation false)
  have he : X.table true 0 = X.table false 0 := by
    have hd := X.boundary false 0
    rw [hz 1 (by omega) false, map_zero] at hd
    exact sub_eq_zero.mp hd.symm
  refine ⟨b, ?_⟩
  apply Cell.ext
  funext side n
  cases n with
  | zero =>
    apply (B.coordinates 0).injective
    rw [B.atom_top]
    cases side
    · exact hb
    · exact (congrArg (B.coordinates 0) he).trans hb
  | succ n => rw [hz (n+1) (by omega) side, B.atom_above 0 b (n+1) (by omega) side]

theorem upper_atom_decomposition (r : ℕ) (X : Cell K)
    (hx : B.AboveAtomOrZero (r+1) X) :
    ∃ as : List B.AtomIndex, (∀ a ∈ as, r < a.1) ∧
      ∀ n, r < n → ∀ side, X.table side n =
        (Cell.PositiveTable.ofCells (as.map B.atomCell)).table side n := by
  rcases hx with hz | ⟨a, ha, he⟩
  · let z := X.table false (r+1)
    refine ⟨B.chainAtomIndices (r+1) z, ?_, ?_⟩
    · intro a ha
      rw [B.chainAtomIndices_degree (r+1) z a ha]
      omega
    · intro n hn side
      by_cases heq : n = r+1
      · subst n
        rw [B.chainAtomIndices_table (r+1) z (X.positive false (r+1)) side]
        cases side
        · rfl
        · have hd := X.boundary false (r+1)
          rw [hz (r+1+1) (by omega) false, map_zero] at hd
          exact sub_eq_zero.mp hd.symm
      · have hnr : r+1 < n := by omega
        rw [hz n hnr side, B.chainAtomIndices_above (r+1) z n hnr side]
  · let A := B.atomCell a
    let z := X.table false (r+1) - A.table false (r+1)
    have hz : z ∈ K.positive (r+1) := B.residual_positive X a.2 (r+1) ha
      (he (r+1+1) (by omega) false)
    refine ⟨a :: B.chainAtomIndices (r+1) z, ?_, ?_⟩
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · omega
      · rw [B.chainAtomIndices_degree (r+1) z b hb]
        omega
    · intro n hn side
      change X.table side n = A.table side n +
        (Cell.PositiveTable.ofCells ((B.chainAtomIndices (r+1) z).map B.atomCell)).table side n
      by_cases heq : n = r+1
      · subst n
        rw [B.chainAtomIndices_table (r+1) z hz side]
        have hs := residual_sides X A (r+1) (he (r+1+1) (by omega) false)
        cases side
        · dsimp [z]
          abel
        · change X.table true (r+1) = A.table true (r+1) +
            (X.table false (r+1) - A.table false (r+1))
          rw [hs]
          abel
      · have hnr : r+1 < n := by omega
        rw [B.chainAtomIndices_above (r+1) z n hnr side, add_zero]
        exact he n hnr side

theorem predicate_of_upper_atom_sum (r : ℕ) (P : Cell K → Prop)
    (hbase : ∀ X, B.AboveAtomOrZero r X → P X)
    (hcomp : ∀ n x y hxy, P x → P y → P (Cell.comp x y n hxy))
    (as : List B.AtomIndex) (hd : ∀ a ∈ as, r < a.1) (X : Cell K)
    (he : ∀ n, r < n → ∀ side, X.table side n =
      (Cell.PositiveTable.ofCells (as.map B.atomCell)).table side n) : P X := by
  have hd' : ∀ a ∈ B.sortAtoms as, r < a.1 := fun a ha =>
    hd a ((B.sortAtoms_perm as).mem_iff.mp ha)
  have hsep : ((B.sortAtoms as).map B.atomCell).Pairwise (fun A D =>
      ∀ b : B.Index r, B.coordinates r (A.table false r) b = 0 ∨
        B.coordinates r (D.table true r) b = 0) := by
    rw [List.pairwise_map]
    apply (B.sortAtoms_pairwise as).imp_of_mem
    intro a b ha hb hab c
    exact B.disjoint a.2 b.2 (hd' a ha) (hd' b hb) hab c
  apply B.ordered_sum_induction r P (fun Y hY => hbase Y (Or.inl hY))
    (hcomp r) ((B.sortAtoms as).map B.atomCell) hsep
  · intro A hA Y hY
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hA
    exact hbase Y (Or.inr ⟨a, hd' a ha, hY⟩)
  · intro n hn side
    exact (he n hn side).trans (B.sortAtoms_table as side n).symm

/-- Actual ordered atoms composition-generate every finite positive table. -/
theorem generated (P : Cell K → Prop) (hatom : ∀ p b, P (B.atom p b))
    (hcomp : ∀ n x y hxy, P x → P y → P (Cell.comp x y n hxy)) : ∀ X, P X := by
  have hlevel : ∀ r (X : Cell K), B.AboveAtomOrZero r X → P X := by
    intro r
    induction r with
    | zero =>
      intro X hx
      rcases hx with hz | ⟨a, ha, he⟩
      · obtain ⟨b, rfl⟩ := B.eq_zero_atom_of_above_zero X hz
        exact hatom 0 b
      · have heq := B.eq_atom_of_above_zero X a.2 ha he
        rw [heq]
        exact hatom a.1 a.2
    | succ r ih =>
      intro X hx
      obtain ⟨as, hd, he⟩ := B.upper_atom_decomposition r X hx
      exact B.predicate_of_upper_atom_sum r P ih hcomp as hd X he
  intro X
  obtain ⟨N, hN⟩ := X.finite_support
  exact hlevel N X (Or.inl hN)

/-- Equality on the ordered atoms determines a strict functor out of the
actual positive-table realization. -/
theorem hom_ext {D : StrictOmegaCategory} (F G : K.realization ⟶ D)
    (he : ∀ p b, F.toFun (B.atom p b) = G.toFun (B.atom p b)) : F = G := by
  apply StrictOmegaCategory.Hom.ext
  funext X
  apply B.generated (fun X => F.toFun X = G.toFun X) he
  intro n x y hxy hx hy
  have hf : D.target n (F.toFun x) = D.source n (F.toFun y) :=
    (F.map_face true n x).symm.trans
      ((congrArg F.toFun hxy).trans (F.map_face false n y))
  have hg : D.target n (G.toFun x) = D.source n (G.toFun y) :=
    (G.map_face true n x).symm.trans
      ((congrArg G.toFun hxy).trans (G.map_face false n y))
  refine (F.map_comp n x y hxy hf).trans (Eq.trans ?_ (G.map_comp n x y hxy hg).symm)
  congr 1

end Thomason.Construction.DirectedComplex.OrderedAtomBasis

end

section

/-! # The natural-number levels of ordered atom decomposition

Level zero is exactly the set of atoms. Increasing the level weakens the
upper-table condition; every r-face is already at level r. These are the
induction interfaces for the remaining free-gluing proof.
-/

namespace Thomason.Construction.DirectedComplex.OrderedAtomBasis

variable {K : DirectedComplex.{0}} (B : OrderedAtomBasis K)

theorem aboveAtomOrZero_mono {r s : ℕ} (hrs : r ≤ s) (X : Cell K)
    (hx : B.AboveAtomOrZero r X) : B.AboveAtomOrZero s X := by
  rcases hx with hz | ⟨a, ha, he⟩
  · exact Or.inl (fun n hn side => hz n (lt_of_le_of_lt hrs hn) side)
  · by_cases hs : s < a.1
    · exact Or.inr ⟨a, hs, fun n hn side => he n (lt_of_le_of_lt hrs hn) side⟩
    · apply Or.inl
      intro n hn side
      exact (he n (lt_of_le_of_lt hrs hn) side).trans
        (B.atom_above a.1 a.2 n (by omega) side)

theorem aboveAtomOrZero_zero_iff (X : Cell K) :
    B.AboveAtomOrZero 0 X ↔ ∃ (p : ℕ) (b : B.Index p), X = B.atom p b := by
  constructor
  · intro hx
    rcases hx with hz | ⟨a, ha, he⟩
    · obtain ⟨b, hb⟩ := B.eq_zero_atom_of_above_zero X hz
      exact ⟨0, b, hb⟩
    · exact ⟨a.1, a.2, B.eq_atom_of_above_zero X a.2 ha he⟩
  · rintro ⟨p, b, rfl⟩
    cases p with
    | zero => exact Or.inl (fun n hn side => B.atom_above 0 b n hn side)
    | succ p => exact Or.inr ⟨⟨p+1,b⟩, Nat.zero_lt_succ p, fun _ _ _ => rfl⟩

theorem aboveAtomOrZero_face (X : Cell K) (side : Bool) (r : ℕ) :
    B.AboveAtomOrZero r (X.face side r) := by
  apply Or.inl
  intro n hn a
  simp only [Cell.face_table, Cell.cutTable, Nat.not_lt.mpr hn.le,
    Nat.ne_of_gt hn, ite_false]

end Thomason.Construction.DirectedComplex.OrderedAtomBasis

end

section

/-! # An explicit ordered list of composable factors

The finite positive splitting returns a full factorization with its matching
equations and an upper-table equation for each individual factor.
-/

namespace Thomason.Construction.DirectedComplex.OrderedAtomBasis

open StrictOmegaCategory

variable {K : DirectedComplex.{0}} (B : OrderedAtomBasis K)

theorem ordered_list_decomposition (r : ℕ) (as : List (Cell K)) (hne : as ≠ [])
    (hsep : as.Pairwise (fun A D => ∀ b : B.Index r,
      B.coordinates r (A.table false r) b = 0 ∨ B.coordinates r (D.table true r) b = 0))
    (X : Cell K)
    (he : ∀ n, r < n → ∀ side,
      X.table side n = (Cell.PositiveTable.ofCells as).table side n) :
    ∃ ys : List (Cell K), CompositeList K.realization r ys X ∧
      List.Forall₂ (fun A Y : Cell K =>
        ∀ n, r < n → ∀ side, Y.table side n = A.table side n) as ys := by
  induction as generalizing X with
  | nil => exact (hne rfl).elim
  | cons A as ih =>
    cases as with
    | nil =>
      refine ⟨[X], CompositeList.singleton (C := K.realization) (r := r) X, .cons ?_ .nil⟩
      intro n hn side
      have hh := he n hn side
      change X.table side n = A.table side n + 0 at hh
      simpa only [add_zero] using hh
    | cons D ds =>
      obtain ⟨hfirst, htail⟩ := List.pairwise_cons.mp hsep
      have hd : ∀ b : B.Index r, B.coordinates r (A.table false r) b = 0 ∨
          B.coordinates r ((Cell.PositiveTable.ofCells (D :: ds)).table true r) b = 0 := by
        intro b
        by_cases hb : B.coordinates r (A.table false r) b = 0
        · exact Or.inl hb
        · right
          exact B.sumCells_coordinate_zero (D :: ds) true r b
            (fun C hC => (hfirst C hC b).resolve_left hb)
      have hs : ∀ n, r < n → ∀ side,
          X.table side n = A.table side n +
            (Cell.PositiveTable.ofCells (D :: ds)).table side n := he
      obtain ⟨Y, Z, hyz, hYZ, hY, hZ⟩ := B.split_of_disjoint X
        (Cell.PositiveTable.ofCell A) (Cell.PositiveTable.ofCells (D :: ds)) r hs hd
      obtain ⟨ys, hys, hrel⟩ := ih (by simp) htail Z hZ
      refine ⟨Y :: ys, ?_, .cons hY hrel⟩
      exact hYZ ▸ (CompositeList.cons (C := K.realization) (r := r) Y hys hyz)

end Thomason.Construction.DirectedComplex.OrderedAtomBasis

end

section

/-! # The positive residual for a reversed pair of atoms

This is the chain calculation in Steiner 2004, Proposition 5.9. A pair
whose opposite boundaries are disjoint has a positive residual one degree
lower. At degree zero its augmentation would be negative, so such a pair
necessarily admits a positive lower composition degree.
-/

namespace Thomason.Construction.DirectedComplex.OrderedAtomBasis

open scoped BigOperators

variable {K : DirectedComplex.{0}} (B : OrderedAtomBasis K)

include B in
theorem augmentation_nonnegative (x : K.group 0) (hx : x ∈ K.positive 0) :
    0 ≤ K.augmentation x := by
  rw [B.augmentation, Finsupp.sum]
  exact Finset.sum_nonneg (fun b _ => B.coordinate_nonnegative 0 x hx b)

/-- A reverse-disjoint pair has an actual positive residual after removing
both atom contributions from its composite. -/
theorem two_atom_residual_positive {p q : ℕ} (a : B.Index p) (b : B.Index q)
    (r : ℕ) (hrp : r < p) (hrq : r < q) (Y Z : Cell K)
    (hyz : Y.face true r = Z.face false r)
    (hY : Y.table false (r+1) = (B.atom p a).table false (r+1))
    (hZ : Z.table false (r+1) = (B.atom q b).table false (r+1))
    (hdis : ∀ e, B.coordinates r ((B.atom p a).table true r) e = 0 ∨
      B.coordinates r ((B.atom q b).table false r) e = 0) :
    (Cell.comp Y Z r hyz).table false r - (B.atom p a).table false r -
      (B.atom q b).table false r ∈ K.positive r := by
  have hx : (Cell.comp Y Z r hyz).table false r = Y.table false r := by
    simp only [Cell.comp_table, Cell.pasteTable, Nat.lt_irrefl, ite_false, ite_true,
      Bool.false_eq_true]
  rw [hx]
  apply (B.positive_iff r _).mpr
  intro e
  have hu := B.coordinate_nonnegative r _ (B.residual_positive Y a r hrp hY) e
  have hv := B.coordinate_nonnegative r _ (B.residual_positive Z b r hrq hZ) e
  have hs := congrArg (fun x => B.coordinates r x e) (residual_sides Y (B.atom p a) r hY)
  have hm := congrArg (fun x => B.coordinates r x e) (Cell.matching_top hyz)
  simp only [map_sub, Finsupp.sub_apply] at hu hv hs ⊢
  rcases hdis e with ha | hb <;> omega

/-- Such a reversed pair cannot occur at degree zero: removing its two
augmentation-one atoms would give a positive chain of augmentation -1. -/
theorem two_atom_degree_positive {p q : ℕ} (a : B.Index p) (b : B.Index q)
    (r : ℕ) (hrp : r < p) (hrq : r < q) (Y Z : Cell K)
    (hyz : Y.face true r = Z.face false r)
    (hY : Y.table false (r+1) = (B.atom p a).table false (r+1))
    (hZ : Z.table false (r+1) = (B.atom q b).table false (r+1))
    (hdis : ∀ e, B.coordinates r ((B.atom p a).table true r) e = 0 ∨
      B.coordinates r ((B.atom q b).table false r) e = 0) : 0 < r := by
  by_contra hn
  have hr : r = 0 := by omega
  subst r
  have hz := B.two_atom_residual_positive a b 0 hrp hrq Y Z hyz hY hZ hdis
  have hp := B.augmentation_nonnegative _ hz
  have ha : K.augmentation ((Cell.comp Y Z 0 hyz).table false 0 -
      (B.atom p a).table false 0 - (B.atom q b).table false 0) = -1 := by
    rw [map_sub, map_sub, (Cell.comp Y Z 0 hyz).augmentation,
      (B.atom p a).augmentation, (B.atom q b).augmentation]
    norm_num
  rw [ha] at hp
  omega

end Thomason.Construction.DirectedComplex.OrderedAtomBasis

end

section

/-! # Ordered lower decomposition of a reverse-disjoint pair

The positive residual in Steiner 2004, Proposition 5.9 gives a concrete
finite list of atoms. Sorting that list and splitting the positive tables
produces actual matching lower composites, with exactly the two original
higher atoms and atoms in the intervening degree.
-/

namespace Thomason.Construction.DirectedComplex.OrderedAtomBasis

variable {K : DirectedComplex.{0}} (B : OrderedAtomBasis K)

theorem two_atom_upper_decomposition {p q : ℕ} (a : B.Index p) (b : B.Index q)
    (r : ℕ) (hrp : r < p) (hrq : r < q) (Y Z : Cell K)
    (hyz : Y.face true r = Z.face false r)
    (hY : ∀ n, r < n → ∀ side, Y.table side n = (B.atom p a).table side n)
    (hZ : ∀ n, r < n → ∀ side, Z.table side n = (B.atom q b).table side n)
    (hdis : ∀ e, B.coordinates r ((B.atom p a).table true r) e = 0 ∨
      B.coordinates r ((B.atom q b).table false r) e = 0) :
    ∃ ls : List B.AtomIndex, (∀ c ∈ ls, c.1 = r) ∧
      ∀ n, r ≤ n → ∀ side, (Cell.comp Y Z r hyz).table side n =
        (Cell.PositiveTable.ofCells
          ((⟨p,a⟩ :: ⟨q,b⟩ :: ls).map B.atomCell)).table side n := by
  let X := Cell.comp Y Z r hyz
  let A := B.atom p a
  let D := B.atom q b
  let z := X.table false r - A.table false r - D.table false r
  have hz : z ∈ K.positive r := B.two_atom_residual_positive a b r hrp hrq
    Y Z hyz (hY (r+1) (by omega) false) (hZ (r+1) (by omega) false) hdis
  have hu (n : ℕ) (hn : r < n) (side : Bool) :
      X.table side n = A.table side n + D.table side n := by
    change (Cell.comp Y Z r hyz).table side n = _
    simp only [Cell.comp_table, Cell.pasteTable, Nat.not_lt.mpr hn.le,
      Nat.ne_of_gt hn, ite_false]
    exact congrArg₂ (· + ·) (hY n hn side) (hZ n hn side)
  refine ⟨B.chainAtomIndices r z, fun c hc => B.chainAtomIndices_degree r z c hc, ?_⟩
  intro n hn side
  change X.table side n = A.table side n + (D.table side n +
    (Cell.PositiveTable.ofCells ((B.chainAtomIndices r z).map B.atomCell)).table side n)
  rcases hn.eq_or_lt with hn | hn
  · subst n
    rw [B.chainAtomIndices_table r z hz side]
    cases side with
    | false => dsimp [z]; abel
    | true =>
      have hb := Cell.boundary_add_of_above X (Cell.PositiveTable.ofCell A)
        (Cell.PositiveTable.ofCell D) r (hu (r+1) (by omega) false)
      change X.table true r - X.table false r =
        (A.table true r - A.table false r) +
          (D.table true r - D.table false r) at hb
      change X.table true r = A.table true r + (D.table true r +
        (X.table false r - A.table false r - D.table false r))
      calc
        X.table true r = (X.table true r - X.table false r) + X.table false r := by abel
        _ = _ := by rw [hb]; abel
  · rw [B.chainAtomIndices_above r z n hn side, add_zero]
    exact hu n hn side

theorem two_atom_ordered_lower_decomposition {p q : ℕ}
    (a : B.Index p) (b : B.Index q) (s : ℕ)
    (hrp : s+1 < p) (hrq : s+1 < q) (Y Z : Cell K)
    (hyz : Y.face true (s+1) = Z.face false (s+1))
    (hY : ∀ n, s+1 < n → ∀ side, Y.table side n = (B.atom p a).table side n)
    (hZ : ∀ n, s+1 < n → ∀ side, Z.table side n = (B.atom q b).table side n)
    (hdis : ∀ e, B.coordinates (s+1) ((B.atom p a).table true (s+1)) e = 0 ∨
      B.coordinates (s+1) ((B.atom q b).table false (s+1)) e = 0) :
    ∃ (ls as : List B.AtomIndex) (xs : List (Cell K)),
      (∀ c ∈ ls, c.1 = s+1) ∧ as.Perm (⟨p,a⟩ :: ⟨q,b⟩ :: ls) ∧
      as.Pairwise (fun c d => B.atomHeight c ≤ B.atomHeight d) ∧
      StrictOmegaCategory.CompositeList K.realization s xs (Cell.comp Y Z (s+1) hyz) ∧
      List.Forall₂ (fun c (x : Cell K) =>
        ∀ n, s < n → ∀ side, x.table side n = (B.atomCell c).table side n) as xs := by
  obtain ⟨ls, hls, he⟩ := B.two_atom_upper_decomposition a b (s+1) hrp hrq
    Y Z hyz hY hZ hdis
  let as := B.sortAtoms (⟨p,a⟩ :: ⟨q,b⟩ :: ls)
  have hp : as.Perm (⟨p,a⟩ :: ⟨q,b⟩ :: ls) := B.sortAtoms_perm _
  have hd : ∀ c ∈ as, s < c.1 := by
    intro c hc
    have hc' := hp.mem_iff.mp hc
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact Nat.lt_trans (Nat.lt_succ_self s) hrp
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact Nat.lt_trans (Nat.lt_succ_self s) hrq
    rw [hls c hc']
    omega
  have hne : as.map B.atomCell ≠ [] := by
    intro hz
    have hl := hp.length_eq
    have ha : as = [] := List.map_eq_nil_iff.mp hz
    rw [ha] at hl
    simp at hl
  have hsep : (as.map B.atomCell).Pairwise (fun A D => ∀ e : B.Index s,
      B.coordinates s (A.table false s) e = 0 ∨
        B.coordinates s (D.table true s) e = 0) := by
    rw [List.pairwise_map]
    apply (B.sortAtoms_pairwise (⟨p,a⟩ :: ⟨q,b⟩ :: ls)).imp_of_mem
    intro c d hc hd' hcd e
    exact B.disjoint c.2 d.2 (hd c hc) (hd d hd') hcd e
  obtain ⟨xs, hxs, hrel⟩ := B.ordered_list_decomposition s (as.map B.atomCell) hne
    hsep (Cell.comp Y Z (s+1) hyz) (fun n hn side =>
      (he n (by omega) side).trans (B.sortAtoms_table _ side n).symm)
  refine ⟨ls, as, xs, hls, hp, B.sortAtoms_pairwise _, hxs, ?_⟩
  exact List.forall₂_map_left_iff.mp hrel

end Thomason.Construction.DirectedComplex.OrderedAtomBasis

end

section

/-! # Grouping a lower string around its two higher atoms

Only the two higher atoms contribute above the intervening degree. Cutting
the actual composite between them gives the binary decomposition of
Steiner 2004, Proposition 5.9.
-/

namespace Thomason.Construction.DirectedComplex.OrderedAtomBasis

open StrictOmegaCategory

variable {K : DirectedComplex.{0}} (B : OrderedAtomBasis K)

def higherAtomLabels (r : ℕ) (as : List B.AtomIndex) : List B.AtomIndex :=
  as.filter (fun a => decide (r < a.1))

theorem atomTable_sum_filter (r : ℕ) (as : List B.AtomIndex)
    (n : ℕ) (hn : r < n) (side : Bool) :
    (as.map (fun a => (B.atomCell a).table side n)).sum =
      ((B.higherAtomLabels r as).map (fun a => (B.atomCell a).table side n)).sum := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    by_cases ha : r < a.1
    · simp only [higherAtomLabels, List.filter_cons, decide_eq_true ha, ite_true,
        List.map_cons, List.sum_cons] at *
      rw [ih]
    · have hz := B.atom_above a.1 a.2 n (by omega) side
      simp only [higherAtomLabels, List.filter_cons, decide_eq_false ha,
        List.map_cons, List.sum_cons, atomCell, hz, zero_add] at *
      exact ih

theorem related_table_sum {as : List B.AtomIndex} {xs : List (Cell K)}
    (r : ℕ) (h : List.Forall₂ (fun a (x : Cell K) =>
      ∀ n, r < n → ∀ side, x.table side n = (B.atomCell a).table side n) as xs)
    (n : ℕ) (hn : r < n) (side : Bool) :
    (xs.map (fun x => x.table side n)).sum =
      (as.map (fun a => (B.atomCell a).table side n)).sum := by
  induction h with
  | nil => rfl
  | cons hhead htail ih =>
    simp only [List.map_cons, List.sum_cons, hhead n hn side, ih]

theorem group_two_higher_atoms (s r : ℕ) (hsr : s ≤ r)
    (as : List B.AtomIndex) (xs : List (Cell K)) (X : Cell K)
    (hxs : CompositeList K.realization s xs X)
    (hrel : List.Forall₂ (fun a (x : Cell K) =>
      ∀ n, s < n → ∀ side, x.table side n = (B.atomCell a).table side n) as xs)
    (a b : B.AtomIndex) (hab : B.higherAtomLabels r as = [a,b]) :
    ∃ (Y Z : Cell K) (hyz : Y.face true s = Z.face false s),
      Cell.comp Y Z s hyz = X ∧
      (∀ n, r < n → ∀ side, Y.table side n = (B.atomCell a).table side n) ∧
      (∀ n, r < n → ∀ side, Z.table side n = (B.atomCell b).table side n) := by
  obtain ⟨ls, rs, has, hl, hr⟩ :=
    List.filter_eq_append_iff.mp (show as.filter (fun c => decide (r < c.1)) =
      [a] ++ [b] from hab)
  have hlne : ls ≠ [] := by
    intro he
    simp [he] at hl
  have hrne : rs ≠ [] := by
    intro he
    simp [he] at hr
  have hlrel : List.Forall₂ (fun a (x : Cell K) =>
      ∀ n, s < n → ∀ side, x.table side n = (B.atomCell a).table side n)
      ls (xs.take ls.length) := by
    have ht := List.forall₂_take ls.length hrel
    rw [has, List.take_left] at ht
    exact ht
  have hrrel : List.Forall₂ (fun a (x : Cell K) =>
      ∀ n, s < n → ∀ side, x.table side n = (B.atomCell a).table side n)
      rs (xs.drop ls.length) := by
    have ht := List.forall₂_drop ls.length hrel
    rw [has, List.drop_left] at ht
    exact ht
  have hleftne : xs.take ls.length ≠ [] := by
    intro he
    have hh := hlrel.length_eq
    rw [he, List.length_nil] at hh
    exact hlne (List.length_eq_zero_iff.mp hh)
  have hrightne : xs.drop ls.length ≠ [] := by
    intro he
    have hh := hrrel.length_eq
    rw [he, List.length_nil] at hh
    exact hrne (List.length_eq_zero_iff.mp hh)
  have hsplit : CompositeList K.realization s
      (xs.take ls.length ++ xs.drop ls.length) X := by
    simpa only [List.take_append_drop] using hxs
  obtain ⟨Y, Z, hyz, hY, hZ, he⟩ := hsplit.split hleftne hrightne
  refine ⟨Y, Z, hyz, he, ?_, ?_⟩
  · intro n hn side
    rw [Cell.compositeList_table hY n (lt_of_le_of_lt hsr hn) side,
      B.related_table_sum s hlrel n (lt_of_le_of_lt hsr hn) side,
      B.atomTable_sum_filter r ls n hn side]
    change ((ls.filter (fun c => decide (r < c.1))).map _).sum = _
    simp only [hl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  · intro n hn side
    rw [Cell.compositeList_table hZ n (lt_of_le_of_lt hsr hn) side,
      B.related_table_sum s hrrel n (lt_of_le_of_lt hsr hn) side,
      B.atomTable_sum_filter r rs n hn side]
    change ((rs.filter (fun c => decide (r < c.1))).map _).sum = _
    simp only [hr, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

/-- A reverse-disjoint pair at degree s+1 is a binary composite at degree s,
with the same higher atom contributions, in one of the two possible orders. -/
theorem two_atom_lowering {p q : ℕ} (a : B.Index p) (b : B.Index q) (s : ℕ)
    (hrp : s+1 < p) (hrq : s+1 < q) (Y Z : Cell K)
    (hyz : Y.face true (s+1) = Z.face false (s+1))
    (hY : ∀ n, s+1 < n → ∀ side, Y.table side n = (B.atom p a).table side n)
    (hZ : ∀ n, s+1 < n → ∀ side, Z.table side n = (B.atom q b).table side n)
    (hdis : ∀ e, B.coordinates (s+1) ((B.atom p a).table true (s+1)) e = 0 ∨
      B.coordinates (s+1) ((B.atom q b).table false (s+1)) e = 0) :
    ∃ (U V : Cell K) (huv : U.face true s = V.face false s),
      Cell.comp U V s huv = Cell.comp Y Z (s+1) hyz ∧
      ((∀ n, s+1 < n → ∀ side, U.table side n = (B.atom p a).table side n) ∧
       (∀ n, s+1 < n → ∀ side, V.table side n = (B.atom q b).table side n) ∨
       (∀ n, s+1 < n → ∀ side, U.table side n = (B.atom q b).table side n) ∧
       (∀ n, s+1 < n → ∀ side, V.table side n = (B.atom p a).table side n)) := by
  obtain ⟨ls, as, xs, hls, hp, _, hxs, hrel⟩ :=
    B.two_atom_ordered_lower_decomposition a b s hrp hrq Y Z hyz hY hZ hdis
  have hf : B.higherAtomLabels (s+1) ls = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro c hc
    simp only [hls c hc, Nat.lt_irrefl, decide_false, Bool.false_eq_true, not_false_eq_true]
  have hperm : (B.higherAtomLabels (s+1) as).Perm [⟨p,a⟩, ⟨q,b⟩] := by
    have hh := hp.filter (fun c => decide (s+1 < c.1))
    simpa only [higherAtomLabels, List.filter_cons, decide_eq_true hrp,
      decide_eq_true hrq, ite_true, show ls.filter (fun c => decide (s+1 < c.1)) = [] from hf]
      using hh
  rcases List.perm_pair.mp hperm with hab | hab
  · obtain ⟨U, V, huv, he, hU, hV⟩ :=
      B.group_two_higher_atoms s (s+1) (by omega) as xs _ hxs hrel ⟨p,a⟩ ⟨q,b⟩ hab
    exact ⟨U, V, huv, he, Or.inl ⟨hU, hV⟩⟩
  · obtain ⟨U, V, huv, he, hU, hV⟩ :=
      B.group_two_higher_atoms s (s+1) (by omega) as xs _ hxs hrel ⟨q,b⟩ ⟨p,a⟩ hab
    exact ⟨U, V, huv, he, Or.inr ⟨hU, hV⟩⟩

end Thomason.Construction.DirectedComplex.OrderedAtomBasis

end

end OAI
