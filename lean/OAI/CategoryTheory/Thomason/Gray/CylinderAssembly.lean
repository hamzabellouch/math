import OAI.CategoryTheory.Thomason.Chains.NormalizedTuples
import OAI.CategoryTheory.Thomason.Gray.DirectedGlobeUniversal
import OAI.CategoryTheory.Thomason.Strict.StrictTerminalConeCategory
import OAI.CategoryTheory.Thomason.Strict.UnderlyingCategory
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Order.UpperLower.Basic

namespace OAI

section

/-!
# Composition generation by normalized simplex atoms

Steiner, *Omega-categories and chain complexes* (2004), Definition 3.2,
Example 3.8 and Theorem 5.6 (arXiv:math/0403237v2), identify these exact
normalized-chain atoms and prove composition generation. The principal atoms in this specialization are fixed by their entire
chain tables.
-/

namespace Thomason.Construction

open CategoryTheory

namespace SimplexComplex

/-- The positive or negative part of an integral chain, coefficient by coefficient. -/
noncomputable def signedPart {m p : ℕ} (a : Bool) (x : Chains m p) : Chains m p :=
  x.mapRange (fun z => max 0 (if a then z else -z)) (by cases a <;> simp)

/-- The distinguished top-dimensional simplex basis element. -/
def topBasis (m : ℕ) : Basis m m := OrderEmbedding.ofStrictMono id strictMono_id

/-- Steiner's downward-recursive formula specifies every entry of an atom. -/
def IsBasisAtom (h : NormalizedSimplexIdentities) {m p : ℕ}
    (b : Basis m p) (x : h.object m) : Prop :=
  (∀ a, x.table a p = Finsupp.single b 1) ∧
  (∀ a n, n < p → x.table a n = signedPart a (differential m n (x.table a (n + 1)))) ∧
  (∀ a n, p < n → x.table a n = 0)

/-- The full table formula characterizes an atom uniquely. -/
theorem IsBasisAtom.unique (h : NormalizedSimplexIdentities) {m p : ℕ}
    {b : Basis m p} {x y : h.object m} (hx : IsBasisAtom h b x) (hy : IsBasisAtom h b y) : x = y := by
  apply DirectedComplex.Cell.ext
  funext a n
  by_cases hpn : p < n
  · exact (hx.2.2 a n hpn).trans (hy.2.2 a n hpn).symm
  · have he : ∀ k, x.table a (p - k) = y.table a (p - k) := by
      intro k
      induction k with
      | zero => simpa using (hx.1 a).trans (hy.1 a).symm
      | succ k ih =>
        by_cases hk : k < p
        · have hn : p - (k + 1) < p := by omega
          rw [hx.2.1 a _ hn, hy.2.1 a _ hn]
          have he : p - (k + 1) + 1 = p - k := by omega
          have ht : x.table a (p - (k + 1) + 1) = y.table a (p - (k + 1) + 1) :=
            he.symm ▸ ih
          exact congrArg (fun z => signedPart a (differential m (p - (k + 1)) z)) ht
        · have hz : p - (k + 1) = p - k := by omega
          exact hz.symm ▸ ih
    have hz : p - (p - n) = n := by omega
    exact hz ▸ he (p - n)

end SimplexComplex

/-- Precisely the published atom facts used in the full-face argument. -/
structure SimplexAtomsInput (h : NormalizedSimplexIdentities) where
  principal (m : ℕ) : h.object m
  principal_table (m : ℕ) : SimplexComplex.IsBasisAtom h (SimplexComplex.topBasis m) (principal m)
  principal_source (m : ℕ) : (h.object m).source 0 (principal m) = SimplexComplex.vertex h 0
  principal_target (m : ℕ) : (h.object m).target 0 (principal m) =
    SimplexComplex.vertex h (Fin.last m)
  generated (m : ℕ) (P : h.object m → Prop)
    (atoms : ∀ p (b : SimplexComplex.Basis m p), P ((h.map b.toOrderHom).toFun (principal p)))
    (compositions : ∀ n x y hxy, P x → P y → P ((h.object m).comp n x y hxy)) :
    ∀ x, P x

namespace SimplexAtomsInput

variable {h : NormalizedSimplexIdentities} (a : SimplexAtomsInput h)

/-- The actual simplex atom indexed by an increasing tuple. -/
noncomputable def atom {m p : ℕ} (b : SimplexComplex.Basis m p) : h.object m :=
  (h.map b.toOrderHom).toFun (a.principal p)

theorem atom_source {m p : ℕ} (b : SimplexComplex.Basis m p) :
    (h.object m).source 0 (a.atom b) = SimplexComplex.vertex h (b 0) := by
  exact ((h.map b.toOrderHom).map_face false 0 (a.principal p)).symm.trans
    ((congrArg (h.map b.toOrderHom).toFun (a.principal_source p)).trans
      (SimplexComplex.map_vertex h b.toOrderHom 0))

theorem atom_target {m p : ℕ} (b : SimplexComplex.Basis m p) :
    (h.object m).target 0 (a.atom b) = SimplexComplex.vertex h (b (Fin.last p)) := by
  exact ((h.map b.toOrderHom).map_face true 0 (a.principal p)).symm.trans
    ((congrArg (h.map b.toOrderHom).toFun (a.principal_target p)).trans
      (SimplexComplex.map_vertex h b.toOrderHom (Fin.last p)))

end SimplexAtomsInput
end Thomason.Construction

end

section

/-!
# Strict labels determined by ordered object functions

The nondecreasing endpoints of oriental cells yield their canonical strict
maps to ordinal categories, natural for all simplex operators.
-/

namespace Thomason.Construction

open CategoryTheory

namespace StrictOmegaCategory

variable {C D : StrictOmegaCategory.{0}}

/-- Taking an object boundary commutes with every strict functor. -/
theorem Hom.object_boundary (f : C ⟶ D) (a : Bool) (x : C) :
    f.toOneFunctor.obj (C.boundaryObject a x) = D.boundaryObject a (f.toFun x) :=
  Subtype.ext (f.map_face a 0 x)

/-- An ordered object function extends uniquely to a strict poset label. -/
def orderedLabel {E : Type} [Preorder E] (f : Objects C → E)
    (hf : ∀ x : C, f (C.boundaryObject false x) ≤ f (C.boundaryObject true x)) :
    C ⟶ StrictPoset.category E where
  toFun x := ⟨f (C.boundaryObject false x), f (C.boundaryObject true x), hf x⟩
  map_face a n x := by
    cases n with
    | zero =>
      cases a <;> apply StrictPoset.Cell.ext
      all_goals
        change f _ = f _
        congr 1
        apply Subtype.ext
        exact C.face_face_same _ _ 0 x
    | succ n =>
      apply StrictPoset.Cell.ext
      all_goals
        change f _ = f _
        congr 1
        apply Subtype.ext
        exact (C.globular _ _ 0 (n + 1) x).trans (ite_eq_left (Nat.zero_lt_succ n))
  map_comp n x y hxy h' := by
    cases n with
    | zero =>
      apply StrictPoset.Cell.ext
      · change f _ = f _
        exact congrArg f (Subtype.ext (C.source_comp 0 x y hxy))
      · change f _ = f _
        exact congrArg f (Subtype.ext (C.target_comp 0 x y hxy))
    | succ n =>
      apply StrictPoset.Cell.ext
      all_goals
        change f _ = f _
        congr 1
        apply Subtype.ext
        exact C.zero_face_comp_succ _ n x y hxy

@[simp]
theorem orderedLabel_object {E : Type} [Preorder E] (f : Objects C → E)
    (hf : ∀ x : C, f (C.boundaryObject false x) ≤ f (C.boundaryObject true x))
    (x : Objects C) :
    (orderedLabel f hf).toFun x.val = StrictPoset.identity (f x) := by
  apply StrictPoset.Cell.ext
  · exact congrArg f (C.boundaryObject_of_object false x)
  · exact congrArg f (C.boundaryObject_of_object true x)

/-- A strict poset label is determined by its action on object cells. -/
theorem hom_poset_ext {E : Type} [Preorder E] {f g : C ⟶ StrictPoset.category E}
    (he : ∀ x : Objects C, f.toFun x.val = g.toFun x.val) : f = g := by
  apply Hom.ext
  funext x
  apply StrictPoset.Cell.ext
  · have hs := he (C.boundaryObject false x)
    have hf := f.map_face false 0 x
    have hg := g.map_face false 0 x
    have he := congrArg (fun z : StrictPoset.Cell E => z.first) (hf.symm.trans (hs.trans hg))
    exact he
  · have ht := he (C.boundaryObject true x)
    have hf := f.map_face true 0 x
    have hg := g.map_face true 0 x
    have he := congrArg (fun z : StrictPoset.Cell E => z.last) (hf.symm.trans (ht.trans hg))
    exact he

end StrictOmegaCategory

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities)

/-- The canonical strict map from an oriental to its ordered vertices. -/
noncomputable def ordinalLabel (m : ℕ) : h.object m ⟶ StrictPoset.category (Fin (m + 1)) :=
  StrictOmegaCategory.orderedLabel (SimplexComplex.objectsEquiv h m)
    (SimplexComplex.endpoints_ordered h)

@[simp]
theorem ordinalLabel_vertex {m : ℕ} (i : Fin (m + 1)) :
    (h.ordinalLabel m).toFun (SimplexComplex.vertex h i) = StrictPoset.identity i := by
  have he := StrictOmegaCategory.orderedLabel_object (SimplexComplex.objectsEquiv h m)
    (SimplexComplex.endpoints_ordered h)
    ((SimplexComplex.objectsEquiv h m).symm i)
  exact he.trans (congrArg StrictPoset.identity ((SimplexComplex.objectsEquiv h m).apply_symm_apply i))

/-- Ordinal labelling commutes with every simplex operator, including degeneracies. -/
theorem ordinalLabel_naturality {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) :
    h.map f ≫ h.ordinalLabel n = h.ordinalLabel m ≫ StrictPoset.map f := by
  apply StrictOmegaCategory.hom_poset_ext
  intro x
  obtain ⟨i, hi⟩ := SimplexComplex.eq_vertex_of_dimensionLE h x.val x.property
  change (h.ordinalLabel n).toFun ((h.map f).toFun x.val) =
    (StrictPoset.map f).toFun ((h.ordinalLabel m).toFun x.val)
  rw [hi, SimplexComplex.map_vertex, ordinalLabel_vertex, ordinalLabel_vertex]
  rfl

end NormalizedSimplexIdentities
end Thomason.Construction

end

section

/-!
# Positive relative-prism chains

The prism formula uses the right tensor factor convention. Its exceptional
last-face cancellation follows from the sieve and constancy assumptions.
-/

namespace Thomason.Construction.SimplexComplex

open scoped BigOperators

noncomputable def rise {m n : ℕ} (f g : Fin (m + 1) →o Fin (n + 1))
    (hfg : ∀ i, f i ≤ g i) : Chains n (m + 1) :=
  tuple (append f (g (Fin.last m)) (hfg _))

/-- The image of a prism generator is the normalized tuple with the final
upper endpoint appended. -/
noncomputable def prismBasis {m n : ℕ} (f g : Fin (m + 1) →o Fin (n + 1))
    (hfg : ∀ i, f i ≤ g i) (p : ℕ) (s : Basis m p) : Chains n (p + 1) :=
  rise (f.comp s.toOrderHom) (g.comp s.toOrderHom) (fun i => hfg (s i))

noncomputable def prism {m n : ℕ} (f g : Fin (m + 1) →o Fin (n + 1))
    (hfg : ∀ i, f i ≤ g i) (p : ℕ) : Chains m p →ₗ[ℤ] Chains n (p + 1) :=
  Finsupp.linearCombination ℤ (prismBasis f g hfg p)

@[simp]
theorem prism_single {m n : ℕ} (f g : Fin (m + 1) →o Fin (n + 1))
    (hfg : ∀ i, f i ≤ g i) (p : ℕ) (s : Basis m p) (z : ℤ) :
    prism f g hfg p (Finsupp.single s z) = z • prismBasis f g hfg p s := by
  simp [prism]

theorem prismBasis_nonneg {m n p : ℕ} (f g : Fin (m + 1) →o Fin (n + 1))
    (hfg : ∀ i, f i ≤ g i) (s : Basis m p) (t : Basis n (p + 1)) :
    0 ≤ prismBasis f g hfg p s t := tuple_nonneg _ _

/-- The new prism operator preserves the specified positive cones. -/
theorem prism_positive {m n p : ℕ} (f g : Fin (m + 1) →o Fin (n + 1))
    (hfg : ∀ i, f i ≤ g i) {x : Chains m p} (hx : x ∈ positive m p) :
    prism f g hfg p x ∈ positive n (p + 1) := by
  classical
  intro t
  simp only [prism, Finsupp.linearCombination_apply, Finsupp.sum,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact Finset.sum_nonneg fun s _ => mul_nonneg (hx s) (prismBasis_nonneg f g hfg s t)

/-- On any simplex whose final vertex is fixed, the whole prism generator
vanishes by normalization. -/
theorem prismBasis_stationary {m n p : ℕ} (f g : Fin (m + 1) →o Fin (n + 1))
    (hfg : ∀ i, f i ≤ g i) (s : Basis m p) (he : f (s (Fin.last p)) = g (s (Fin.last p))) :
    prismBasis f g hfg p s = 0 := tuple_append_eq_zero _ _ _ he

/-- Sieve membership of the penultimate vertex gives an entirely old initial
segment; otherwise both final vertices lie in the constant new part. -/
theorem old_initial_or_constant_tail {E : Type*} [Preorder E] {A : Set E}
    (hA : IsLowerSet A) {n p : ℕ} (f g : E →o Fin (n + 1))
    (hagree : ∀ x ∈ A, f x = g x)
    (hconstant : ∀ x ∉ A, ∀ y ∉ A, g x = g y)
    (s : Fin (p + 2) →o E) :
    (∀ i : Fin (p + 1), f (s i.castSucc) = g (s i.castSucc)) ∨
      g (s (Fin.last (p + 1))) = g (s (Fin.last p).castSucc) := by
  by_cases ha : s (Fin.last p).castSucc ∈ A
  · left
    intro i
    apply hagree
    exact hA (s.monotone (Fin.castSucc_le_castSucc_iff.mpr i.le_last)) ha
  · right
    apply hconstant
    · intro hx
      exact ha (hA (s.monotone (Fin.le_last _)) hx)
    · exact ha

/-- The exceptional-face identity needed in the differential of the prism,
now derived from exactly the order/sieve hypotheses of the manuscript. -/
theorem relative_prism_last_face_cancel {E : Type*} [Preorder E] {A : Set E}
    (hA : IsLowerSet A) {n p : ℕ} (f g : E →o Fin (n + 1))
    (hfg : ∀ x, f x ≤ g x) (hagree : ∀ x ∈ A, f x = g x)
    (hconstant : ∀ x ∉ A, ∀ y ∉ A, g x = g y)
    (s : Fin (p + 2) →o E) :
    tuple (append (initial (f.comp s)) (g (s (Fin.last (p + 1))))
      ((hfg _).trans (g.monotone (s.monotone (Fin.le_last _))))) -
    tuple (append (initial (f.comp s)) (g (s (Fin.last p).castSucc)) (hfg _)) =
      tuple (g.comp s) :=
  prism_last_face_cancel (f.comp s) (g.comp s) (fun i => hfg (s i))
    (old_initial_or_constant_tail hA f g hagree hconstant s)

end Thomason.Construction.SimplexComplex

end

section

/-! # The signed boundary calculation for the positive relative prism -/

namespace Thomason.Construction.SimplexComplex

open scoped BigOperators

@[simp]
theorem deleteTuple_last {n p : ℕ} (f : Fin (p + 2) →o Fin (n + 1)) :
    deleteTuple f (Fin.last (p + 1)) = initial f := by
  apply DFunLike.ext
  intro i
  change f ((Fin.last (p + 1)).succAbove i) = f i.castSucc
  rw [Fin.succAbove_last]

theorem rise_delete_castSucc {n p : ℕ} (f g : Fin (p + 2) →o Fin (n + 1))
    (hfg : ∀ i, f i ≤ g i) (i : Fin (p + 1)) :
    rise (deleteTuple f i.castSucc) (deleteTuple g i.castSucc)
      (fun j => hfg (i.castSucc.succAbove j)) =
    tuple (append (deleteTuple f i.castSucc) (g (Fin.last (p + 1)))
      ((f.monotone (Fin.le_last _)).trans (hfg _))) := by
  unfold rise
  congr 1
  apply DFunLike.ext
  intro j
  induction j using Fin.lastCases with
  | cast j => exact (append_castSucc _ _ _ j).trans (append_castSucc _ _ _ j).symm
  | last =>
    have he : (deleteTuple g i.castSucc) (Fin.last p) = g (Fin.last (p + 1)) := by
      change g (i.castSucc.succAbove (Fin.last p)) = g (Fin.last (p + 1))
      rw [Fin.succAbove_ne_last_last (Fin.castSucc_ne_last i)]
    exact (append_last _ _ _).trans (he.trans (append_last _ _ _).symm)

/-- The prism's boundary identity on weakly increasing tuples, with exactly
its old-initial-segment/constant-final-segment hypothesis. -/
theorem rise_boundary (h : NormalizedSimplexIdentities) {n p : ℕ}
    (f g : Fin (p + 2) →o Fin (n + 1)) (hfg : ∀ i, f i ≤ g i)
    (hcases : (∀ i : Fin (p + 1), f i.castSucc = g i.castSucc) ∨
      g (Fin.last (p + 1)) = g (Fin.last p).castSucc) :
    differential n (p + 1) (rise f g hfg) =
      (∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        rise (deleteTuple f i) (deleteTuple g i) (fun j => hfg (i.succAbove j))) +
      ((-1 : ℤ) ^ (p + 1)) • (tuple g - tuple f) := by
  rw [rise, differential_tuple h]
  conv_lhs => rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, delete_append_last, delete_append_castSucc]
  conv_lhs => rw [Fin.sum_univ_castSucc]
  conv_rhs => rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, rise_delete_castSucc, deleteTuple_last]
  have hc := prism_last_face_cancel f g hfg hcases
  rw [← hc]
  simp only [rise, initial_apply, pow_succ, mul_neg_one, neg_smul, smul_sub]
  abel

theorem prism_differentialBasis {m n p : ℕ}
    (f g : Fin (m + 1) →o Fin (n + 1)) (hfg : ∀ i, f i ≤ g i)
    (s : Basis m (p + 1)) :
    prism f g hfg p (differentialBasis m p s) =
      ∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        prismBasis f g hfg p (deleteVertex s i) := by
  simp only [differentialBasis, map_sum, prism_single]

/-- The signed differential formula for each basis prism, derived from the
actual sieve hypotheses rather than assumed as a cylinder input. -/
theorem prismBasis_boundary (h : NormalizedSimplexIdentities) {m n p : ℕ}
    {A : Set (Fin (m + 1))} (hA : IsLowerSet A)
    (f g : Fin (m + 1) →o Fin (n + 1)) (hfg : ∀ i, f i ≤ g i)
    (hagree : ∀ x ∈ A, f x = g x)
    (hconstant : ∀ x ∉ A, ∀ y ∉ A, g x = g y) (s : Basis m (p + 1)) :
    differential n (p + 1) (prismBasis f g hfg (p + 1) s) =
      prism f g hfg p (differentialBasis m p s) +
      ((-1 : ℤ) ^ (p + 1)) • (mapBasis g (p + 1) s - mapBasis f (p + 1) s) := by
  have hb := rise_boundary h (f.comp s.toOrderHom) (g.comp s.toOrderHom)
    (fun i => hfg (s i)) (old_initial_or_constant_tail hA f g hagree hconstant s.toOrderHom)
  have hd (q : Fin (m + 1) →o Fin (n + 1)) (i : Fin (p + 2)) :
      deleteTuple (q.comp s.toOrderHom) i = q.comp (deleteVertex s i).toOrderHom := by
    apply DFunLike.ext
    intro j
    rfl
  simp only [hd] at hb
  simpa only [prismBasis, prism_differentialBasis, mapBasis_eq_tuple] using hb

theorem rise_boundary_zero (h : NormalizedSimplexIdentities) {n : ℕ}
    (f g : Fin 1 →o Fin (n + 1)) (hfg : ∀ i, f i ≤ g i) :
    differential n 0 (rise f g hfg) = tuple g - tuple f := by
  let a := append f (g (Fin.last 0)) (hfg _)
  have hzero : deleteTuple a 0 = g := by
    apply DFunLike.ext
    intro i
    fin_cases i
    change a ((0 : Fin 2).succAbove 0) = g 0
    change a (Fin.last 1) = g 0
    exact append_last f (g (Fin.last 0)) (hfg _)
  have hone : deleteTuple a 1 = f := delete_append_last f _ _
  change differential n 0 (tuple a) = _
  rw [differential_tuple h, Fin.sum_univ_two, hzero, hone]
  simp [sub_eq_add_neg]

end Thomason.Construction.SimplexComplex

end

section

/-! # Realizing the positive relative-prism chain map -/

namespace Thomason.Construction.SimplexComplex

open scoped BigOperators

variable (h : NormalizedSimplexIdentities)
variable {m n : ℕ} {A : Set (Fin (m + 1))} (hA : IsLowerSet A)
variable (f g : Fin (m + 1) →o Fin (n + 1)) (hfg : ∀ i, f i ≤ g i)
variable (hagree : ∀ x ∈ A, f x = g x)
variable (hconstant : ∀ x ∉ A, ∀ y ∉ A, g x = g y)

include h hA hagree hconstant in
/-- Extend the basis boundary identity by linearity in every positive degree. -/
theorem prism_boundary (p : ℕ) (x : Chains m (p + 1)) :
    differential n (p + 1) (prism f g hfg (p + 1) x) =
      prism f g hfg p (differential m p x) +
        ((-1 : ℤ) ^ (p + 1)) • (mapChains g (p + 1) x - mapChains f (p + 1) x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, hx, hy, smul_sub, smul_add]
    abel
  | single s z =>
    simp only [prism_single, differential_single, map_smul, mapChains_single]
    rw [prismBasis_boundary h hA f g hfg hagree hconstant s]
    simp only [smul_add, smul_sub, smul_comm z ((-1 : ℤ) ^ (p + 1))]

include h in
/-- Degree zero of the same boundary identity. -/
theorem prism_boundary_zero (x : Chains m 0) :
    differential n 0 (prism f g hfg 0 x) = mapChains g 0 x - mapChains f 0 x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    abel
  | single s z =>
    simp only [prism_single, map_smul, mapChains_single, prismBasis]
    have hz := rise_boundary_zero h (f.comp s.toOrderHom) (g.comp s.toOrderHom)
      (fun i => hfg (s i))
    simpa only [mapBasis_eq_tuple, smul_sub] using congrArg (fun y => z • y) hz

open _root_.OAI.Thomason.Construction.DirectedComplex

/-- The generator formula on the actual right tensor chain groups. -/
noncomputable def prismApp : (p : ℕ) →
    (RightCylinder.group (directedComplex m (h.squared m)) p) →+ Chains n p
  | 0 =>
    { toFun := fun x => mapChains f 0 x.1 + mapChains g 0 x.2
      map_zero' := by simp [directedComplex]
      map_add' := by intros; simp [directedComplex]; abel }
  | p + 1 =>
    { toFun := fun x => mapChains f (p + 1) x.1 + mapChains g (p + 1) x.2.1 +
        prism f g hfg p x.2.2
      map_zero' := by simp [directedComplex]
      map_add' := by intros; simp [directedComplex]; abel }

/-- The positive relative prism is a genuine augmented directed chain map. -/
noncomputable def prismChainMap (h : NormalizedSimplexIdentities) {m n : ℕ}
    {A : Set (Fin (m + 1))} (hA : IsLowerSet A)
    (f g : Fin (m + 1) →o Fin (n + 1)) (hfg : ∀ i, f i ≤ g i)
    (hagree : ∀ x ∈ A, f x = g x)
    (hconstant : ∀ x ∉ A, ∀ y ∉ A, g x = g y) : Hom
    (rightCylinder (directedComplex m (h.squared m))) (directedComplex n (h.squared n)) where
  app := prismApp h f g hfg
  differential p x := by
    cases p with
    | zero =>
      change mapChains f 0 (differential m 0 x.1 - x.2.2) +
        mapChains g 0 (differential m 0 x.2.1 + x.2.2) =
        differential n 0 (mapChains f 1 x.1 + mapChains g 1 x.2.1 + prism f g hfg 0 x.2.2)
      simp only [map_add, map_sub]
      rw [prism_boundary_zero h f g hfg, ← h.naturality f 0 x.1,
        ← h.naturality g 0 x.2.1]
      abel
    | succ p =>
      change mapChains f (p + 1)
          (differential m (p + 1) x.1 - ((-1 : ℤ) ^ (p + 1)) • x.2.2) +
        mapChains g (p + 1)
          (differential m (p + 1) x.2.1 + ((-1 : ℤ) ^ (p + 1)) • x.2.2) +
        prism f g hfg p (differential m p x.2.2) =
        differential n (p + 1)
          (mapChains f (p + 2) x.1 + mapChains g (p + 2) x.2.1 +
            prism f g hfg (p + 1) x.2.2)
      simp only [map_add, map_sub, map_smul, prism_boundary h hA f g hfg hagree hconstant,
        smul_sub]
      rw [← h.naturality f (p + 1) x.1, ← h.naturality g (p + 1) x.2.1]
      abel
  augmentation x := by
    change augmentation n (mapChains f 0 x.1 + mapChains g 0 x.2) =
      augmentation m x.1 + augmentation m x.2
    simp only [map_add, augmentation_mapChains]
  positive p x hx := by
    cases p with
    | zero =>
      exact (positive n 0).add_mem (mapChains_positive f hx.1) (mapChains_positive g hx.2)
    | succ p =>
      exact (positive n (p + 1)).add_mem
        ((positive n (p + 1)).add_mem (mapChains_positive f hx.1) (mapChains_positive g hx.2.1))
        (prism_positive f g hfg hx.2.2)

/-- Strict realization of the explicitly constructed positive prism map. -/
noncomputable def strictPrism :
    StrictOmegaCategory.Hom
      (rightCylinder (directedComplex m (h.squared m))).realization
      (directedComplex n (h.squared n)).realization :=
  (prismChainMap h hA f g hfg hagree hconstant).realization

include hA hagree hconstant in
theorem prismChainMap_endpoint (a : Bool) (p : ℕ) (x : Chains m p) :
    (prismChainMap h hA f g hfg hagree hconstant).app p
      ((RightCylinder.endpoint (directedComplex m (h.squared m)) a).app p x) =
      mapChains (if a then g else f) p x := by
  cases p <;> cases a <;>
    simp [prismChainMap, prismApp, RightCylinder.endpoint, RightCylinder.endpointMap]

include hA hagree hconstant in
/-- The realized prism has exactly the two prescribed strict endpoint functors. -/
theorem strictPrism_endpoint (a : Bool)
    (x : (directedComplex m (h.squared m)).realization) :
    strictPrism h hA f g hfg hagree hconstant
      ((RightCylinder.endpoint (directedComplex m (h.squared m)) a).realization x) =
      (directedMap (h.squared m) (h.squared n) (if a then g else f)
        (h.naturality _)).realization x := by
  apply Cell.ext
  funext b p
  exact prismChainMap_endpoint h hA f g hfg hagree hconstant a p (x.table b p)

end Thomason.Construction.SimplexComplex

end

section

/-! # Degeneracy compatibility and stationarity of positive prisms -/

namespace Thomason.Construction.SimplexComplex

/-- A repeated lower image makes the entire normalized prism tuple zero. -/
theorem rise_eq_zero_of_not_strictMono {m n : ℕ}
    (f g : Fin (m + 1) →o Fin (n + 1)) (hfg : ∀ i, f i ≤ g i)
    (hf : ¬StrictMono f) : rise f g hfg = 0 := by
  have hn : ¬StrictMono (fun k => (append f (g (Fin.last m)) (hfg _)) (top (m + 1) k)) := by
    intro hs
    apply hf
    intro i j hij
    have hh := hs (Fin.castSucc_lt_castSucc_iff.mpr hij)
    change append f (g (Fin.last m)) (hfg _) i.castSucc <
      append f (g (Fin.last m)) (hfg _) j.castSucc at hh
    simpa only [append_castSucc] using hh
  simp only [rise, tuple, mapBasis, dite_eq_right hn]

/-- The prism operator commutes with all simplex maps, including degeneracies.
This is an equality in every chain degree, not just on top-dimensional atoms. -/
theorem prism_precomp {l m n : ℕ} (f g : Fin (m + 1) →o Fin (n + 1))
    (hfg : ∀ i, f i ≤ g i) (a : Fin (l + 1) →o Fin (m + 1)) (p : ℕ)
    (x : Chains l p) :
    prism f g hfg p (mapChains a p x) =
      prism (f.comp a) (g.comp a) (fun i => hfg (a i)) p x := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single s z =>
    simp only [mapChains_single, map_smul]
    rw [prism_single (f.comp a) (g.comp a) (fun i => hfg (a i)) p s z]
    apply congrArg (fun y => z • y)
    by_cases ha : StrictMono (fun i => a (s i))
    · let t : Basis m p := OrderEmbedding.ofStrictMono (fun i => a (s i)) ha
      have hm : mapBasis a p s = Finsupp.single t 1 := dite_eq_left ha
      rw [hm, prism_single, one_smul]
      rfl
    · have hm : mapBasis a p s = 0 := dite_eq_right ha
      rw [hm, map_zero]
      symm
      apply rise_eq_zero_of_not_strictMono
      intro hh
      apply ha
      intro i j hij
      exact lt_of_not_ge fun hle => (not_le_of_gt (hh hij)) (f.monotone hle)

/-- A pointwise fixed pair has a zero prism in every degree. -/
theorem prism_eq_zero_of_eq {m n : ℕ} (f g : Fin (m + 1) →o Fin (n + 1))
    (hfg : ∀ i, f i ≤ g i) (he : ∀ i, f i = g i) (p : ℕ) (x : Chains m p) :
    prism f g hfg p x = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single s z => simp only [prism_single, prismBasis_stationary f g hfg s (he _), smul_zero]

/-- Restricting to any simplex in the old part gives strict chain stationarity. -/
theorem prism_stationary {l m n : ℕ} {A : Set (Fin (m + 1))}
    (f g : Fin (m + 1) →o Fin (n + 1)) (hfg : ∀ i, f i ≤ g i)
    (hagree : ∀ i ∈ A, f i = g i) (a : Fin (l + 1) →o Fin (m + 1))
    (ha : ∀ i, a i ∈ A) (p : ℕ) (x : Chains l p) :
    prism f g hfg p (mapChains a p x) = 0 := by
  rw [prism_precomp]
  exact prism_eq_zero_of_eq _ _ _ (fun i => hagree (a i) (ha i)) p x

open _root_.OAI.Thomason.Construction.DirectedComplex

/-- Stationarity is an equality of the complete directed chain maps on the
old cylinder, including all lower-dimensional entries. -/
theorem prismChainMap_stationary (h : NormalizedSimplexIdentities) {l m n : ℕ}
    {A : Set (Fin (m + 1))} (hA : IsLowerSet A)
    (f g : Fin (m + 1) →o Fin (n + 1)) (hfg : ∀ i, f i ≤ g i)
    (hagree : ∀ i ∈ A, f i = g i)
    (hconstant : ∀ x ∉ A, ∀ y ∉ A, g x = g y)
    (a : Fin (l + 1) →o Fin (m + 1)) (ha : ∀ i, a i ∈ A)
    (p : ℕ) (x : RightCylinder.group (directedComplex l (h.squared l)) p) :
    (prismChainMap h hA f g hfg hagree hconstant).app p
      ((RightCylinder.map (directedMap (h.squared l) (h.squared m) a (h.naturality a))).app p x) =
      mapChains (f.comp a) p ((RightCylinder.projection (directedComplex l (h.squared l))).app p x) := by
  have hga : g.comp a = f.comp a := DFunLike.ext _ _ (fun i => (hagree (a i) (ha i)).symm)
  cases p with
  | zero =>
    change mapChains f 0 (mapChains a 0 x.1) + mapChains g 0 (mapChains a 0 x.2) =
      mapChains (f.comp a) 0 (x.1 + x.2)
    rw [mapChains_comp, mapChains_comp, hga, map_add]
  | succ p =>
    change mapChains f (p + 1) (mapChains a (p + 1) x.1) +
      mapChains g (p + 1) (mapChains a (p + 1) x.2.1) +
      prism f g hfg p (mapChains a p x.2.2) = mapChains (f.comp a) (p + 1) (x.1 + x.2.1)
    rw [mapChains_comp, mapChains_comp, hga, prism_stationary f g hfg hagree a ha, add_zero, map_add]

/-- The new relative prism is stationary as a strict functor after applying
Steiner realization; it is not merely zero on top chains. -/
theorem strictPrism_stationary (h : NormalizedSimplexIdentities) {l m n : ℕ}
    {A : Set (Fin (m + 1))} (hA : IsLowerSet A)
    (f g : Fin (m + 1) →o Fin (n + 1)) (hfg : ∀ i, f i ≤ g i)
    (hagree : ∀ i ∈ A, f i = g i)
    (hconstant : ∀ x ∉ A, ∀ y ∉ A, g x = g y)
    (a : Fin (l + 1) →o Fin (m + 1)) (ha : ∀ i, a i ∈ A)
    (x : (rightCylinder (directedComplex l (h.squared l))).realization) :
    strictPrism h hA f g hfg hagree hconstant
      ((RightCylinder.map (directedMap (h.squared l) (h.squared m) a (h.naturality a))).realization x) =
    (directedMap (h.squared l) (h.squared n) (f.comp a) (h.naturality _)).realization
      ((RightCylinder.projection (directedComplex l (h.squared l))).realization x) := by
  apply Cell.ext
  funext b p
  exact prismChainMap_stationary h hA f g hfg hagree hconstant a ha p (x.table b p)

end Thomason.Construction.SimplexComplex

end

section

/-!
# The right Gray interval adjunction and comparison

We first construct the cosimplicial strict right cylinders of the normalized
simplex complexes. `RightGrayInput` then records the right-interval
specialization of Ara--Maltsiniotis (2020), Theorem A.15 and Section A.16:
a right tensor functor with right adjoint, its endpoint/projection maps, and
the natural comparison on the actual oriental chain cylinders. These data specify the right tensor convention for the conditional
relative-prism construction.
-/

namespace Thomason.Construction

open CategoryTheory
open _root_.OAI.Thomason.Construction.DirectedComplex

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities)

noncomputable def cylinderObject (m : ℕ) : StrictOmegaCategory :=
  (rightCylinder (SimplexComplex.directedComplex m (h.squared m))).realization

noncomputable def cylinderMap {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) :
    h.cylinderObject m ⟶ h.cylinderObject n :=
  (RightCylinder.map (SimplexComplex.directedMap (h.squared m) (h.squared n)
    f (h.naturality f))).realization

theorem cylinderMap_id (m : ℕ) : h.cylinderMap (OrderHom.id : Fin (m + 1) →o Fin (m + 1)) =
    𝟙 (h.cylinderObject m) := by
  apply StrictOmegaCategory.Hom.ext
  funext x
  apply Cell.ext
  funext a p
  cases p with
  | zero =>
    change (SimplexComplex.mapChains OrderHom.id 0 (x.table a 0).1,
      SimplexComplex.mapChains OrderHom.id 0 (x.table a 0).2) = x.table a 0
    simp
  | succ p =>
    change (SimplexComplex.mapChains OrderHom.id (p + 1) (x.table a (p + 1)).1,
      SimplexComplex.mapChains OrderHom.id (p + 1) (x.table a (p + 1)).2.1,
      SimplexComplex.mapChains OrderHom.id p (x.table a (p + 1)).2.2) = x.table a (p + 1)
    simp

theorem cylinderMap_comp {l m n : ℕ} (f : Fin (l + 1) →o Fin (m + 1))
    (g : Fin (m + 1) →o Fin (n + 1)) : h.cylinderMap (g.comp f) = h.cylinderMap f ≫ h.cylinderMap g := by
  apply StrictOmegaCategory.Hom.ext
  funext x
  apply Cell.ext
  funext a p
  change (RightCylinder.map (SimplexComplex.directedMap (h.squared l) (h.squared n)
      (g.comp f) (h.naturality _))).app p (x.table a p) =
    (RightCylinder.map (SimplexComplex.directedMap (h.squared m) (h.squared n)
      g (h.naturality _))).app p
      ((RightCylinder.map (SimplexComplex.directedMap (h.squared l) (h.squared m)
        f (h.naturality _))).app p (x.table a p))
  cases p <;>
    simp [RightCylinder.map, RightCylinder.mapMap,
      SimplexComplex.directedMap, SimplexComplex.mapChains_comp]

/-- The cosimplicial diagram of the actual strict chain cylinders. -/
noncomputable def cylinderCosimplicial : SimplexCategory ⥤ StrictOmegaCategory.{0} where
  obj m := h.cylinderObject m.len
  map f := h.cylinderMap f.toOrderHom
  map_id m := h.cylinderMap_id m.len
  map_comp f g := h.cylinderMap_comp f.toOrderHom g.toOrderHom

noncomputable def cylinderEndpoint (a : Bool) : h.cosimplicial ⟶ h.cylinderCosimplicial where
  app m := (RightCylinder.endpoint (SimplexComplex.directedComplex m.len (h.squared m.len)) a).realization
  naturality m n f := by
    apply StrictOmegaCategory.Hom.ext
    funext x
    apply Cell.ext
    funext b p
    exact (RightCylinder.map_endpoint
      (SimplexComplex.directedMap (h.squared m.len) (h.squared n.len) f.toOrderHom
        (h.naturality f.toOrderHom)) a p (x.table b p)).symm

noncomputable def cylinderProjection : h.cylinderCosimplicial ⟶ h.cosimplicial where
  app m := (RightCylinder.projection (SimplexComplex.directedComplex m.len (h.squared m.len))).realization
  naturality m n f := by
    apply StrictOmegaCategory.Hom.ext
    funext x
    apply Cell.ext
    funext b p
    exact RightCylinder.projection_map
      (SimplexComplex.directedMap (h.squared m.len) (h.squared n.len) f.toOrderHom
        (h.naturality f.toOrderHom)) p (x.table b p)

end NormalizedSimplexIdentities

/-- The exact published input about tensoring with the oriented interval.
The natural isomorphism compares to the explicitly constructed chain tensor;
its endpoint and projection equations fix the right-tensor convention. -/
structure RightGrayInput (h : NormalizedSimplexIdentities) where
  cylinder : StrictOmegaCategory.{0} ⥤ StrictOmegaCategory.{0}
  internalHom : StrictOmegaCategory.{0} ⥤ StrictOmegaCategory.{0}
  adjunction : cylinder ⊣ internalHom
  endpoint : Bool → (𝟭 StrictOmegaCategory.{0} ⟶ cylinder)
  projection : cylinder ⟶ 𝟭 StrictOmegaCategory.{0}
  endpoint_projection (a : Bool) (C : StrictOmegaCategory.{0}) :
    (endpoint a).app C ≫ projection.app C = 𝟙 C
  simplexComparison : h.cylinderCosimplicial ≅ h.cosimplicial ⋙ cylinder
  endpoint_comparison (a : Bool) (m : SimplexCategory) :
    (h.cylinderEndpoint a).app m ≫ simplexComparison.hom.app m =
      (endpoint a).app (h.object m.len)
  projection_comparison (m : SimplexCategory) :
    simplexComparison.hom.app m ≫ projection.app (h.object m.len) =
      h.cylinderProjection.app m

namespace RightGrayInput

variable {h : NormalizedSimplexIdentities} (G : RightGrayInput h)

/-- Cocontinuity follows from the published right internal-hom adjunction. -/
theorem preservesColimits : Limits.PreservesColimitsOfSize.{0, 0} G.cylinder := by
  have := G.adjunction.isLeftAdjoint
  infer_instance

/-- The constructed chain prism transported through the published comparison. -/
noncomputable def prism {m n : ℕ} {A : Set (Fin (m + 1))} (hA : IsLowerSet A)
    (f g : Fin (m + 1) →o Fin (n + 1)) (hfg : ∀ i, f i ≤ g i)
    (hagree : ∀ i ∈ A, f i = g i) (hconstant : ∀ x ∉ A, ∀ y ∉ A, g x = g y) :
    G.cylinder.obj (h.object m) ⟶ h.object n :=
  G.simplexComparison.inv.app (.mk m) ≫
    SimplexComplex.strictPrism h hA f g hfg hagree hconstant

/-- The comparison preserves the two endpoint functors of the new prism. -/
theorem prism_endpoint {m n : ℕ} {A : Set (Fin (m + 1))} (hA : IsLowerSet A)
    (f g : Fin (m + 1) →o Fin (n + 1)) (hfg : ∀ i, f i ≤ g i)
    (hagree : ∀ i ∈ A, f i = g i) (hconstant : ∀ x ∉ A, ∀ y ∉ A, g x = g y)
    (a : Bool) :
    (G.endpoint a).app (h.object m) ≫ G.prism hA f g hfg hagree hconstant =
      h.map (if a then g else f) := by
  let e : h.object m ⟶ h.cylinderObject m := (h.cylinderEndpoint a).app (.mk m)
  let i : h.cylinderObject m ≅ G.cylinder.obj (h.object m) :=
    G.simplexComparison.app (.mk m)
  let P : h.cylinderObject m ⟶ h.object n :=
    SimplexComplex.strictPrism h hA f g hfg hagree hconstant
  have he : e ≫ i.hom = (G.endpoint a).app (h.object m) :=
    G.endpoint_comparison a (.mk m)
  change (G.endpoint a).app (h.object m) ≫ (i.inv ≫ P) = _
  calc
    _ = (e ≫ i.hom) ≫ (i.inv ≫ P) :=
      congrArg (fun k => k ≫ (i.inv ≫ P)) he.symm
    _ = e ≫ P := by simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = h.map (if a then g else f) := by
      apply StrictOmegaCategory.Hom.ext
      funext x
      exact SimplexComplex.strictPrism_endpoint h hA f g hfg hagree hconstant a x

/-- Stationarity of the complete strict chain prism passes to the right
Gray cylinder along the published natural comparison. -/
theorem prism_stationary {l m n : ℕ} {A : Set (Fin (m + 1))} (hA : IsLowerSet A)
    (f g : Fin (m + 1) →o Fin (n + 1)) (hfg : ∀ i, f i ≤ g i)
    (hagree : ∀ i ∈ A, f i = g i) (hconstant : ∀ x ∉ A, ∀ y ∉ A, g x = g y)
    (a : Fin (l + 1) →o Fin (m + 1)) (ha : ∀ i, a i ∈ A) :
    G.cylinder.map (h.map a) ≫ G.prism hA f g hfg hagree hconstant =
      G.projection.app (h.object l) ≫ h.map (f.comp a) := by
  let il : h.cylinderObject l ≅ G.cylinder.obj (h.object l) :=
    G.simplexComparison.app (.mk l)
  let im : h.cylinderObject m ≅ G.cylinder.obj (h.object m) :=
    G.simplexComparison.app (.mk m)
  let P : h.cylinderObject m ⟶ h.object n :=
    SimplexComplex.strictPrism h hA f g hfg hagree hconstant
  let ca : h.cylinderObject l ⟶ h.cylinderObject m := h.cylinderMap a
  let cp : h.cylinderObject l ⟶ h.object l := h.cylinderProjection.app (.mk l)
  let v : h.object l ⟶ h.object n := h.map (f.comp a)
  have hn : G.cylinder.map (h.map a) ≫ im.inv = il.inv ≫ ca :=
    G.simplexComparison.inv.naturality (SimplexCategory.Hom.mk a)
  have hp : ca ≫ P = cp ≫ v := by
    apply StrictOmegaCategory.Hom.ext
    funext x
    exact SimplexComplex.strictPrism_stationary h hA f g hfg hagree hconstant a ha x
  have hcp : il.hom ≫ G.projection.app (h.object l) = cp :=
    G.projection_comparison (.mk l)
  have hproj : il.inv ≫ cp = G.projection.app (h.object l) := by
    calc
      _ = il.inv ≫ (il.hom ≫ G.projection.app (h.object l)) :=
        congrArg (fun k => il.inv ≫ k) hcp.symm
      _ = _ := il.inv_hom_id_assoc _
  change G.cylinder.map (h.map a) ≫ (im.inv ≫ P) = G.projection.app (h.object l) ≫ v
  calc
    _ = (G.cylinder.map (h.map a) ≫ im.inv) ≫ P := (Category.assoc _ _ _).symm
    _ = (il.inv ≫ ca) ≫ P := congrArg (fun k => k ≫ P) hn
    _ = il.inv ≫ (ca ≫ P) := Category.assoc _ _ _
    _ = il.inv ≫ (cp ≫ v) := congrArg (fun k => il.inv ≫ k) hp
    _ = (il.inv ≫ cp) ≫ v := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun k => k ≫ v) hproj

end RightGrayInput

end Thomason.Construction

end

section

/-!
# Assembly of compatible strict cylinders

This is the colimit step in the relative-prism construction. It uses
cocontinuity of the right Gray tensor, proved from the published adjunction.
The compatibility hypotheses concern the local maps being glued, not a
model-structure or couniversality conclusion.
-/

namespace Thomason.Construction.RightGrayInput

open CategoryTheory CategoryTheory.Limits

variable {h : NormalizedSimplexIdentities} (G : RightGrayInput h)
  {J : Type} [SmallCategory J] {D : J ⥤ StrictOmegaCategory.{0}}
  {c : Cocone D} (hc : IsColimit c)

include hc

/-- Equality on all simplex cylinders is equality on the colimit cylinder. -/
theorem cylinder_hom_ext {Y : StrictOmegaCategory.{0}}
    {P Q : G.cylinder.obj c.pt ⟶ Y}
    (he : ∀ j, G.cylinder.map (c.ι.app j) ≫ P = G.cylinder.map (c.ι.app j) ≫ Q) : P = Q := by
  have := G.preservesColimits
  exact (isColimitOfPreserves G.cylinder hc).hom_ext he

/-- Compatible local strict cylinders assemble to a unique whole cylinder. -/
theorem assemble_cylinder {Y : StrictOmegaCategory.{0}}
    (P : ∀ j, G.cylinder.obj (D.obj j) ⟶ Y)
    (hP : ∀ {i j} (a : i ⟶ j), G.cylinder.map (D.map a) ≫ P j = P i) :
    ∃! Q : G.cylinder.obj c.pt ⟶ Y,
      ∀ j, G.cylinder.map (c.ι.app j) ≫ Q = P j := by
  have := G.preservesColimits
  let t : Cocone (D ⋙ G.cylinder) :=
    { pt := Y
      ι := { app := P, naturality := fun i j a => by simpa using hP a } }
  let hgc := isColimitOfPreserves G.cylinder hc
  refine ⟨hgc.desc t, hgc.fac t, ?_⟩
  intro Q hQ
  exact hgc.hom_ext (fun j => (hQ j).trans (hgc.fac t j).symm)

/-- The endpoint of an assembled cylinder is the map prescribed on every
piece of the colimit. -/
theorem assembled_endpoint {Y : StrictOmegaCategory.{0}}
    (P : G.cylinder.obj c.pt ⟶ Y) (F : c.pt ⟶ Y) (a : Bool)
    (hF : ∀ j, (G.endpoint a).app (D.obj j) ≫ G.cylinder.map (c.ι.app j) ≫ P =
      c.ι.app j ≫ F) :
    (G.endpoint a).app c.pt ≫ P = F := by
  apply hc.hom_ext
  intro j
  let i : D.obj j ⟶ c.pt := c.ι.app j
  have hn : i ≫ (G.endpoint a).app c.pt = (G.endpoint a).app (D.obj j) ≫ G.cylinder.map i :=
    (G.endpoint a).naturality i
  change i ≫ ((G.endpoint a).app c.pt ≫ P) = i ≫ F
  calc
    _ = (i ≫ (G.endpoint a).app c.pt) ≫ P := (Category.assoc _ _ _).symm
    _ = ((G.endpoint a).app (D.obj j) ≫ G.cylinder.map i) ≫ P := congrArg (fun k => k ≫ P) hn
    _ = _ := (Category.assoc _ _ _).trans (hF j)

/-- To prove stationarity on a subcategory presented as a colimit, it
suffices to prove the factorization on the whole cylinder of every piece. -/
theorem assembled_stationary {X Y : StrictOmegaCategory.{0}}
    (a : c.pt ⟶ X) (v : c.pt ⟶ Y) (P : G.cylinder.obj X ⟶ Y)
    (hs : ∀ j, G.cylinder.map (c.ι.app j ≫ a) ≫ P =
      G.projection.app (D.obj j) ≫ (c.ι.app j ≫ v)) :
    G.cylinder.map a ≫ P = G.projection.app c.pt ≫ v := by
  apply G.cylinder_hom_ext hc
  intro j
  calc
    _ = G.cylinder.map (c.ι.app j ≫ a) ≫ P := by rw [G.cylinder.map_comp, Category.assoc]
    _ = G.projection.app (D.obj j) ≫ (c.ι.app j ≫ v) := hs j
    _ = (G.cylinder.map (c.ι.app j) ≫ G.projection.app c.pt) ≫ v := by
      let i : D.obj j ⟶ c.pt := c.ι.app j
      have hn : G.cylinder.map i ≫ G.projection.app c.pt = G.projection.app (D.obj j) ≫ i :=
        G.projection.naturality i
      exact (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ v) hn.symm)
    _ = _ := Category.assoc _ _ _

end Thomason.Construction.RightGrayInput

end

end OAI
