import OAI.CategoryTheory.Thomason.Chains.FinalPositiveSimplexSupport
import OAI.CategoryTheory.Thomason.Strict.StrictIsomorphisms
import Mathlib.Order.Fin.InsertNth

namespace OAI

section

/-! # Naturality of normalized simplex chains

For a monotone vertex map, nondegenerate images commute with deletion. In a
degenerate image, choose an adjacent equal pair: every other face vanishes,
and the two remaining faces coincide with opposite signs.
-/

namespace Thomason.Construction.SimplexComplex

open scoped BigOperators

/-- The image chain depends only on the composite vertex function. -/
theorem mapBasis_congr {m n p : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (s t : Basis m p) (h : ∀ i, f (s i) = f (t i)) :
    mapBasis f p s = mapBasis f p t := by
  unfold mapBasis
  simp only [funext h]

/-- A nondegenerate image commutes with deleting a vertex. -/
theorem mapBasis_delete_strict {m n p : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (s : Basis m (p + 1)) (hf : StrictMono (fun i => f (s i))) (i : Fin (p + 2)) :
    mapBasis f p (deleteVertex s i) =
      Finsupp.single (deleteVertex (OrderEmbedding.ofStrictMono _ hf) i) 1 := by
  have hi : StrictMono (fun k => f (deleteVertex s i k)) :=
    hf.comp (Fin.strictMono_succAbove i)
  rw [mapBasis, dite_eq_left hi]
  rfl

/-- Deleting either member of an adjacent equal pair gives the same image. -/
theorem mapBasis_delete_equal {m n p : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (s : Basis m (p + 1)) (i : Fin (p + 1)) (hi : f (s i.castSucc) = f (s i.succ)) :
    mapBasis f p (deleteVertex s i.castSucc) =
      mapBasis f p (deleteVertex s i.succ) := by
  apply mapBasis_congr
  intro k
  change f (s (i.castSucc.succAbove k)) = f (s (i.succ.succAbove k))
  rcases lt_trichotomy k i with h | rfl | h
  · rw [Fin.succAbove_castSucc_of_lt _ _ h,
      Fin.succAbove_succ_of_le _ _ h.le]
  · simpa only [Fin.succAbove_castSucc_self, Fin.succAbove_succ_self] using hi.symm
  · rw [Fin.succAbove_castSucc_of_le _ _ h.le,
      Fin.succAbove_succ_of_lt _ _ h]

/-- A face which retains an equal pair has zero normalized image. -/
theorem mapBasis_delete_vanish {m n p : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (s : Basis m (p + 1)) (i : Fin (p + 1)) (hi : f (s i.castSucc) = f (s i.succ))
    (j : Fin (p + 2)) (hja : j ≠ i.castSucc) (hjb : j ≠ i.succ) :
    mapBasis f p (deleteVertex s j) = 0 := by
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hja.symm
  obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hjb.symm
  have hn : ¬StrictMono (fun k => f (deleteVertex s j k)) := by
    intro hk
    have hab : a = b := hk.injective (by
      change f (s (j.succAbove a)) = f (s (j.succAbove b))
      rw [ha, hb]
      exact hi)
    have he : i.castSucc = i.succ := ha.symm.trans ((congrArg j.succAbove hab).trans hb)
    exact (ne_of_lt i.castSucc_lt_succ) he
  exact dite_eq_right hn

/-- Any degenerate monotone image has an adjacent equal pair. -/
theorem exists_adjacent_equal {m n p : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (s : Basis m (p + 1)) (hf : ¬StrictMono (fun i => f (s i))) :
    ∃ i : Fin (p + 1), f (s i.castSucc) = f (s i.succ) := by
  by_contra! hn
  apply hf
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  exact lt_of_le_of_ne (f.monotone (s.monotone i.castSucc_le_succ)) (hn i)

/-- Naturality on one nondegenerate source simplex, including degenerate images. -/
theorem differential_mapBasis {m n p : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (s : Basis m (p + 1)) :
    mapChains f p (differentialBasis m p s) = differential n p (mapBasis f (p + 1) s) := by
  classical
  by_cases hf : StrictMono (fun i => f (s i))
  · rw [mapBasis, dite_eq_left hf, differential_single, one_smul]
    simp only [differentialBasis, map_sum, mapChains_single, mapBasis_delete_strict f s hf,
      Finsupp.smul_single, smul_eq_mul, mul_one]
  · obtain ⟨i, hi⟩ := exists_adjacent_equal f s hf
    rw [mapBasis, dite_eq_right hf, map_zero]
    simp only [differentialBasis, map_sum, mapChains_single]
    let term (j : Fin (p + 2)) : Chains n p :=
      ((-1 : ℤ) ^ j.val) • mapBasis f p (deleteVertex s j)
    change (∑ j, term j) = 0
    have hab : i.castSucc ≠ i.succ := ne_of_lt i.castSucc_lt_succ
    have hs : (∑ j, term j) = term i.castSucc + term i.succ := by
      calc
        _ = ∑ j ∈ ({i.castSucc, i.succ} : Finset (Fin (p + 2))), term j := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro j _ hj
          have hj' : j ≠ i.castSucc ∧ j ≠ i.succ := by simpa using hj
          simp only [term, mapBasis_delete_vanish f s i hi j hj'.1 hj'.2, smul_zero]
        _ = _ := Finset.sum_pair hab
    rw [hs]
    dsimp [term]
    rw [mapBasis_delete_equal f s i hi]
    simp only [pow_succ, mul_neg_one, neg_smul,
      add_neg_cancel]

/-- The concrete normalized differential is natural under every monotone map. -/
theorem boundaryNaturality {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) :
    BoundaryNaturality f := by
  intro p x
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single s z => simp [differential_mapBasis]

end SimplexComplex

/-- The normalized simplex differential squares to zero and is natural. -/
theorem normalizedSimplexIdentities : NormalizedSimplexIdentities where
  squared := SimplexComplex.boundarySquared
  naturality := SimplexComplex.boundaryNaturality

end Thomason.Construction

end

section

/-!
# Normalized tuple calculus for the relative prism

A weakly increasing tuple denotes its normalized simplex chain: repetitions
are sent to zero. The boundary formula, including tuples with repetitions,
follows from naturality of normalized chains.
-/

namespace Thomason.Construction.SimplexComplex

open scoped BigOperators

/-- The top basis simplex on its own set of vertices. -/
def top (p : ℕ) : Basis p p := (OrderIso.refl _).toOrderEmbedding

/-- The normalized chain represented by a weakly increasing tuple. -/
noncomputable def tuple {n p : ℕ} (f : Fin (p + 1) →o Fin (n + 1)) : Chains n p :=
  mapBasis f p (top p)

/-- Delete one entry of a weakly increasing tuple. -/
def deleteTuple {n p : ℕ} (f : Fin (p + 2) →o Fin (n + 1)) (i : Fin (p + 2)) :
    Fin (p + 1) →o Fin (n + 1) := f.comp (Fin.succAboveOrderEmb i).toOrderHom

theorem mapBasis_eq_tuple {m n p : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (s : Basis m p) : mapBasis f p s = tuple (f.comp s.toOrderHom) := rfl

/-- Composition acts on normalized tuples, including zero/degenerate tuples. -/
theorem mapChains_tuple {m n p : ℕ} (f : Fin (p + 1) →o Fin (m + 1))
    (g : Fin (m + 1) →o Fin (n + 1)) :
    mapChains g p (tuple f) = tuple (g.comp f) := mapBasis_comp f g (top p)

/-- The usual alternating boundary formula remains valid for every monotone
list. This includes degenerate lists, for which the nonzero faces cancel. -/
theorem differential_tuple (h : NormalizedSimplexIdentities) {n p : ℕ}
    (f : Fin (p + 2) →o Fin (n + 1)) :
    differential n p (tuple f) =
      ∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) • tuple (deleteTuple f i) := by
  have hf := h.naturality f p (Finsupp.single (top (p + 1)) 1)
  simp only [differential_single, one_smul, mapChains_single] at hf
  change differential n p (mapBasis f (p + 1) (top (p + 1))) = _
  rw [← hf]
  simp only [differentialBasis, map_sum, mapChains_single]
  rfl

/-- A tuple with two specified equal entries is zero in normalized chains. -/
theorem tuple_eq_zero_of_repeat {n p : ℕ} (f : Fin (p + 1) →o Fin (n + 1))
    {i j : Fin (p + 1)} (hij : i < j) (he : f i = f j) : tuple f = 0 := by
  have hn : ¬StrictMono (fun k => f (top p k)) := by
    intro hs
    have hl := hs hij
    change f i < f j at hl
    exact (ne_of_lt hl) he
  simp only [tuple, mapBasis, dite_eq_right hn]

theorem tuple_nonneg {n p : ℕ} (f : Fin (p + 1) →o Fin (n + 1))
    (s : Basis n p) : 0 ≤ tuple f s := mapBasis_nonneg f (top p) s

/-- Append one upper vertex to a monotone tuple. -/
def append {n p : ℕ} (f : Fin (p + 1) →o Fin (n + 1)) (b : Fin (n + 1))
    (hb : f (Fin.last p) ≤ b) : Fin (p + 2) →o Fin (n + 1) where
  toFun := Fin.snoc (fun i => f i) b
  monotone' := by
    simpa only [Fin.insertNth_last'] using Fin.insertNth_last_monotone f.monotone b hb

@[simp]
theorem append_castSucc {n p : ℕ} (f : Fin (p + 1) →o Fin (n + 1)) (b) (hb)
    (i : Fin (p + 1)) : append f b hb i.castSucc = f i := by
  change Fin.snoc (α := fun _ => Fin (n + 1)) (fun j => f j) b i.castSucc = f i
  simp only [Fin.snoc_castSucc]

@[simp]
theorem append_last {n p : ℕ} (f : Fin (p + 1) →o Fin (n + 1)) (b) (hb) :
    append f b hb (Fin.last (p + 1)) = b := by
  change Fin.snoc (α := fun _ => Fin (n + 1)) (fun j => f j) b (Fin.last (p + 1)) = b
  simp only [Fin.snoc_last]

def initial {n p : ℕ} (f : Fin (p + 2) →o Fin (n + 1)) :
    Fin (p + 1) →o Fin (n + 1) := f.comp (Fin.castSuccOrderEmb).toOrderHom

@[simp]
theorem initial_apply {n p : ℕ} (f : Fin (p + 2) →o Fin (n + 1))
    (i : Fin (p + 1)) : initial f i = f i.castSucc := rfl

theorem append_initial {n p : ℕ} (f : Fin (p + 2) →o Fin (n + 1)) :
    append (initial f) (f (Fin.last (p + 1)))
      (f.monotone (Fin.le_last _)) = f := by
  apply DFunLike.ext
  intro i
  induction i using Fin.lastCases with
  | last => exact append_last _ _ _
  | cast i => exact append_castSucc _ _ _ i

/-- Appending a repeated final vertex gives the zero normalized chain. -/
theorem tuple_append_eq_zero {n p : ℕ} (f : Fin (p + 1) →o Fin (n + 1)) (b) (hb)
    (he : f (Fin.last p) = b) : tuple (append f b hb) = 0 := by
  apply tuple_eq_zero_of_repeat _ (Fin.castSucc_lt_last (Fin.last p))
  simpa only [append_castSucc, append_last] using he

theorem delete_append_last {n p : ℕ} (f : Fin (p + 1) →o Fin (n + 1)) (b) (hb) :
    deleteTuple (append f b hb) (Fin.last (p + 1)) = f := by
  apply DFunLike.ext
  intro i
  change append f b hb ((Fin.last (p + 1)).succAbove i) = f i
  rw [Fin.succAbove_last]
  exact append_castSucc f b hb i

theorem delete_append_castSucc {n p : ℕ} (f : Fin (p + 2) →o Fin (n + 1)) (b) (hb)
    (i : Fin (p + 2)) :
    deleteTuple (append f b hb) i.castSucc =
      append (deleteTuple f i) b ((f.monotone (Fin.le_last _)).trans hb) := by
  apply DFunLike.ext
  intro j
  induction j using Fin.lastCases with
  | last =>
    change append f b hb (i.castSucc.succAbove (Fin.last (p + 1))) = _
    rw [Fin.succAbove_ne_last_last (Fin.castSucc_ne_last i)]
    exact (append_last f b hb).trans (append_last _ b _).symm
  | cast j =>
    change append f b hb (i.castSucc.succAbove j.castSucc) = _
    rw [Fin.castSucc_succAbove_castSucc]
    exact (append_castSucc f b hb _).trans
      (append_castSucc (deleteTuple f i) b _ j).symm

/-- The two exceptional faces in the relative prism cancel to the target
endpoint. The alternatives express exactly the old-initial/new-tail split. -/
theorem prism_last_face_cancel {n p : ℕ}
    (f g : Fin (p + 2) →o Fin (n + 1)) (hfg : ∀ i, f i ≤ g i)
    (hcases : (∀ i : Fin (p + 1), f i.castSucc = g i.castSucc) ∨
      g (Fin.last (p + 1)) = g (Fin.last p).castSucc) :
    tuple (append (initial f) (g (Fin.last (p + 1)))
      ((hfg _).trans (g.monotone (Fin.le_last _)))) -
    tuple (append (initial f) (g (Fin.last p).castSucc) (hfg _)) = tuple g := by
  rcases hcases with hold | hnew
  · have hz := tuple_append_eq_zero (initial f) (g (Fin.last p).castSucc) (hfg _)
      (hold (Fin.last p))
    have he : append (initial f) (g (Fin.last (p + 1)))
        ((hfg _).trans (g.monotone (Fin.le_last _))) = g := by
      apply DFunLike.ext
      intro i
      induction i using Fin.lastCases with
      | last => exact append_last _ _ _
      | cast i => exact (append_castSucc _ _ _ i).trans (hold i)
    rw [hz, sub_zero, he]
  · have he : append (initial f) (g (Fin.last (p + 1)))
        ((hfg _).trans (g.monotone (Fin.le_last _))) =
      append (initial f) (g (Fin.last p).castSucc) (hfg _) := by
      apply DFunLike.ext
      intro i
      induction i using Fin.lastCases with
      | last => exact (append_last _ _ _).trans (hnew.trans (append_last _ _ _).symm)
      | cast i => exact (append_castSucc _ _ _ i).trans (append_castSucc _ _ _ i).symm
    rw [he, sub_self]
    exact (tuple_eq_zero_of_repeat g (Fin.castSucc_lt_last (Fin.last p)) hnew.symm).symm

end Thomason.Construction.SimplexComplex

end

end OAI
