import Mathlib
import OAI.CategoryTheory.Thomason.Globes
import OAI.CategoryTheory.Thomason.SimplexRanks

namespace OAI

/-! Horn Realization. -/

noncomputable section
universe u v w z


namespace Thomason.WeakHomotopy

open scoped unitInterval Topology Topology.Homotopy
open CubeExtension

variable {N : Type u} [Fintype N] [Nonempty N]
variable {X : Type v} {Y : Type w} {Z : Type z}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

lemma move_natural (f : C(X,Y)) {a b : X} (γ : Path a b) (p : GenLoop N X a)
    (q : I × I^N) :
    move (loopMap N f a p) (γ.map f.continuous) q = f (move p γ q) :=
  extend_natural
    ⟨fun z : Unit × I^N => p z.2, p.val.continuous.comp continuous_snd⟩
    ⟨fun z : Unit × I => γ z.2, γ.continuous.comp continuous_snd⟩
    (fun _ x hx => (p.property x hx).trans γ.source.symm) f ((),q)

lemma transport_natural (f : C(X,Y)) {a b : X} (γ : Path a b)
    (p : HomotopyGroup N X a) :
    transport (γ.map f.continuous) (groupMap N f a p) =
      groupMap N f b (transport γ p) := by
  induction p using Quotient.inductionOn with
  | h p =>
    apply congrArg Quotient.mk''
    apply GenLoop.ext
    intro x
    exact move_natural f γ p (1,x)

lemma groupMap_bijective_along_path (f : C(X,Y)) {a b : X} (γ : Path a b)
    (h : Function.Bijective (groupMap N f a)) :
    Function.Bijective (groupMap N f b) := by
  have ht := (transport_bijective (N := N) (γ.map f.continuous)).comp h
  have he : transport (N := N) (γ.map f.continuous) ∘ groupMap N f a =
      groupMap N f b ∘ transport γ := funext (transport_natural f γ)
  rw [he] at ht
  exact (Function.Bijective.of_comp_iff _ (transport_bijective γ)).mp ht

lemma groupMap_comp (N : Type*) (f : C(X,Y)) (g : C(Y,Z)) (x : X) :
    groupMap N (g.comp f) x = groupMap N g (f x) ∘ groupMap N f x := by
  funext p
  induction p using Quotient.inductionOn with
  | h p => rfl

lemma groupMap_id (N : Type*) (x : X) : groupMap N (.id X) x = id := by
  funext p
  exact basedGroupMap_id N x p

lemma equivalence_id : Equivalence (.id X) := by
  constructor
  · have he : componentsMap (.id X) = id := funext componentsMap_id
    rw [he]
    exact Function.bijective_id
  · intro n x
    rw [groupMap_id]
    exact Function.bijective_id

lemma Equivalence.comp {f : C(X,Y)} {g : C(Y,Z)} (hf : Equivalence f) (hg : Equivalence g) :
    Equivalence (g.comp f) := by
  constructor
  · have he : componentsMap (g.comp f) = componentsMap g ∘ componentsMap f :=
      (funext (componentsMap_comp f g)).symm
    rw [he]
    exact hg.1.comp hf.1
  · intro n x
    rw [groupMap_comp]
    exact (hg.2 n (f x)).comp (hf.2 n x)

lemma Equivalence.of_comp_right {f : C(X,Y)} {g : C(Y,Z)}
    (hfg : Equivalence (g.comp f)) (hg : Equivalence g) : Equivalence f := by
  constructor
  · have he : componentsMap (g.comp f) = componentsMap g ∘ componentsMap f :=
      (funext (componentsMap_comp f g)).symm
    have ht := hfg.1
    rw [he] at ht
    exact (Function.Bijective.of_comp_iff' hg.1 _).mp ht
  · intro n x
    have ht := hfg.2 n x
    rw [groupMap_comp] at ht
    exact (Function.Bijective.of_comp_iff' (hg.2 n (f x)) _).mp ht

lemma Equivalence.of_comp_left {f : C(X,Y)} {g : C(Y,Z)}
    (hfg : Equivalence (g.comp f)) (hf : Equivalence f) : Equivalence g := by
  constructor
  · have he : componentsMap (g.comp f) = componentsMap g ∘ componentsMap f :=
      (funext (componentsMap_comp f g)).symm
    have ht := hfg.1
    rw [he] at ht
    exact (Function.Bijective.of_comp_iff _ hf.1).mp ht
  · intro n y
    obtain ⟨c, hc⟩ := hf.1.surjective (ZerothHomotopy.mk y)
    induction c using ZerothHomotopy.rec with
    | mk x =>
      have he : ZerothHomotopy.mk (f x) = ZerothHomotopy.mk y := hc
      obtain ⟨γ⟩ : Nonempty (Path (f x) y) := Quotient.exact he
      apply groupMap_bijective_along_path g γ
      have ht := hfg.2 n x
      rw [groupMap_comp] at ht
      exact (Function.Bijective.of_comp_iff _ (hf.2 n x)).mp ht

lemma groupMap_homotopy (N : Type u) [Fintype N] [Nonempty N]
    {f g : C(X,Y)} (H : f.Homotopy g) (x : X) (p : HomotopyGroup N X x) :
    transport (N := N)
      (⟨⟨fun t => H (t,x), H.continuous.comp (continuous_id.prodMk continuous_const)⟩,
        H.apply_zero x, H.apply_one x⟩ : Path (f x) (g x))
      (groupMap N f x p) = groupMap N g x p := by
  induction p using Quotient.inductionOn with
  | h p =>
    apply Quotient.sound
    apply transportLoop_homotopic_of_homotopy (loopMap N f x p) (loopMap N g x p)
      _ ⟨fun q => H (q.1,p q.2), H.continuous.comp
        (continuous_fst.prodMk (p.val.continuous.comp continuous_snd))⟩
    · exact fun y => H.apply_zero (p y)
    · exact fun y => H.apply_one (p y)
    · intro t y hy
      change H (t,p.val y) = H (t,x)
      rw [p.property y hy]

lemma Equivalence.of_homotopic {f g : C(X,Y)} (hf : Equivalence f) (H : f.Homotopic g) :
    Equivalence g := by
  obtain ⟨H⟩ := H
  constructor
  · have he : componentsMap f = componentsMap g :=
      funext (componentsMap_homotopic ⟨H⟩)
    rw [← he]
    exact hf.1
  · intro n x
    let γ : Path (f x) (g x) :=
      ⟨⟨fun t => H (t,x), H.continuous.comp (continuous_id.prodMk continuous_const)⟩,
        H.apply_zero x, H.apply_one x⟩
    have ht := (transport_bijective (N := Fin (n+1)) γ).comp (hf.2 n x)
    have he : transport γ ∘ groupMap (Fin (n+1)) f x = groupMap (Fin (n+1)) g x :=
      funext (groupMap_homotopy _ H x)
    rwa [he] at ht

end Thomason.WeakHomotopy

end

noncomputable section
universe u v w z


namespace Thomason.WeakHomotopy

open scoped Topology Topology.Homotopy

variable {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']

lemma bijective_of_retract {A B A' B' : Type*}
    (f : A → B) (g : A' → B') (i : A → A') (j : B → B') (r : A' → A) (s : B' → B)
    (hri : Function.LeftInverse r i) (hsj : Function.LeftInverse s j)
    (hgi : ∀ x, g (i x) = j (f x)) (hfr : ∀ x, f (r x) = s (g x))
    (hg : Function.Bijective g) : Function.Bijective f := by
  constructor
  · intro a b hab
    apply hri.injective
    apply hg.injective
    rw [hgi, hgi, hab]
  · intro b
    obtain ⟨a, ha⟩ := hg.surjective (j b)
    exact ⟨r a, by rw [hfr, ha, hsj]⟩

lemma basedGroupMap_bijective (N : Type*) (f : C(X,Y)) (x : X) (y : Y) (h : f x = y)
    (hf : Function.Bijective (groupMap N f x)) :
    Function.Bijective (basedGroupMap N f x y h) := by
  subst y
  exact hf

lemma Equivalence.of_retract (f : C(X,Y)) (g : C(X',Y'))
    (i : C(X,X')) (j : C(Y,Y')) (r : C(X',X)) (s : C(Y',Y))
    (hri : r.comp i = .id X) (hsj : s.comp j = .id Y)
    (hgi : g.comp i = j.comp f) (hfr : f.comp r = s.comp g)
    (hg : Equivalence g) : Equivalence f := by
  constructor
  · apply bijective_of_retract (componentsMap f) (componentsMap g)
      (componentsMap i) (componentsMap j) (componentsMap r) (componentsMap s)
    · intro x
      rw [componentsMap_comp, hri, componentsMap_id]
    · intro y
      rw [componentsMap_comp, hsj, componentsMap_id]
    · intro x
      rw [componentsMap_comp, componentsMap_comp, hgi]
    · intro y
      rw [componentsMap_comp, componentsMap_comp, hfr]
    · exact hg.1
  · intro n x
    let N := Fin (n+1)
    have hir : r (i x) = x := ContinuousMap.congr_fun hri x
    have hjs : s (j (f x)) = f x := ContinuousMap.congr_fun hsj (f x)
    have hig : g (i x) = j (f x) := ContinuousMap.congr_fun hgi x
    change Function.Bijective (basedGroupMap N f x (f x) rfl)
    apply bijective_of_retract _ (basedGroupMap N g (i x) (j (f x)) hig)
      (basedGroupMap N i x (i x) rfl) (basedGroupMap N j (f x) (j (f x)) rfl)
      (basedGroupMap N r (i x) x hir) (basedGroupMap N s (j (f x)) (f x) hjs)
    · intro p
      rw [basedGroupMap_comp]
      have ht (h : (r.comp i) x = x) :
          basedGroupMap N (r.comp i) x x h p = p := by
        simpa only [hri] using basedGroupMap_id N x p
      exact ht _
    · intro p
      rw [basedGroupMap_comp]
      have ht (h : (s.comp j) (f x) = f x) :
          basedGroupMap N (s.comp j) (f x) (f x) h p = p := by
        simpa only [hsj] using basedGroupMap_id N (f x) p
      exact ht _
    · intro p
      rw [basedGroupMap_comp, basedGroupMap_comp]
      simp only [hgi]
    · intro p
      rw [basedGroupMap_comp, basedGroupMap_comp]
      simp only [hfr]
    · exact basedGroupMap_bijective N g (i x) (j (f x)) hig (hg.2 n (i x))

end Thomason.WeakHomotopy

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory

def topologicalWeakEquivalences : MorphismProperty TopCat.{u} :=
  fun _ _ f => WeakHomotopy.Equivalence f.hom

instance topologicalWeakEquivalences_containsIdentities :
    topologicalWeakEquivalences.{u}.ContainsIdentities where
  id_mem _ := WeakHomotopy.equivalence_id

instance topologicalWeakEquivalences_isMultiplicative :
    topologicalWeakEquivalences.{u}.IsMultiplicative where
  comp_mem _ _ hf hg := WeakHomotopy.Equivalence.comp hf hg

instance topologicalWeakEquivalences_hasTwoOutOfThreeProperty :
    topologicalWeakEquivalences.{u}.HasTwoOutOfThreeProperty where
  of_precomp _ _ hf hfg := WeakHomotopy.Equivalence.of_comp_left hfg hf
  of_postcomp _ _ hg hfg := WeakHomotopy.Equivalence.of_comp_right hfg hg

instance topologicalWeakEquivalences_isStableUnderRetracts :
    topologicalWeakEquivalences.{u}.IsStableUnderRetracts where
  of_retract h hg := by
    apply WeakHomotopy.Equivalence.of_retract _ _ h.i.left.hom h.i.right.hom
      h.r.left.hom h.r.right.hom _ _ _ _ hg
    · exact congrArg TopCat.Hom.hom h.retract_left
    · exact congrArg TopCat.Hom.hom h.retract_right
    · exact congrArg TopCat.Hom.hom h.i_w
    · exact congrArg TopCat.Hom.hom h.r_w

instance simplicialWeakEquivalences_containsIdentities :
    simplicialWeakEquivalences.{u}.ContainsIdentities :=
  inferInstanceAs (topologicalWeakEquivalences.inverseImage SSet.toTop).ContainsIdentities

instance simplicialWeakEquivalences_isMultiplicative :
    simplicialWeakEquivalences.{u}.IsMultiplicative :=
  inferInstanceAs (topologicalWeakEquivalences.inverseImage SSet.toTop).IsMultiplicative

instance simplicialWeakEquivalences_hasTwoOutOfThreeProperty :
    simplicialWeakEquivalences.{u}.HasTwoOutOfThreeProperty :=
  inferInstanceAs (topologicalWeakEquivalences.inverseImage SSet.toTop).HasTwoOutOfThreeProperty

instance simplicialWeakEquivalences_isStableUnderRetracts :
    simplicialWeakEquivalences.{u}.IsStableUnderRetracts :=
  inferInstanceAs (topologicalWeakEquivalences.inverseImage SSet.toTop).IsStableUnderRetracts

instance thomasonWeakEquivalences_hasTwoOutOfThreeProperty :
    thomasonWeakEquivalences.{u}.HasTwoOutOfThreeProperty :=
  inferInstanceAs (simplicialWeakEquivalences.inverseImage thomasonRight).HasTwoOutOfThreeProperty

instance thomasonWeakEquivalences_isStableUnderRetracts :
    thomasonWeakEquivalences.{u}.IsStableUnderRetracts :=
  inferInstanceAs (simplicialWeakEquivalences.inverseImage thomasonRight).IsStableUnderRetracts

instance thomasonWeakEquivalencesFinite_hasTwoOutOfThreeProperty (n : ℕ) :
    (thomasonWeakEquivalencesFinite.{u} n).HasTwoOutOfThreeProperty :=
  inferInstanceAs
    (simplicialWeakEquivalences.inverseImage (thomasonRightFinite n)).HasTwoOutOfThreeProperty

instance thomasonWeakEquivalencesFinite_isStableUnderRetracts (n : ℕ) :
    (thomasonWeakEquivalencesFinite.{u} n).IsStableUnderRetracts :=
  inferInstanceAs
    (simplicialWeakEquivalences.inverseImage (thomasonRightFinite n)).IsStableUnderRetracts

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.TopologicalHorn

open scoped Topology

abbrev Simplex (n : ℕ) := Convexity.StdSimplex ℝ (Fin (n + 1))

def horn {n : ℕ} (i : Fin (n + 2)) : Set (Simplex (n + 1)) :=
  {x | ∃ j, j ≠ i ∧ x.weights j = 0}

noncomputable def minimum {n : ℕ} (i : Fin (n + 2)) (x : Simplex (n + 1)) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun k : Fin (n + 1) => x.weights (i.succAbove k))

lemma minimum_nonneg {n : ℕ} (i : Fin (n + 2)) (x : Simplex (n + 1)) :
    0 ≤ minimum i x :=
  Finset.le_inf' _ _ (fun _ _ => Convexity.StdSimplex.weights_nonneg _)

lemma minimum_le {n : ℕ} (i : Fin (n + 2)) (x : Simplex (n + 1))
    (j : Fin (n + 2)) (hj : j ≠ i) : minimum i x ≤ x.weights j := by
  obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
  exact Finset.inf'_le _ (Finset.mem_univ k)

lemma minimum_attained {n : ℕ} (i : Fin (n + 2)) (x : Simplex (n + 1)) :
    ∃ j, j ≠ i ∧ minimum i x = x.weights j := by
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun k : Fin (n + 1) => x.weights (i.succAbove k))
  exact ⟨i.succAbove k, i.succAbove_ne k, hk⟩

lemma continuous_minimum {n : ℕ} (i : Fin (n + 2)) : Continuous (minimum i) := by
  exact Continuous.finset_inf'_apply Finset.univ_nonempty
    (fun k _ => Convexity.StdSimplex.continuous_weights_apply ℝ (i.succAbove k))

lemma minimum_eq_zero {n : ℕ} (i : Fin (n + 2)) (x : Simplex (n + 1))
    (hx : x ∈ horn i) : minimum i x = 0 := by
  obtain ⟨j, hj, hxj⟩ := hx
  exact le_antisymm (hxj ▸ minimum_le i x j hj) (minimum_nonneg i x)

noncomputable def retractSimplex {n : ℕ} (i : Fin (n + 2)) :
    C(Simplex (n + 1), Simplex (n + 1)) := by
  classical
  let r (x : Simplex (n + 1)) (j : Fin (n + 2)) :=
    if j = i then x.weights i + (n + 1 : ℝ) * minimum i x else x.weights j - minimum i x
  refine ⟨fun x => ⟨Finsupp.equivFunOnFinite.symm (r x), ?_, ?_⟩, ?_⟩
  · intro j
    dsimp [r]
    split_ifs
    · exact add_nonneg (Convexity.StdSimplex.weights_nonneg i)
        (mul_nonneg (by positivity) (minimum_nonneg i x))
    · exact sub_nonneg.mpr (minimum_le i x j ‹j ≠ i›)
  · rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    change ∑ j, r x j = 1
    rw [Fin.sum_univ_succAbove _ i]
    simp only [r, ite_eq_left rfl, Fin.succAbove_ne, ite_false, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hx := Convexity.StdSimplex.total_of_fintype x
    rw [Fin.sum_univ_succAbove _ i] at hx
    push_cast
    linarith
  · apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).continuous_iff.mpr
    apply continuous_pi
    intro j
    dsimp [r]
    split_ifs
    · exact (Convexity.StdSimplex.continuous_weights_apply ℝ i).add
        ((continuous_minimum i).const_mul _)
    · exact (Convexity.StdSimplex.continuous_weights_apply ℝ j).sub (continuous_minimum i)

lemma retractSimplex_zero {n : ℕ} (i : Fin (n + 2)) (x : Simplex (n + 1)) :
    retractSimplex i x ∈ horn i := by
  obtain ⟨j, hj, hx⟩ := minimum_attained i x
  refine ⟨j, hj, ?_⟩
  change (if j = i then _ else _) = _
  simp only [hj, ite_false, hx, sub_self]

noncomputable def retract {n : ℕ} (i : Fin (n + 2)) :
    C(Simplex (n + 1), horn i) :=
  ⟨fun x => ⟨retractSimplex i x, retractSimplex_zero i x⟩,
    (retractSimplex i).continuous.subtype_mk _⟩

lemma retract_fixed {n : ℕ} (i : Fin (n + 2)) (x : horn i) :
    (retract i x).val = x.val := by
  ext j
  change (if j = i then _ else _) = _
  rw [minimum_eq_zero i x x.property]
  split_ifs with h
  · simp [h]
  · simp

end Thomason.TopologicalHorn

end

noncomputable section
universe u v w z


namespace Thomason.TopologicalHorn

open CategoryTheory

lemma map_injective_apply {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Injective f) (x : Convexity.StdSimplex ℝ A) (a : A) :
    (Convexity.StdSimplex.map f x).weights (f a) = x.weights a := by
  exact Finsupp.mapDomain_apply_of_injective hf x.weights a

lemma map_not_range {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (x : Convexity.StdSimplex ℝ A) (b : B) (hb : b ∉ Set.range f) :
    (Convexity.StdSimplex.map f x).weights b = 0 := by
  exact Finsupp.mapDomain_of_notMem_range x.weights b hb

lemma map_succAbove_pivot {n : ℕ} (j : Fin (n + 2)) (x : Simplex n) :
    (Convexity.StdSimplex.map j.succAbove x).weights j = 0 :=
  map_not_range _ _ _ (by simp)

lemma map_succAbove_apply {n : ℕ} (j : Fin (n + 2)) (x : Simplex n)
    (k : Fin (n + 1)) :
    (Convexity.StdSimplex.map j.succAbove x).weights (j.succAbove k) = x.weights k :=
  map_injective_apply _ Fin.succAbove_right_injective _ _

lemma map_succAbove_injective {n : ℕ} (j : Fin (n + 2)) :
    Function.Injective (Convexity.StdSimplex.map (R := ℝ) j.succAbove) := by
  intro x y h
  ext k
  simpa only [map_succAbove_apply] using
    congrArg (fun simplex => simplex.weights (j.succAbove k)) h

noncomputable def drop {n : ℕ} (j : Fin (n + 2)) :
    C({x : Simplex (n+1) | x.weights j = 0}, Simplex n) := by
  refine ⟨fun x => ⟨Finsupp.equivFunOnFinite.symm (fun k => x.val.weights (j.succAbove k)),
    fun _ => Convexity.StdSimplex.weights_nonneg _, by
    have hx := Convexity.StdSimplex.total_of_fintype x.val
    rw [Fin.sum_univ_succAbove _ j, x.property, zero_add] at hx
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    exact hx⟩, ?_⟩
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous_iff.mpr
  apply continuous_pi
  intro k
  exact (Convexity.StdSimplex.continuous_weights_apply ℝ (j.succAbove k)).comp
    continuous_subtype_val

lemma map_drop {n : ℕ} (j : Fin (n + 2)) (x : Simplex (n+1)) (hx : x.weights j = 0) :
    Convexity.StdSimplex.map j.succAbove (drop j ⟨x,hx⟩) = x := by
  ext k
  by_cases h : k = j
  · subst k
    rw [map_succAbove_pivot, hx]
  · obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq h
    rw [map_succAbove_apply]
    rfl

lemma drop_map {n : ℕ} (j : Fin (n + 2)) (x : Simplex n) :
    drop j ⟨Convexity.StdSimplex.map j.succAbove x, map_succAbove_pivot j x⟩ = x := by
  ext k
  exact map_succAbove_apply j x k

lemma double_map {n : ℕ} (j k : Fin (n + 3)) (hjk : j < k) (x : Simplex n) :
    Convexity.StdSimplex.map j.succAbove (Convexity.StdSimplex.map
      (k.pred (Fin.ne_zero_of_lt hjk)).succAbove x) =
    Convexity.StdSimplex.map k.succAbove (Convexity.StdSimplex.map
      (j.castPred (Fin.ne_last_of_lt hjk)).succAbove x) := by
  rw [← Convexity.StdSimplex.map_comp, ← Convexity.StdSimplex.map_comp]
  congr 1
  obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hjk)
  obtain ⟨k, rfl⟩ := k.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hjk)
  simp only [Fin.pred_succ, Fin.castPred_castSucc]
  have he := SimplexCategory.δ_comp_δ (show j ≤ k by simpa using hjk)
  exact (congrArg (fun f : SimplexCategory.mk n ⟶ SimplexCategory.mk (n+2) =>
    fun a => f a) he).symm

noncomputable def closedCoverPaste {A : Type u} {B : Type v} {J : Type w}
    [TopologicalSpace A] [TopologicalSpace B] [Finite J]
    (s : J → Set A) (hs : ∀ j, IsClosed (s j)) (hv : ∀ a, ∃ j, a ∈ s j)
    (f : ∀ j, C(s j, B))
    (hf : ∀ j k a (hj : a ∈ s j) (hk : a ∈ s k), f j ⟨a,hj⟩ = f k ⟨a,hk⟩) : C(A,B) := by
  let g (a : A) := f (hv a).choose ⟨a, (hv a).choose_spec⟩
  have he (j : J) (a : A) (ha : a ∈ s j) : g a = f j ⟨a, ha⟩ :=
    hf _ _ _ _ _
  refine ⟨g, (locallyFinite_of_finite s).continuous ?_ hs ?_⟩
  · exact Set.eq_univ_of_forall (fun a => Set.mem_iUnion.mpr (hv a))
  · intro j
    rw [continuousOn_iff_continuous_domRestrict]
    exact (f j).continuous.congr (fun a => (he j a a.property).symm)

lemma closedCoverPaste_apply {A : Type u} {B : Type v} {J : Type w}
    [TopologicalSpace A] [TopologicalSpace B] [Finite J]
    (s : J → Set A) (hs : ∀ j, IsClosed (s j)) (hv : ∀ a, ∃ j, a ∈ s j)
    (f : ∀ j, C(s j, B))
    (hf : ∀ j k a (hj : a ∈ s j) (hk : a ∈ s k), f j ⟨a,hj⟩ = f k ⟨a,hk⟩)
    (j : J) (a : A) (ha : a ∈ s j) :
    closedCoverPaste s hs hv f hf a = f j ⟨a,ha⟩ :=
  hf _ _ _ _ _

end Thomason.TopologicalHorn

end

noncomputable section
universe u v w z


namespace Thomason.TopologicalHorn

open CategoryTheory Simplicial SimplicialObject

noncomputable def singularValue {X : TopCat.{u}} {n : ℕ}
    (f : (SSet.stdSimplex.obj ⦋n⦌ : SSet.{u}) ⟶ TopCat.toSSet.obj X) : C(Simplex n, X) :=
  X.toSSetObjEquiv _ (SSet.yonedaEquiv f)

lemma singularValue_delta {X : TopCat.{u}} {n : ℕ}
    (f : (SSet.stdSimplex.obj ⦋n+1⦌ : SSet.{u}) ⟶ TopCat.toSSet.obj X)
    (j : Fin (n+2)) (x : Simplex n) :
    singularValue (SSet.stdSimplex.δ j ≫ f) x =
      singularValue f (Convexity.StdSimplex.map j.succAbove x) := by
  simp only [singularValue, SSet.stdSimplex.yonedaEquiv_δ_comp,
    TopCat.toSSetObjEquiv_δ_apply]

lemma singular_faces_agree {X : TopCat.{u}} {n : ℕ} {i : Fin (n+2)}
    (f : ∀ (j : Fin (n+2)) (_ : j ≠ i), (SSet.stdSimplex.obj ⦋n⦌ : SSet.{u}) ⟶ TopCat.toSSet.obj X)
    (hf : SSet.horn.IsCompatible f) (j k : Fin (n+2)) (hj : j ≠ i) (hk : k ≠ i)
    (x : Simplex (n+1)) (hxj : x.weights j = 0) (hxk : x.weights k = 0) :
    singularValue (f j hj) (drop j ⟨x,hxj⟩) = singularValue (f k hk) (drop k ⟨x,hxk⟩) := by
  by_cases he : j = k
  · subst k
    rfl
  suffices h : ∀ (j k : Fin (n+2)) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k)
      (hxj : x.weights j = 0) (hxk : x.weights k = 0),
      singularValue (f j hj) (drop j ⟨x,hxj⟩) =
        singularValue (f k hk) (drop k ⟨x,hxk⟩) by
    rcases lt_or_gt_of_ne he with hlt | hlt
    · exact h j k hj hk hlt hxj hxk
    · exact (h k j hk hj hlt hxk hxj).symm
  clear j k hj hk hxj hxk he
  intro j k hj hk hjk hxj hxk
  cases n with
  | zero =>
    have hs := Convexity.StdSimplex.total_of_fintype x
    rw [Fin.sum_univ_two] at hs
    fin_cases j <;> fin_cases k <;> norm_num at hjk
    change x.weights 0 = 0 at hxj
    change x.weights 1 = 0 at hxk
    linarith
  | succ n =>
    let b := k.pred (Fin.ne_zero_of_lt hjk)
    let a := j.castPred (Fin.ne_last_of_lt hjk)
    let y := drop j ⟨x,hxj⟩
    have hy : y.weights b = 0 := by
      change x.weights (j.succAbove b) = 0
      simpa only [b, Fin.succAbove_pred_of_lt j k hjk] using hxk
    let z := drop b ⟨y,hy⟩
    have hyz : Convexity.StdSimplex.map b.succAbove z = y := map_drop b y hy
    have hkz : Convexity.StdSimplex.map a.succAbove z = drop k ⟨x,hxk⟩ := by
      apply map_succAbove_injective k
      rw [map_drop, ← double_map j k hjk z, hyz]
      exact map_drop j x hxj
    have heq := congrArg (fun g => singularValue g z) (hf j k hj hk hjk)
    rw [singularValue_delta, singularValue_delta] at heq
    change singularValue (f j hj) (Convexity.StdSimplex.map b.succAbove z) =
      singularValue (f k hk) (Convexity.StdSimplex.map a.succAbove z) at heq
    rwa [hyz, hkz] at heq

noncomputable def hornValue {X : TopCat.{u}} {n : ℕ} {i : Fin (n+2)}
    (f : ∀ (j : Fin (n+2)) (_ : j ≠ i), (SSet.stdSimplex.obj ⦋n⦌ : SSet.{u}) ⟶ TopCat.toSSet.obj X)
    (hf : SSet.horn.IsCompatible f) : C(horn i, X) :=
  closedCoverPaste (fun j : {j : Fin (n+2) // j ≠ i} => {x | x.val.weights j.val = 0})
    (fun j => isClosed_eq ((Convexity.StdSimplex.continuous_weights_apply ℝ j.val).comp
      continuous_subtype_val) continuous_const)
    (fun x => by obtain ⟨j,hj,hx⟩ := x.property; exact ⟨⟨j,hj⟩,hx⟩)
    (fun j => (singularValue (f j.val j.property)).comp
      ((drop j.val).comp ⟨fun x => ⟨x.val.val,x.property⟩,
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩))
    (fun j k x hj hk => singular_faces_agree f hf j.val k.val j.property k.property x.val hj hk)

lemma hornValue_face {X : TopCat.{u}} {n : ℕ} {i : Fin (n+2)}
    (f : ∀ (j : Fin (n+2)) (_ : j ≠ i), (SSet.stdSimplex.obj ⦋n⦌ : SSet.{u}) ⟶ TopCat.toSSet.obj X)
    (hf : SSet.horn.IsCompatible f) (j : Fin (n+2)) (hj : j ≠ i) (x : Simplex n) :
    hornValue f hf ⟨Convexity.StdSimplex.map j.succAbove x, j, hj, map_succAbove_pivot j x⟩ =
      singularValue (f j hj) x := by
  rw [hornValue, closedCoverPaste_apply (j := ⟨j,hj⟩) (ha := map_succAbove_pivot j x)]
  change singularValue (f j hj)
    (drop j ⟨Convexity.StdSimplex.map j.succAbove x, map_succAbove_pivot j x⟩) = _
  rw [drop_map]

theorem singular_kan (X : TopCat.{u}) : SSet.KanComplex (TopCat.toSSet.obj X) := by
  rw [SSet.KanComplex.iff]
  intro n i f hf
  let h : C(Simplex (n+1), X) := (hornValue f hf).comp (retract i)
  let φ := SSet.yonedaEquiv.symm ((X.toSSetObjEquiv _).symm h)
  have hφ : singularValue φ = h := by
    simp only [singularValue, φ, Equiv.apply_symm_apply]
  refine ⟨φ, ?_⟩
  intro j hj
  apply SSet.yonedaEquiv.injective
  apply (X.toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro x
  change singularValue (SSet.stdSimplex.δ j ≫ φ) x = singularValue (f j hj) x
  rw [singularValue_delta, hφ]
  change hornValue f hf (retract i (Convexity.StdSimplex.map j.succAbove x)) = _
  have hx : Convexity.StdSimplex.map j.succAbove x ∈ horn i := ⟨j,hj,map_succAbove_pivot j x⟩
  have he : retract i (Convexity.StdSimplex.map j.succAbove x) = ⟨_,hx⟩ :=
    Subtype.ext (retract_fixed i ⟨_,hx⟩)
  rw [he]
  exact hornValue_face f hf j hj x

end Thomason.TopologicalHorn

end

noncomputable section
universe u v w z


namespace Thomason.TopologicalHorn

open CategoryTheory Simplicial
open scoped unitInterval Topology

variable {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]

noncomputable def simplexHomotopy {n : ℕ} (f g : C(A, Simplex n)) : f.Homotopy g where
  toFun q := ⟨Finsupp.equivFunOnFinite.symm
    (fun k => (1 - (q.1 : ℝ)) * (f q.2).weights k + (q.1 : ℝ) * (g q.2).weights k),
    fun k => add_nonneg (mul_nonneg (sub_nonneg.mpr q.1.property.2)
      (Convexity.StdSimplex.weights_nonneg k))
      (mul_nonneg q.1.property.1 (Convexity.StdSimplex.weights_nonneg k)), by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      simp only [Finsupp.coe_equivFunOnFinite_symm,
        Finset.sum_add_distrib, ← Finset.mul_sum, Convexity.StdSimplex.total_of_fintype, mul_one]
      ring⟩
  continuous_toFun := by
    apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous_iff.mpr
    apply continuous_pi
    intro k
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((Convexity.StdSimplex.continuous_weights_apply ℝ k).comp
        (f.continuous.comp continuous_snd)) |>.add
      ((continuous_subtype_val.comp continuous_fst).mul
        ((Convexity.StdSimplex.continuous_weights_apply ℝ k).comp
          (g.continuous.comp continuous_snd)))
  map_zero_left a := by
    ext k
    change (1 - (0 : ℝ)) * (f a).weights k + (0 : ℝ) * (g a).weights k = (f a).weights k
    ring
  map_one_left a := by
    ext k
    change (1 - (1 : ℝ)) * (f a).weights k + (1 : ℝ) * (g a).weights k = (g a).weights k
    ring

lemma simplexHomotopy_fixed {n : ℕ} (f g : C(A, Simplex n)) (a : A) (ha : f a = g a) (t : I) :
    simplexHomotopy f g (t,a) = f a := by
  ext k
  change (1 - (t : ℝ)) * (f a).weights k + (t : ℝ) * (g a).weights k = (f a).weights k
  rw [← ha]
  ring

noncomputable def simplexHomeoHomotopy {n : ℕ} (e : B ≃ₜ Simplex n) (f g : C(A,B)) :
    f.Homotopy g where
  toFun q := e.symm (simplexHomotopy ((⟨e,e.continuous⟩ : C(B, Simplex n)).comp f) ((⟨e,e.continuous⟩ : C(B, Simplex n)).comp g) q)
  continuous_toFun := e.symm.continuous.comp (simplexHomotopy _ _).continuous
  map_zero_left a := by rw [ContinuousMap.Homotopy.apply_zero]; exact e.symm_apply_apply _
  map_one_left a := by rw [ContinuousMap.Homotopy.apply_one]; exact e.symm_apply_apply _

lemma simplexHomeoHomotopy_fixed {n : ℕ} (e : B ≃ₜ Simplex n) (f g : C(A,B))
    (a : A) (ha : f a = g a) (t : I) : simplexHomeoHomotopy e f g (t,a) = f a := by
  change e.symm (simplexHomotopy ((⟨e,e.continuous⟩ : C(B, Simplex n)).comp f) ((⟨e,e.continuous⟩ : C(B, Simplex n)).comp g) (t,a)) = _
  rw [simplexHomotopy_fixed _ _ a (congrArg e ha)]
  exact e.symm_apply_apply _

lemma equivalence_of_simplex_retract {n : ℕ} (e : B ≃ₜ Simplex n)
    (j : C(A,B)) (p : C(B,A)) (hp : p.comp j = .id A) : WeakHomotopy.Equivalence j := by
  apply WeakHomotopy.equivalence_of_strong_retract j p hp
  refine ⟨{ toHomotopy := simplexHomeoHomotopy e (j.comp p) (.id B)
            prop' := ?_ }⟩
  rintro t b ⟨a,rfl⟩
  exact simplexHomeoHomotopy_fixed e (j.comp p) (.id B) (j a)
    (congrArg j (ContinuousMap.congr_fun hp a)) t

noncomputable def realizationHornRetraction {n : ℕ} (i : Fin (n+2)) :
    SSet.toTop.obj (SSet.stdSimplex.obj ⦋n+1⦌ : SSet.{u}) ⟶
      SSet.toTop.obj (SSet.horn (n+1) i : SSet.{u}) := by
  let : ((SSet.toTop ⋙ TopCat.toSSet).obj (SSet.horn (n+1) i : SSet.{u})).KanComplex :=
    singular_kan (SSet.toTop.obj (SSet.horn (n+1) i : SSet.{u}))
  let filler :=  (SSet.KanComplex.hornFilling
    (sSetTopAdj.unit.app (SSet.horn (n+1) i : SSet.{u}))).choose
  exact (sSetTopAdj.homEquiv _ _).symm filler

lemma realizationHornRetraction_comp {n : ℕ} (i : Fin (n+2)) :
    SSet.toTop.map (SSet.horn.{u} (n+1) i).ι ≫ realizationHornRetraction i = 𝟙 _ := by
  let : ((SSet.toTop ⋙ TopCat.toSSet).obj (SSet.horn (n+1) i : SSet.{u})).KanComplex :=
    singular_kan (SSet.toTop.obj (SSet.horn (n+1) i : SSet.{u}))
  have h := (SSet.KanComplex.hornFilling
    (sSetTopAdj.unit.app (SSet.horn (n+1) i : SSet.{u}))).choose_spec
  apply (sSetTopAdj.homEquiv _ _).injective
  rw [sSetTopAdj.homEquiv_naturality_left, sSetTopAdj.homEquiv_id]
  change _ ≫ (sSetTopAdj.homEquiv _ _) ((sSetTopAdj.homEquiv _ _).symm _) = _
  rw [Equiv.apply_symm_apply]
  exact h.symm

theorem horn_weak_equivalence {n : ℕ} (i : Fin (n+2)) :
    simplicialWeakEquivalences.{u} (SSet.horn (n+1) i).ι := by
  apply equivalence_of_simplex_retract (SimplexCategory.toTopHomeo ⦋n+1⦌)
    _ (realizationHornRetraction i).hom
  exact congrArg TopCat.Hom.hom (realizationHornRetraction_comp i)

end Thomason.TopologicalHorn

end

end OAI
