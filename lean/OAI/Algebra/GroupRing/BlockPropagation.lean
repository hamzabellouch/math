import Mathlib

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.BlockPropagation

open scoped BigOperators

structure Skeleton (I : Type*) where
  root : I
  parent : I → I
  rank : I → ℕ
  decreasing : ∀ i, i ≠ root → rank (parent i) < rank i

/-- A connected comparison graph supplies a decreasing parent system, with
any chosen block as root (in particular the minimizer of its weight bin). -/
theorem exists_skeleton {I : Type*} (G : SimpleGraph I) (hc : G.Connected) (r : I) :
    ∃ S : Skeleton I, S.root = r ∧ ∀ i, i ≠ r → G.Adj i (S.parent i) := by
  classical
  have hn (i : I) (hi : i ≠ r) :
      ∃ j, G.Adj i j ∧ G.dist j r < G.dist i r := by
    obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist i r
    cases p with
    | nil => exact False.elim (hi rfl)
    | @cons a b c hab p =>
      refine ⟨b, hab, ?_⟩
      have hle := G.dist_le p
      simp only [SimpleGraph.Walk.length_cons] at hp
      omega
  let parent := fun i => if hi : i = r then r else (hn i hi).choose
  refine ⟨⟨r, parent, fun i => G.dist i r, ?_⟩, rfl, ?_⟩
  · intro i hi
    dsimp [parent]
    rw [dite_eq_right hi]
    exact (hn i hi).choose_spec.2
  · intro i hi
    dsimp [parent]
    rw [dite_eq_right hi]
    exact (hn i hi).choose_spec.1

namespace Skeleton

variable {I T : Type*} (S : Skeleton I) (h : I → ℕ)
    (known : (i : I) → Finset (Fin (h i)))
    (determine : (i : I) → Fin (h i) → (Fin (h (S.parent i)) → T) → T)

abbrev Assignment := (i : I) → Fin (h i) → T

def Consistent (w : Assignment h (T := T)) : Prop :=
  ∀ i, i ≠ S.root → ∀ k ∈ known i, w i k = determine i k (w (S.parent i))

abbrev FreePosition := {p : (i : I) × Fin (h i) // p.1 ≠ S.root ∧ p.2 ∉ known p.1}

/-- The omitted coordinates plus the root word determine every full word. -/
theorem assignment_ext {w v : Assignment h (T := T)}
    (hw : S.Consistent h known determine w) (hv : S.Consistent h known determine v)
    (hroot : w S.root = v S.root)
    (hfree : ∀ p : S.FreePosition h known, w p.val.1 p.val.2 = v p.val.1 p.val.2) : w = v := by
  have hall (n : ℕ) : ∀ i, S.rank i = n → w i = v i := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hi
      by_cases hir : i = S.root
      · subst i
        exact hroot
      · funext k
        by_cases hk : k ∈ known i
        · rw [hw i hir k hk, hv i hir k hk]
          have hp : S.rank (S.parent i) < n := hi ▸ S.decreasing i hir
          rw [ih _ hp (S.parent i) rfl]
        · exact hfree ⟨⟨i,k⟩,hir,hk⟩
  funext i
  exact hall (S.rank i) i rfl

variable [Fintype I] [Fintype T] [DecidableEq I]

/-- Exact number of unrecorded letters after the tree comparisons. -/
theorem card_freePositions :
    Nat.card (S.FreePosition h known) =
      ∑ i : {i : I // i ≠ S.root}, (h i.val - (known i.val).card) := by
  classical
  let e : S.FreePosition h known ≃
      (i : {i : I // i ≠ S.root}) × {k : Fin (h i.val) // k ∉ known i.val} :=
    { toFun := fun p => ⟨⟨p.val.1,p.property.1⟩,⟨p.val.2,p.property.2⟩⟩
      invFun := fun p => ⟨⟨p.1.val,p.2.val⟩,p.1.property,p.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]

/-- Choose actual root words from R, then at most |T| choices per omitted
coordinate. The remaining coordinates are forced by the comparisons. -/
theorem card_assignments (R : Finset (Fin (h S.root) → T)) :
    Nat.card {w : Assignment h (T := T) //
      S.Consistent h known determine w ∧ w S.root ∈ R} ≤
      R.card * (Fintype.card T) ^
        (∑ i : {i : I // i ≠ S.root}, (h i.val - (known i.val).card)) := by
  classical
  let encode : {w : Assignment h (T := T) //
        S.Consistent h known determine w ∧ w S.root ∈ R} →
      R × (S.FreePosition h known → T) := fun w =>
    (⟨w.val S.root,w.property.2⟩,fun p => w.val p.val.1 p.val.2)
  have henc : Function.Injective encode := by
    intro w v he
    apply Subtype.ext
    apply S.assignment_ext h known determine w.property.1 v.property.1
    · exact congrArg (fun p => p.1.val) he
    · intro p
      exact congrFun (congrArg Prod.snd he) p
  have hc := Fintype.card_le_of_injective encode henc
  rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_fun] at hc
  have he : Fintype.card (S.FreePosition h known) =
      ∑ i : {i : I // i ≠ S.root}, (h i.val - (known i.val).card) := by
    simpa only [Nat.card_eq_fintype_card] using S.card_freePositions h known
  simpa only [Nat.card_eq_fintype_card, he] using hc

end Skeleton
end TorsionFreeZeroDivisors.BlockPropagation

/-! Label projection along connected substring links.
A link determines a specified subset of one block from positions in its
partner word, via a letter equivalence such as identity or inversion.
No embedding of inactive graph vertices is requested or assumed. -/
namespace TorsionFreeZeroDivisors.StageLabels

section
open scoped Classical BigOperators
open BlockPropagation

variable {I T : Type*} [Fintype I] [Fintype T] [Nonempty T]

/-- A finite directed presentation of substring links. Both directions of
an actual interval-isometry link may be included; extra constraints only
reduce the set of feasible strings. -/
structure Links (h : I → ℕ) where
  graph : SimpleGraph I
  known : (i j : I) → Finset (Fin (h i))
  source : (i j : I) → known i j → Fin (h j)
  symbol : I → I → (T ≃ T)

namespace Links
variable {h : I → ℕ} (L : Links (T := T) h)

abbrev Word := (i : I) → Fin (h i) → T

def Consistent (w : Word (T := T) (h := h)) : Prop :=
  ∀ i j, L.graph.Adj i j → ∀ k : L.known i j,
    w i k.val = L.symbol i j (w j (L.source i j k))

abbrev RootedWords (r : I) (R : Finset (Fin (h r) → T)) :=
  {w : Word (T := T) (h := h) // L.Consistent w ∧ w r ∈ R}

/-- Full strings on a connected link component, with a chosen root, are
bounded by the root choices times one alphabet choice per missing position. -/
theorem connected_count (hc : L.graph.Connected) (r : I)
    (R : Finset (Fin (h r) → T)) (e : ℕ)
    (he : ∀ i j, L.graph.Adj i j → h i - (L.known i j).card ≤ e) :
    Fintype.card (L.RootedWords r R) ≤
      R.card * (Fintype.card T)^(e*(Fintype.card I-1)) := by
  obtain ⟨S,hr,hparent⟩ := exists_skeleton L.graph hc r
  subst r
  let known := fun i => L.known i (S.parent i)
  let determine := fun i (k : Fin (h i)) (w : Fin (h (S.parent i)) → T) =>
    if hk : k ∈ known i then L.symbol i (S.parent i) (w (L.source i (S.parent i) ⟨k,hk⟩))
    else Classical.choice (inferInstance : Nonempty T)
  let forget : L.RootedWords S.root R →
      {w : Skeleton.Assignment h (T := T) // S.Consistent h known determine w ∧ w S.root ∈ R} :=
    fun w => ⟨w.val,by
      constructor
      · intro i hi k hk
        dsimp [determine]
        rw [dite_eq_left hk]
        exact w.property.1 i (S.parent i) (hparent i hi) ⟨k,hk⟩
      · exact w.property.2⟩
  have hf : Function.Injective forget := by
    intro a b heq
    apply Subtype.ext
    exact congrArg (fun q : {w : Skeleton.Assignment h (T := T) //
      S.Consistent h known determine w ∧ w S.root ∈ R} => q.val) heq
  have hk : (∑ i : {i : I // i ≠ S.root}, (h i.val - (known i.val).card)) ≤
      e*(Fintype.card I-1) := by
    calc
      _ ≤ ∑ _i : {i : I // i ≠ S.root}, e := Finset.sum_le_sum (fun i _ =>
        he i.val (S.parent i.val) (hparent i.val i.property))
      _ = e*(Fintype.card I-1) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_subtype_compl]
        have hr : Fintype.card {i : I // i = S.root} = 1 := by simp
        rw [hr,mul_comm]
        rfl
  calc
    _ ≤ Fintype.card {w : Skeleton.Assignment h (T := T) //
        S.Consistent h known determine w ∧ w S.root ∈ R} :=
      Fintype.card_le_of_injective forget hf
    _ ≤ R.card * (Fintype.card T)^
        (∑ i : {i : I // i ≠ S.root}, (h i.val - (known i.val).card)) := by
      simpa only [Nat.card_eq_fintype_card] using S.card_assignments h known determine R
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right Fintype.card_pos hk)

end Links

variable {C : Type*} [Fintype C] (color : I → C) (h : I → ℕ)

abbrev Fiber (c : C) := {i : I // color i = c}
abbrev PieceWord (c : C) := (i : Fiber color c) → Fin (h i.val) → T

def restrictWord (w : (i : I) → Fin (h i) → T) (c : C) : PieceWord (T := T) color h c :=
  fun i => w i.val

def activeComponents (A : Finset I) : Finset C :=
  A.image color

def stageWords (A : Finset I) (P : ((i : I) → Fin (h i) → T) → Prop) :
    Finset ((i : A) → Fin (h i.val) → T) :=
  (Finset.univ.filter P).image (fun w i => w i.val)

omit [Nonempty T] [Fintype C] in
/-- Restriction to active blocks is bounded by complete strings only on the
components they meet. The representative root of a component need not be
active: the witness is a *string*, not an embedding in a sampled graph. -/
theorem projection_count (A : Finset I) (P : ((i : I) → Fin (h i) → T) → Prop)
    (Q : (c : C) → PieceWord (T := T) color h c → Prop)
    (hQ : ∀ w, P w → ∀ c ∈ activeComponents color A, Q c (restrictWord color h w c)) :
    (stageWords h A P).card ≤
      ∏ c : activeComponents color A, Fintype.card {w : PieceWord (T := T) color h c.val // Q c.val w} := by
  have hs (w : stageWords h A P) :
      ∃ W : (i : I) → Fin (h i) → T, P W ∧ (fun i : A => W i.val) = w.val := by
    obtain ⟨W,hW,hw⟩ := Finset.mem_image.mp w.property
    exact ⟨W,(Finset.mem_filter.mp hW).2,hw⟩
  let full (w : stageWords h A P) := (hs w).choose
  have full_spec (w : stageWords h A P) :
      P (full w) ∧ (fun i : A => full w i.val) = w.val := (hs w).choose_spec
  let encode (w : stageWords h A P) : (c : activeComponents color A) →
      {W : PieceWord (T := T) color h c.val // Q c.val W} :=
    fun c => ⟨restrictWord color h (full w) c.val,hQ _ (full_spec w).1 c.val c.property⟩
  have he : Function.Injective encode := by
    intro w v heq
    apply Subtype.ext
    funext i
    let c : activeComponents color A := ⟨color i.val,Finset.mem_image.mpr ⟨i.val,i.property,rfl⟩⟩
    have h1 := congrFun (congrArg (fun f => (f c).val) heq) (⟨i.val,rfl⟩ : Fiber color c.val)
    change full w i.val = full v i.val at h1
    rw [← (congrFun (full_spec w).2 i),← (congrFun (full_spec v).2 i)]
    exact h1
  have hc := Fintype.card_le_of_injective encode he
  simpa only [Fintype.card_coe,Fintype.card_pi] using hc

end

open scoped Classical BigOperators
variable {I T : Type*} [Fintype I] [Fintype T] [Nonempty T]
variable {h : I → ℕ} (L : Links (T := T) h)

namespace Links

def component (c : L.graph.ConnectedComponent) : Links (T := T) (fun i : c => h i.val) where
  graph := c.toSimpleGraph
  known i j := L.known i.val j.val
  source i j := L.source i.val j.val
  symbol i j := L.symbol i.val j.val

omit [Fintype I] [Fintype T] [Nonempty T] in
theorem restrict_consistent {w : (i : I) → Fin (h i) → T} (hw : L.Consistent w)
    (c : L.graph.ConnectedComponent) :
    (L.component c).Consistent (fun i => w i.val) := by
  intro i j hij k
  exact hw i.val j.val hij k

/-- Exact local bound on one actual connected component; its root is arbitrary. -/
theorem component_count (c : L.graph.ConnectedComponent) (r : c)
    (R : Finset (Fin (h r.val) → T)) (e : ℕ)
    (he : ∀ i j, L.graph.Adj i j → h i - (L.known i j).card ≤ e) :
    Fintype.card ((L.component c).RootedWords r R) ≤
      R.card * (Fintype.card T)^(e*(Fintype.card c-1)) := by
  have hc : (L.component c).graph.Connected := c.connected_toSimpleGraph
  have hh := (L.component c).connected_count hc r R e
    (fun i j hij => he i.val j.val hij)
  simpa only [← Nat.card_eq_fintype_card] using hh

omit [Fintype T] [Nonempty T] in
/-- Sum of sizes only over components met by the stage. -/
theorem active_component_size (A : Finset I) :
    (∑ c : activeComponents L.graph.connectedComponentMk A, Fintype.card c.val) ≤
      Fintype.card I := by
  let f : (c : activeComponents L.graph.connectedComponentMk A) × c.val → I :=
    fun x => x.2.val
  have hf : Function.Injective f := by
    rintro ⟨c,i⟩ ⟨d,j⟩ hij
    change i.val = j.val at hij
    have hcd : c = d := Subtype.ext (i.property.symm.trans (hij ▸ j.property))
    subst d
    have hi : i = j := Subtype.ext hij
    subst j
    rfl
  simpa only [Fintype.card_sigma] using Fintype.card_le_of_injective f hf

/-- Completing strings on each active link component before projection gives
an exponential stage bound. No vertices of an inactive chain are embedded. -/
theorem stage_exp (A : Finset I)
    (r : (c : L.graph.ConnectedComponent) → c)
    (R : (c : L.graph.ConnectedComponent) → Finset (Fin (h (r c).val) → T))
    (P : ((i : I) → Fin (h i) → T) → Prop)
    (hP : ∀ w, P w → L.Consistent w)
    (hroot : ∀ w, P w → ∀ c, w (r c).val ∈ R c)
    (e : ℕ) (he : ∀ i j, L.graph.Adj i j → h i - (L.known i j).card ≤ e)
    (cost : L.graph.ConnectedComponent → ℝ)
    (hcost : ∀ c, ((R c).card : ℝ) ≤ Real.exp (cost c)) :
    ((stageWords h A P).card : ℝ) ≤
      Real.exp ((∑ c : activeComponents L.graph.connectedComponentMk A, cost c.val) +
        (e : ℝ) * Fintype.card I * Real.log (Fintype.card T)) := by
  let C := activeComponents L.graph.connectedComponentMk A
  have hp : (stageWords h A P).card ≤
      ∏ c : C, Fintype.card ((L.component c.val).RootedWords (r c.val) (R c.val)) := by
    have hh := projection_count L.graph.connectedComponentMk h A P
      (fun c w => (L.component c).Consistent w ∧ w (r c) ∈ R c)
      (fun w hw c _ => ⟨L.restrict_consistent (hP w hw) c, hroot w hw c⟩)
    convert hh using 1
    apply congrArg
    funext c
    simp only [← Nat.card_eq_fintype_card]
    rfl
  have ha : 0 < (Fintype.card T : ℝ) := by exact_mod_cast Fintype.card_pos
  have halog : 0 ≤ Real.log (Fintype.card T) := Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α := T))
  have hcard (c : C) :
      (Fintype.card ((L.component c.val).RootedWords (r c.val) (R c.val)) : ℝ) ≤
        Real.exp (cost c.val + (e : ℝ) * Fintype.card c.val * Real.log (Fintype.card T)) := by
    have hn := L.component_count c.val (r c.val) (R c.val) e he
    have hn' : (Fintype.card ((L.component c.val).RootedWords (r c.val) (R c.val)) : ℝ) ≤
        ((R c.val).card : ℝ) * (Fintype.card T : ℝ)^(e*(Fintype.card c.val-1)) := by exact_mod_cast hn
    calc
      _ ≤ ((R c.val).card : ℝ) * (Fintype.card T : ℝ)^(e*(Fintype.card c.val-1)) := hn'
      _ ≤ Real.exp (cost c.val) * (Fintype.card T : ℝ)^(e*(Fintype.card c.val-1)) :=
        mul_le_mul_of_nonneg_right (hcost _) (pow_nonneg ha.le _)
      _ = Real.exp (cost c.val + (e*(Fintype.card c.val-1) : ℕ) * Real.log (Fintype.card T)) := by
        rw [Real.exp_add,Real.exp_nat_mul,Real.exp_log ha]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        apply add_le_add_right
        apply mul_le_mul_of_nonneg_right _ halog
        rw [Nat.cast_mul]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg e)
        exact_mod_cast Nat.sub_le (Fintype.card c.val) 1
  calc
    _ ≤ (∏ c : C, (Fintype.card ((L.component c.val).RootedWords (r c.val) (R c.val)) : ℝ)) := by
      exact_mod_cast hp
    _ ≤ ∏ c : C, Real.exp (cost c.val + (e : ℝ)*Fintype.card c.val*Real.log (Fintype.card T)) :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun component _ => hcard component)
    _ = Real.exp ((∑ c : C, cost c.val) +
        (e : ℝ)*(∑ c : C, (Fintype.card c.val : ℝ))*Real.log (Fintype.card T)) := by
      rw [← Real.exp_sum,Finset.sum_add_distrib]
      congr 1
      simp only [Finset.mul_sum,Finset.sum_mul]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_right _ halog
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg e)
      exact_mod_cast L.active_component_size A

end Links
end TorsionFreeZeroDivisors.StageLabels

/-! The link constraints are now extracted from the actual occurrence
matching, rather than supplied as an unexplained propagation hypothesis. -/

end

end OAI
