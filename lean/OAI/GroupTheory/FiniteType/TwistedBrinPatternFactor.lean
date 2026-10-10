import Mathlib
import OAI.GroupTheory.FiniteType.TwistedBrinGermBrick

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin.Pattern
section
variable {S : Type u}

structure Factor (P Q : Pattern S) where
  remainder : Leaves P → Pattern S
  leaves : (Σ i : Leaves P, Leaves (remainder i)) ≃ Leaves Q
  prefix_eq : ∀ i, leafPrefix Q (leaves i) =
    (leafPrefix P i.1).append (leafPrefix (remainder i.1) i.2)

noncomputable def Factor.fromLeaf (P : Pattern S) : Factor .leaf P where
  remainder := fun _ => P
  leaves := {
    toFun := Sigma.snd
    invFun := fun i => ⟨(),i⟩
    left_inv := by rintro ⟨⟨⟩,i⟩; rfl
    right_inv := fun _ => rfl }
  prefix_eq := by rintro ⟨i,j⟩; exact (Prefix.empty_append _).symm

noncomputable def SplitView.uniformCons {P : Pattern S} {s : S} (p : SplitView P s)
    (L : List S) (f : Factor (uniform L) p.left) (g : Factor (uniform L) p.right) :
    Factor (uniform (s :: L)) P where
  remainder := Sum.elim f.remainder g.remainder
  leaves := (Equiv.sumSigmaDistrib (fun i => Leaves (Sum.elim f.remainder g.remainder i))).trans
    ((Equiv.sumCongr f.leaves g.leaves).trans p.leaves)
  prefix_eq := by
    rintro ⟨i,j⟩
    cases i with
    | inl i =>
      change leafPrefix P (p.leaves (.inl (f.leaves ⟨i,j⟩))) = _
      rw [p.prefix_eq (.inl (f.leaves ⟨i,j⟩))]
      change (Prefix.cut s false).append (leafPrefix p.left (f.leaves ⟨i,j⟩)) =
        ((Prefix.cut s false).append (leafPrefix (uniform L) i)).append _
      rw [f.prefix_eq ⟨i,j⟩,Prefix.append_assoc]
      rfl
    | inr i =>
      change leafPrefix P (p.leaves (.inr (g.leaves ⟨i,j⟩))) = _
      rw [p.prefix_eq (.inr (g.leaves ⟨i,j⟩))]
      change (Prefix.cut s true).append (leafPrefix p.right (g.leaves ⟨i,j⟩)) =
        ((Prefix.cut s true).append (leafPrefix (uniform L) i)).append _
      rw [g.prefix_eq ⟨i,j⟩,Prefix.append_assoc]
      rfl

theorem uniform_factor_exists (L : List S) (hn : L.Nodup) (P : Pattern S)
    (h : ∀ s ∈ L, ∀ i : Leaves P, leafPrefix P i s ≠ []) :
    Nonempty (Factor (uniform L) P) := by
  induction L generalizing P with
  | nil => exact ⟨Factor.fromLeaf P⟩
  | cons s L ih =>
    obtain ⟨hs,hL⟩ := List.nodup_cons.mp hn
    obtain ⟨p⟩ := splitView_exists P s (h s (by simp))
    have hl : ∀ t ∈ L, ∀ i : Leaves p.left, leafPrefix p.left i t ≠ [] := by
      intro t ht i
      have hts : t ≠ s := by rintro rfl; exact hs ht
      have hh := h t (List.mem_cons_of_mem s ht) (p.leaves (.inl i))
      rw [p.prefix_eq (.inl i)] at hh
      simpa [leafPrefix,hts] using hh
    have hr : ∀ t ∈ L, ∀ i : Leaves p.right, leafPrefix p.right i t ≠ [] := by
      intro t ht i
      have hts : t ≠ s := by rintro rfl; exact hs ht
      have hh := h t (List.mem_cons_of_mem s ht) (p.leaves (.inr i))
      rw [p.prefix_eq (.inr i)] at hh
      simpa [leafPrefix,hts] using hh
    obtain ⟨f⟩ := ih hL p.left hl
    obtain ⟨g⟩ := ih hL p.right hr
    exact ⟨p.uniformCons L f g⟩

noncomputable instance leavesNonempty (P : Pattern S) : Nonempty (Leaves P) := by
  obtain ⟨i,_,_⟩ := partition P (fun _ _ => false)
  exact ⟨i⟩

lemma Factor.card_le {P Q : Pattern S} (f : Factor P Q) :
    Fintype.card (Leaves P) ≤ Fintype.card (Leaves Q) := by
  classical
  let h : Leaves P → Leaves Q := fun i => f.leaves ⟨i,Classical.arbitrary (Leaves (f.remainder i))⟩
  apply Fintype.card_le_of_injective h
  intro i j he
  exact congrArg Sigma.fst (f.leaves.injective he)

lemma uniform_card (L : List S) : Fintype.card (Leaves (uniform L)) = 2 ^ L.length := by
  induction L with
  | nil => change Fintype.card Unit = 1; exact Fintype.card_unique
  | cons s L ih =>
    change Fintype.card (Leaves (uniform L) ⊕ Leaves (uniform L)) = _
    rw [Fintype.card_sum,ih]
    simp [List.length_cons,pow_succ,Nat.mul_two]

lemma mem_coordinates_of_prefix_nonempty (P : Pattern S) (i : Leaves P) (s : S)
    (h : leafPrefix P i s ≠ []) : s ∈ coordinates P := by
  classical
  induction P with
  | leaf => exact (h rfl).elim
  | split t P Q ihP ihQ =>
    by_cases hst : s = t
    · subst s; simp [coordinates]
    · cases i with
      | inl i =>
        have hh : leafPrefix P i s ≠ [] := by simpa [leafPrefix,hst] using h
        simp only [coordinates,Finset.mem_insert,Finset.mem_union]
        exact Or.inr (Or.inl (ihP i hh))
      | inr i =>
        have hh : leafPrefix Q i s ≠ [] := by simpa [leafPrefix,hst] using h
        simp only [coordinates,Finset.mem_insert,Finset.mem_union]
        exact Or.inr (Or.inr (ihQ i hh))

noncomputable def firstCoordinates (P : Pattern S) : Finset S := by
  classical
  exact (coordinates P).filter (fun s => ∀ i : Leaves P, leafPrefix P i s ≠ [])

lemma mem_firstCoordinates (P : Pattern S) (s : S) :
    s ∈ firstCoordinates P ↔ ∀ i : Leaves P, leafPrefix P i s ≠ [] := by
  classical
  rw [firstCoordinates,Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    exact ⟨mem_coordinates_of_prefix_nonempty P (Classical.arbitrary _) s (h _),h⟩

lemma firstCoordinates_nonempty {P : Pattern S} (h : P ≠ .leaf) :
    (firstCoordinates P).Nonempty := by
  cases P with
  | leaf => exact (h rfl).elim
  | split s P Q => exact ⟨s,(mem_firstCoordinates _ _).mpr (split_prefix_nonempty s P Q)⟩

lemma firstCoordinates_factor (P : Pattern S) (F : Finset S) (hF : F ⊆ firstCoordinates P) :
    Nonempty (Factor (uniform F.toList) P) := by
  classical
  apply uniform_factor_exists F.toList F.nodup_toList P
  intro s hs i
  exact (mem_firstCoordinates P s).mp (hF (Finset.mem_toList.mp hs)) i

lemma firstCoordinates_card_bound (P : Pattern S) :
    2 ^ (firstCoordinates P).card ≤ Fintype.card (Leaves P) := by
  classical
  obtain ⟨f⟩ := firstCoordinates_factor P (firstCoordinates P) (fun _ h => h)
  simpa only [uniform_card,Finset.length_toList] using f.card_le

end

variable {S : Type u}

lemma firstCoordinates_uniform [DecidableEq S] (L : List S) : firstCoordinates (uniform L) = L.toFinset := by
  classical
  ext s
  rw [mem_firstCoordinates,List.mem_toFinset]
  simp_rw [← List.length_pos_iff,uniform_length]
  simp only [List.count_pos_iff,forall_const]

end TwistedBrin.Pattern

namespace TwistedBrin.Basis
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma Forest.cutRefines_factor {B C : Basis ρ} (F : Forest ρ B C)
    (P : B → Pattern S) (f : ∀ b, Pattern.Factor (P b) (F.pattern b)) :
    CutRefines ρ (expand ρ B P) C := by
  apply cutRefines_ofChartPartition ρ (expandedChart ρ B P) (expanded_partition ρ B P)
    C (fun i => (f i.1).remainder i.2)
  rintro ⟨b,i⟩ j
  change GermBrick.mk ρ (LocalEmbedding.comp ρ
    (LocalEmbedding.comp ρ (chart ρ B b) (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix (P b) i)))
    (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix ((f b).remainder i) j))) ∈ C.pieces
  rw [LocalEmbedding.comp_assoc,← LocalEmbedding.ofPrefix_append,← (f b).prefix_eq ⟨i,j⟩]
  exact (F.chart_eq ⟨b,(f b).leaves ⟨i,j⟩⟩) ▸ (F.leaves ⟨b,(f b).leaves ⟨i,j⟩⟩).property

noncomputable def gridExpansion (B : Basis ρ) (K : B → Finset S) : Basis ρ :=
  expand ρ B (fun b => Pattern.uniform (K b).toList)

lemma cutRefines_gridExpansion (B : Basis ρ) (K : B → Finset S) :
    CutRefines ρ B (gridExpansion ρ B K) := ⟨Forest.expansion B _⟩

lemma rank_gridExpansion (B : Basis ρ) (K : B → Finset S) :
    rank ρ (gridExpansion ρ B K) = ∑ b : B, 2 ^ (K b).card := by
  rw [gridExpansion,rank_expand]
  simp_rw [Pattern.uniform_card,Finset.length_toList]

lemma Forest.gridExpansion_refines {B C : Basis ρ} (F : Forest ρ B C)
    (K : B → Finset S) (hK : ∀ b, K b ⊆ Pattern.firstCoordinates (F.pattern b)) :
    CutRefines ρ (gridExpansion ρ B K) C := by
  classical
  let f := fun b => Classical.choice (Pattern.firstCoordinates_factor (F.pattern b) (K b) (hK b))
  exact F.cutRefines_factor ρ (fun b => Pattern.uniform (K b).toList) f

noncomputable def Forest.firstGrid {B C : Basis ρ} (F : Forest ρ B C) : Basis ρ :=
  gridExpansion ρ B (fun b => Pattern.firstCoordinates (F.pattern b))

lemma Forest.firstGrid_lower {B C : Basis ρ} (F : Forest ρ B C) :
    CutRefines ρ B (F.firstGrid ρ) := cutRefines_gridExpansion ρ B _

lemma Forest.firstGrid_upper {B C : Basis ρ} (F : Forest ρ B C) :
    CutRefines ρ (F.firstGrid ρ) C := F.gridExpansion_refines ρ _ (fun _ _ h => h)

end TwistedBrin.Basis

namespace TwistedBrin.Pattern
variable {S : Type u}

lemma firstCoordinates_eq_of_pieces_eq {P Q : Pattern S} (h : pieces P = pieces Q) :
    firstCoordinates P = firstCoordinates Q := by
  classical
  apply Finset.Subset.antisymm
  · intro s hs
    apply (mem_firstCoordinates Q s).mpr
    intro j
    have hj : leafPrefix Q j ∈ pieces P := by rw [h]; exact (mem_pieces Q _).mpr ⟨j,rfl⟩
    obtain ⟨i,hi⟩ := (mem_pieces P _).mp hj
    rw [← hi]
    exact (mem_firstCoordinates P s).mp hs i
  · intro s hs
    apply (mem_firstCoordinates P s).mpr
    intro i
    have hi : leafPrefix P i ∈ pieces Q := by rw [← h]; exact (mem_pieces P _).mpr ⟨i,rfl⟩
    obtain ⟨j,hj⟩ := (mem_pieces Q _).mp hi
    rw [← hj]
    exact (mem_firstCoordinates Q s).mp hs j

end TwistedBrin.Pattern

namespace TwistedBrin.Basis
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma Forest.leaf_restricts {B C : Basis ρ} (F : Forest ρ B C) (i : F.Index) :
    GermBrick.Restricts ρ (F.leaves i).val i.1.val :=
  ⟨chart ρ B i.1,Pattern.leafPrefix (F.pattern i.1) i.2,
    (chart_germ ρ B i.1).symm,(F.chart_eq i).symm⟩

lemma Forest.pieces_eq {B C : Basis ρ} (F K : Forest ρ B C) (b : B) :
    Pattern.pieces (F.pattern b) = Pattern.pieces (K.pattern b) := by
  classical
  have help (F K : Forest ρ B C) : Pattern.pieces (F.pattern b) ⊆ Pattern.pieces (K.pattern b) := by
    intro p hp
    obtain ⟨i,rfl⟩ := (Pattern.mem_pieces _ _).mp hp
    obtain ⟨⟨b',j⟩,hj⟩ := K.leaves.surjective (F.leaves ⟨b,i⟩)
    have hr : GermBrick.Restricts ρ (F.leaves ⟨b,i⟩).val b'.val := by
      rw [← hj]
      exact K.leaf_restricts ρ ⟨b',j⟩
    have hb : b = b' := refines_ancestor_unique ρ (F.leaf_restricts ρ ⟨b,i⟩) hr
    subst b'
    apply (Pattern.mem_pieces _ _).mpr
    refine ⟨j,?_⟩
    apply GermBrick.restriction_injective ρ (chart ρ B b)
    exact (K.chart_eq ⟨b,j⟩).trans ((congrArg Subtype.val hj).trans (F.chart_eq ⟨b,i⟩).symm)
  exact Finset.Subset.antisymm (help F K) (help K F)

lemma Forest.firstCoordinates_eq {B C : Basis ρ} (F K : Forest ρ B C) (b : B) :
    Pattern.firstCoordinates (F.pattern b) = Pattern.firstCoordinates (K.pattern b) :=
  Pattern.firstCoordinates_eq_of_pieces_eq (F.pieces_eq ρ K b)

lemma Forest.firstGrid_eq {B C : Basis ρ} (F K : Forest ρ B C) :
    F.firstGrid ρ = K.firstGrid ρ := by
  unfold Forest.firstGrid
  congr 1
  funext b
  exact F.firstCoordinates_eq ρ K b

lemma gridExpansion_mono (B : Basis ρ) (K L : B → Finset S) (h : ∀ b, K b ⊆ L b) :
    CutRefines ρ (gridExpansion ρ B K) (gridExpansion ρ B L) := by
  classical
  apply (Forest.expansion B (fun b => Pattern.uniform (L b).toList)).gridExpansion_refines ρ K
  intro b
  change K b ⊆ Pattern.firstCoordinates (Pattern.uniform (L b).toList)
  simpa only [Pattern.firstCoordinates_uniform,Finset.toList_toFinset] using h b

end TwistedBrin.Basis

namespace TwistedBrin.Pattern
variable {S : Type u}

lemma firstCoordinates_graft (P : Pattern S) (Q : Leaves P → Pattern S) :
    firstCoordinates P ⊆ firstCoordinates (graft P Q) := by
  intro s hs
  apply (mem_firstCoordinates _ _).mpr
  intro k
  obtain ⟨⟨i,j⟩,rfl⟩ := (graftLeaves P Q).surjective k
  rw [graft_prefix]
  intro he
  exact (mem_firstCoordinates P s).mp hs i ((List.append_eq_nil_iff.mp he).1)

@[simp] lemma firstCoordinates_leaf : firstCoordinates (.leaf : Pattern S) = ∅ := by
  classical
  simp [firstCoordinates,coordinates]

end TwistedBrin.Pattern

namespace TwistedBrin.Basis
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma Forest.firstCoordinates_mono {B C D : Basis ρ} (F : Forest ρ B C)
    (K : Forest ρ C D) (H : Forest ρ B D) (b : B) :
    Pattern.firstCoordinates (F.pattern b) ⊆ Pattern.firstCoordinates (H.pattern b) := by
  rw [H.firstCoordinates_eq ρ (F.trans K) b]
  exact Pattern.firstCoordinates_graft _ _

lemma Forest.firstCoordinates_of_grid_eq {B C : Basis ρ} (F : Forest ρ B C)
    (K : B → Finset S) (h : C = gridExpansion ρ B K) (b : B) :
    Pattern.firstCoordinates (F.pattern b) = K b := by
  classical
  subst C
  simpa only [Forest.expansion,Pattern.firstCoordinates_uniform,Finset.toList_toFinset] using
    F.firstCoordinates_eq ρ (Forest.expansion B (fun b => Pattern.uniform (K b).toList)) b

lemma gridExpansion_injective (B : Basis ρ) : Function.Injective (gridExpansion ρ B) := by
  classical
  intro K L h
  funext b
  simpa only [Forest.expansion,Pattern.firstCoordinates_uniform,Finset.toList_toFinset] using
    (Forest.expansion B (fun b => Pattern.uniform (K b).toList)).firstCoordinates_of_grid_eq ρ L h b

@[simp] lemma gridExpansion_empty (B : Basis ρ) : gridExpansion ρ B (fun _ => ∅) = B := by
  simp only [gridExpansion,Finset.toList_empty,Pattern.uniform,expand_leaf]

lemma Forest.firstGrid_ne {B C : Basis ρ} (F : Forest ρ B C) (h : B ≠ C) :
    F.firstGrid ρ ≠ B := by
  intro he
  have hh : (fun b => Pattern.firstCoordinates (F.pattern b)) = (fun _ => ∅) :=
    gridExpansion_injective ρ B (he.trans (gridExpansion_empty ρ B).symm)
  apply h
  apply F.eq_of_all_leaf
  intro b
  by_contra hn
  have hb := Pattern.firstCoordinates_nonempty hn
  rw [congrFun hh b] at hb
  exact Finset.not_nonempty_empty hb

noncomputable def firstCuts {B C : Basis ρ} (h : CutRefines ρ B C) : B → Finset S :=
  fun b => Pattern.firstCoordinates ((Classical.choice h).pattern b)

lemma firstCuts_forest {B C : Basis ρ} (h : CutRefines ρ B C) (F : Forest ρ B C) (b : B) :
    firstCuts ρ h b = Pattern.firstCoordinates (F.pattern b) :=
  (Classical.choice h).firstCoordinates_eq ρ F b

lemma firstCuts_mono {B C D : Basis ρ} (hBC : CutRefines ρ B C) (hCD : CutRefines ρ C D)
    (hBD : CutRefines ρ B D) (b : B) : firstCuts ρ hBC b ⊆ firstCuts ρ hBD b :=
  (Classical.choice hBC).firstCoordinates_mono ρ (Classical.choice hCD) (Classical.choice hBD) b

lemma firstCuts_grid (B : Basis ρ) (K : B → Finset S) (h : CutRefines ρ B (gridExpansion ρ B K)) :
    firstCuts ρ h = K := by
  funext b
  exact (Classical.choice h).firstCoordinates_of_grid_eq ρ K rfl b

lemma gridExpansion_refines_iff {B C : Basis ρ} (h : CutRefines ρ B C) (K : B → Finset S) :
    CutRefines ρ (gridExpansion ρ B K) C ↔ ∀ b, K b ⊆ firstCuts ρ h b := by
  constructor
  · intro hKC b
    have hh := firstCuts_mono ρ (cutRefines_gridExpansion ρ B K) hKC h b
    rwa [firstCuts_grid] at hh
  · intro hh
    exact (Classical.choice h).gridExpansion_refines ρ K hh

noncomputable def firstCore {B C : Basis ρ} (h : CutRefines ρ B C) : Basis ρ :=
  gridExpansion ρ B (firstCuts ρ h)

lemma firstCore_lower {B C : Basis ρ} (h : CutRefines ρ B C) : CutRefines ρ B (firstCore ρ h) :=
  cutRefines_gridExpansion ρ B _

lemma firstCore_upper {B C : Basis ρ} (h : CutRefines ρ B C) : CutRefines ρ (firstCore ρ h) C :=
  (gridExpansion_refines_iff ρ h _).mpr (fun _ _ h => h)

lemma firstCore_ne {B C : Basis ρ} (h : CutRefines ρ B C) (hne : B ≠ C) : firstCore ρ h ≠ B :=
  (Classical.choice h).firstGrid_ne ρ hne

lemma firstCore_mono {B C D : Basis ρ} (hBC : CutRefines ρ B C) (hCD : CutRefines ρ C D)
    (hBD : CutRefines ρ B D) : CutRefines ρ (firstCore ρ hBC) (firstCore ρ hBD) :=
  gridExpansion_mono ρ B _ _ (firstCuts_mono ρ hBC hCD hBD)

lemma firstCore_grid (B : Basis ρ) (K : B → Finset S) (h : CutRefines ρ B (gridExpansion ρ B K)) :
    firstCore ρ h = gridExpansion ρ B K := by rw [firstCore,firstCuts_grid]

end

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

structure CutInterval (B C : Basis ρ) where
  val : Basis ρ
  lower : CutRefines ρ B val
  upper : CutRefines ρ val C

namespace CutInterval
variable {ρ} {B C : Basis ρ}
@[ext] lemma ext {D E : CutInterval ρ B C} (h : D.val = E.val) : D = E := by
  cases D; cases E; simp_all
instance : PartialOrder (CutInterval ρ B C) where
  le D E := CutRefines ρ D.val E.val
  le_refl D := cutRefines_refl ρ D.val
  le_trans _ _ _ := cutRefines_trans ρ
  le_antisymm _ _ h k := ext (cutRefines_antisymm ρ h k)
instance : Finite (CutInterval ρ B C) := by
  let := finite_interval ρ B C
  exact Finite.of_injective
    (fun D : CutInterval ρ B C =>
      (⟨D.val,le_of_cutRefines ρ D.lower,le_of_cutRefines ρ D.upper⟩ :
        {E : Basis ρ // B ≤ E ∧ E ≤ C}))
    (fun _ _ h => ext (congrArg Subtype.val h))

noncomputable def core (D : CutInterval ρ B C) : CutInterval ρ B C :=
  ⟨firstCore ρ D.lower, firstCore_lower ρ D.lower,
    cutRefines_trans ρ (firstCore_upper ρ D.lower) D.upper⟩
lemma core_le (D : CutInterval ρ B C) : D.core ≤ D := firstCore_upper ρ D.lower
lemma core_mono : Monotone (core : CutInterval ρ B C → CutInterval ρ B C) := by
  intro D E h
  exact firstCore_mono ρ D.lower h E.lower
@[simp] lemma core_core (D : CutInterval ρ B C) : D.core.core = D.core := by
  apply ext
  exact firstCore_grid ρ B (firstCuts ρ D.lower) _

noncomputable def coreHom : CutInterval ρ B C →o CutInterval ρ B C :=
  ⟨core,core_mono⟩

lemma core_ne_bottom (D : CutInterval ρ B C) (h : D.val ≠ B) : D.core.val ≠ B :=
  firstCore_ne ρ D.lower h.symm
lemma core_ne_top (D : CutInterval ρ B C) (h : D.val ≠ C) : D.core.val ≠ C := by
  intro he
  apply h
  apply cutRefines_antisymm ρ D.upper
  have hh : CutRefines ρ D.core.val D.val := firstCore_upper ρ D.lower
  simpa only [he] using hh
end CutInterval

def CutSelections {B C : Basis ρ} (h : CutRefines ρ B C) :=
  {K : B → Finset S // ∀ b, K b ⊆ firstCuts ρ h b}

namespace CutSelections
variable {ρ} {B C : Basis ρ} (h : CutRefines ρ B C)
instance : PartialOrder (CutSelections ρ h) := inferInstanceAs
  (PartialOrder {K : B → Finset S // ∀ b, K b ⊆ firstCuts ρ h b})

noncomputable def toInterval (K : CutSelections ρ h) : CutInterval ρ B C :=
  ⟨gridExpansion ρ B K.val,cutRefines_gridExpansion ρ B _,
    (gridExpansion_refines_iff ρ h K.val).mpr K.property⟩
noncomputable def ofInterval (D : CutInterval ρ B C) : CutSelections ρ h :=
  ⟨firstCuts ρ D.lower, firstCuts_mono ρ D.lower D.upper h⟩

lemma of_to (K : CutSelections ρ h) : ofInterval h (toInterval h K) = K := by
  apply Subtype.ext
  exact firstCuts_grid ρ B K.val _
lemma to_of (D : CutInterval ρ B C) : toInterval h (ofInterval h D) = D.core := by
  apply CutInterval.ext
  rfl
lemma to_le_iff (K : CutSelections ρ h) (D : CutInterval ρ B C) :
    toInterval h K ≤ D ↔ K ≤ ofInterval h D :=
  gridExpansion_refines_iff ρ D.lower K.val
lemma to_mono : Monotone (toInterval h) := by
  intro K L hKL
  exact gridExpansion_mono ρ B K.val L.val hKL
lemma of_mono : Monotone (ofInterval h) := by
  intro D E hDE
  exact firstCuts_mono ρ D.lower hDE E.lower

noncomputable def fixedEquiv : CutSelections ρ h ≃o
    {D : CutInterval ρ B C // D.core = D} where
  toFun K := ⟨toInterval h K,by
    apply CutInterval.ext
    exact firstCore_grid ρ B K.val _⟩
  invFun D := ofInterval h D.val
  left_inv := of_to h
  right_inv D := by
    apply Subtype.ext
    exact (to_of h D.val).trans D.property
  map_rel_iff' := by
    intro K L
    change toInterval h K ≤ toInterval h L ↔ K ≤ L
    rw [to_le_iff, of_to]
end CutSelections
end TwistedBrin.Basis

end

end OAI
