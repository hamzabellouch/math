import OAI.Combinatorics.CycleDecomposition.ScaleDecomposition

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section

namespace ErdosGallai.Indexing
noncomputable section
open Finset

variable {I : Type cycleUniverse1} [DecidableEq I]

def batchWeight (w : I → ℕ) (b : Finset I) : ℝ := ∑ i ∈ b, (w i : ℝ)

lemma batchWeight_nonneg {I : Type cycleUniverse2} [_contextInstance1 : DecidableEq I] (w : I → ℕ) (b : Finset I) : 0 ≤ batchWeight w b := by
  exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

lemma indexed_batch_construction (w : I → ℕ) (A : Finset I) (B : ℝ) (hB : 0 < B)
    (hw : ∀ i ∈ A, (w i : ℝ) ≤ B/2) :
    ∃ P : List (Finset I),
      P.Pairwise Disjoint ∧
      (∀ i, i ∈ A ↔ ∃ b ∈ P, i ∈ b) ∧
      (∀ b ∈ P, b.Nonempty ∧ batchWeight w b ≤ B) ∧
      (∀ b ∈ P.tail, B/2 < batchWeight w b) ∧
      (P.map (batchWeight w)).sum = batchWeight w A := by
  induction A using Finset.induction_on with
  | empty =>
    refine ⟨[], by simp, ?_, by simp, by simp, ?_⟩
    · simp
    · simp [batchWeight]
  | @insert a A ha ih =>
    obtain ⟨P, hdisj, hcover, hbins, hheavy, hmass⟩ := ih (fun i hi => hw i (by simp [hi]))
    have hwa := hw a (by simp)
    have haP : ∀ b ∈ P, a ∉ b := by
      intro b hb hab
      exact ha ((hcover a).mpr ⟨b,hb,hab⟩)
    cases P with
    | nil =>
      have hAz : A = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        simpa using (hcover i).mp hi
      subst A
      refine ⟨[{a}], by simp, ?_, ?_, by simp, ?_⟩
      · intro i; simp
      · intro b hb
        simp only [List.mem_singleton] at hb
        subst b
        exact ⟨by simp, by simp [batchWeight]; linarith⟩
      · simp
    | cons b bs =>
      have hab : a ∉ b := haP b (by simp)
      obtain ⟨hbne,hbB⟩ := hbins b (by simp)
      by_cases hlight : batchWeight w b ≤ B/2
      · refine ⟨insert a b :: bs, ?_, ?_, ?_, ?_, ?_⟩
        · rw [List.pairwise_cons]
          refine ⟨?_, (List.pairwise_cons.mp hdisj).2⟩
          intro d hd
          exact Finset.disjoint_insert_left.mpr ⟨haP d (by simp [hd]),
            (List.pairwise_cons.mp hdisj).1 d hd⟩
        · intro i
          constructor
          · intro hia
            rcases Finset.mem_insert.mp hia with hia | hi
            · exact ⟨insert a b, by simp, by simp [hia]⟩
            · obtain ⟨d,hd,hid⟩ := (hcover i).mp hi
              rcases List.mem_cons.mp hd with hd | hd
              · subst d
                exact ⟨insert a b, by simp, Finset.mem_insert_of_mem hid⟩
              · exact ⟨d, by simp [hd], hid⟩
          · rintro ⟨d,hd,hid⟩
            rcases List.mem_cons.mp hd with rfl | hd
            · rcases Finset.mem_insert.mp hid with rfl | hib
              · simp
              · exact Finset.mem_insert_of_mem ((hcover i).mpr ⟨b, by simp, hib⟩)
            · exact Finset.mem_insert_of_mem ((hcover i).mpr ⟨d, by simp [hd], hid⟩)
        · intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · refine ⟨by simp, ?_⟩
            simp only [batchWeight, Finset.sum_insert hab]
            change (w a : ℝ) + batchWeight w b ≤ B
            linarith
          · exact hbins d (by simp [hd])
        · simpa using hheavy
        · simp only [List.map_cons, List.sum_cons] at hmass ⊢
          rw [show batchWeight w (insert a b) = (w a:ℝ)+batchWeight w b by
            simp [batchWeight, hab], show batchWeight w (insert a A) = (w a:ℝ)+batchWeight w A by
            simp [batchWeight, ha]]
          linarith
      · refine ⟨{a} :: b :: bs, ?_, ?_, ?_, ?_, ?_⟩
        · rw [List.pairwise_cons]
          exact ⟨fun d hd => Finset.disjoint_singleton_left.mpr (haP d hd), hdisj⟩
        · intro i
          constructor
          · intro hi
            rcases Finset.mem_insert.mp hi with hia | hi
            · exact ⟨{a}, by simp, by simp [hia]⟩
            · obtain ⟨d,hd,hid⟩ := (hcover i).mp hi
              exact ⟨d, List.mem_cons_of_mem _ hd, hid⟩
          · rintro ⟨d,hd,hid⟩
            rcases List.mem_cons.mp hd with rfl | hd
            · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hid))
            · exact Finset.mem_insert_of_mem ((hcover i).mpr ⟨d,hd,hid⟩)
        · intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact ⟨by simp, by simp [batchWeight]; linarith⟩
          · exact hbins d hd
        · intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact lt_of_not_ge hlight
          · exact hheavy d hd
        · simp only [List.map_cons, List.sum_cons] at hmass ⊢
          simp only [batchWeight, Finset.sum_singleton, Finset.sum_insert ha] at hmass ⊢
          linarith

lemma batch_tail_mass {I : Type cycleUniverse3} [_contextInstance1 : DecidableEq I] (w : I → ℕ) (P : List (Finset I)) (t : ℝ)
    (ht : ∀ b ∈ P, t ≤ batchWeight w b) :
    (P.length : ℝ)*t ≤ (P.map (batchWeight w)).sum := by
  induction P with
  | nil => simp
  | cons b bs ih =>
    have hb := ht b (by simp)
    have hbs := ih (fun d hd => ht d (by simp [hd]))
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.map_cons, List.sum_cons]
    nlinarith

theorem indexed_batch_partition (w : I → ℕ) (A : Finset I) (B : ℝ) (hB : 0 < B)
    (hw : ∀ i ∈ A, (w i : ℝ) ≤ B/2) :
    ∃ P : List (Finset I),
      P.Pairwise Disjoint ∧
      (∀ i, i ∈ A ↔ ∃ b ∈ P, i ∈ b) ∧
      (∀ b ∈ P, b.Nonempty ∧ batchWeight w b ≤ B) ∧
      (P.map (batchWeight w)).sum = batchWeight w A ∧
      (P.length : ℝ) ≤ 1 + 2*batchWeight w A/B := by
  obtain ⟨P,hd,hc,hb,ht,hm⟩ := indexed_batch_construction w A B hB hw
  refine ⟨P,hd,hc,hb,hm,?_⟩
  have htail := batch_tail_mass w P.tail (B/2) (fun b hb => (ht b hb).le)
  cases P with
  | nil =>
    simp only [List.length_nil, Nat.cast_zero]
    have hh := div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (batchWeight_nonneg w A)) hB.le
    linarith
  | cons b bs =>
    simp only [List.tail_cons, List.length_cons, Nat.cast_add, Nat.cast_one] at htail ⊢
    simp only [List.map_cons, List.sum_cons] at hm
    have hb0 := batchWeight_nonneg w b
    have hdv : (bs.length : ℝ) ≤ 2*batchWeight w A/B := by
      apply (le_div_iff₀ hB).mpr
      linarith
    linarith

end
end ErdosGallai.Indexing

namespace ErdosGallai.Indexing
noncomputable section
open scoped BigOperators

private theorem cover_card_le {V : Type cycleUniverse4} {I : Type cycleUniverse5} [DecidableEq V] [Fintype I]
    (S : Finset V) (W : I → Finset V)
    (h : S ⊆ Finset.univ.biUnion W) :
    S.card ≤ ∑ i, (W i).card :=
  (Finset.card_le_card h).trans Finset.card_biUnion_le

private theorem disjoint_piece_inter {V : Type cycleUniverse6} {J : Type cycleUniverse7} [DecidableEq V] [Fintype J]
    (R : J → Finset V) (hR : Pairwise fun i j => Disjoint (R i) (R j))
    (S : Finset V) :
    (S ∩ Finset.univ.biUnion R).card = ∑ j, (S ∩ R j).card := by
  rw [Finset.inter_biUnion]
  apply Finset.card_biUnion
  intro i _ j _ hij
  exact (hR hij).mono Finset.inter_subset_right Finset.inter_subset_right

theorem active_occurrences {V : Type cycleUniverse8} {I : Type cycleUniverse9} {J : Type cycleUniverse10} [DecidableEq V]
    [Fintype I] [Fintype J]
    (Y good : Finset V) (W : I → Finset V) (R : J → Finset V)
    (_hW : ∀ i, W i ⊆ Y) (hRsub : ∀ j, R j ⊆ Y)
    (hcover : Y ⊆ Finset.univ.biUnion W)
    (hR : Pairwise fun i j => Disjoint (R i) (R j))
    (keep : I → J → Prop) [∀ i j, Decidable (keep i j)] :
    let active := ∑ i, ∑ j, if keep i j then (W i ∩ R j ∩ good).card else 0
    let skipped := ∑ i, ∑ j, if keep i j then 0 else (W i ∩ R j ∩ good).card
    (∑ j, (R j).card) ≤ active + skipped + (Y \ good).card ∧
    active + Y.card ≤ (∑ j, (R j).card) + ∑ i, (W i).card := by
  classical
  dsimp only
  let U := Finset.univ.biUnion R
  have hU : U ⊆ Y := by
    intro v hv
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hv
    exact hRsub j hj
  have hcard : U.card = ∑ j, (R j).card := by
    apply Finset.card_biUnion
    intro i _ j _ hij
    exact hR hij
  let mass := ∑ i, ∑ j, (W i ∩ R j ∩ good).card
  let whole := ∑ i, (W i ∩ U).card
  have hsplit :
      (∑ i, ∑ j, if keep i j then (W i ∩ R j ∩ good).card else 0) +
      (∑ i, ∑ j, if keep i j then 0 else (W i ∩ R j ∩ good).card) = mass := by
    dsimp [mass]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> omega
  have hgood : (U ∩ good).card ≤ mass := by
    have hc : U ∩ good ⊆ Finset.univ.biUnion (fun i => W i ∩ U ∩ good) := by
      intro v hv
      obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp (hcover (hU (Finset.mem_inter.mp hv).1))
      exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_inter.mpr
        ⟨Finset.mem_inter.mpr ⟨hvi, (Finset.mem_inter.mp hv).1⟩,
          (Finset.mem_inter.mp hv).2⟩⟩
    apply (cover_card_le (U ∩ good) _ hc).trans
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro i _
    have heq : W i ∩ U ∩ good = (W i ∩ good) ∩ U := by ext v; simp only [Finset.mem_inter]; tauto
    rw [heq, disjoint_piece_inter R hR]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    ext v
    simp only [Finset.mem_inter]
    tauto
  have hbad : (U \ good).card ≤ (Y \ good).card := by
    apply Finset.card_le_card
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨hU (Finset.mem_sdiff.mp hv).1, (Finset.mem_sdiff.mp hv).2⟩
  have hmass : mass ≤ whole := by
    apply Finset.sum_le_sum
    intro i _
    rw [disjoint_piece_inter R hR]
    exact Finset.sum_le_sum fun j _ => Finset.card_le_card Finset.inter_subset_left
  have houtside : (Y \ U).card ≤ ∑ i, (W i \ U).card := by
    apply cover_card_le
    intro v hv
    obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp (hcover (Finset.mem_sdiff.mp hv).1)
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_sdiff.mpr ⟨hvi, (Finset.mem_sdiff.mp hv).2⟩⟩
  have hY : U.card + (Y \ U).card = Y.card := by
    simpa only [Finset.inter_eq_right.mpr hU] using Finset.card_inter_add_card_sdiff Y U
  have hWsum : whole + (∑ i, (W i \ U).card) = ∑ i, (W i).card := by
    dsimp [whole]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.card_inter_add_card_sdiff (W i) U
  have hUgood := Finset.card_inter_add_card_sdiff U good
  constructor <;> omega

theorem skipped_occurrences_bound {V : Type cycleUniverse11} {I : Type cycleUniverse12} {J : Type cycleUniverse13} [DecidableEq V]
    [Fintype I] [Fintype J] (W : I → Finset V) (R : J → Finset V)
    (good : Finset V) (L : ℕ) :
    (∑ i, ∑ j, if L ≤ (W i ∩ R j ∩ good).card then 0
      else (W i ∩ R j ∩ good).card) ≤ L * Fintype.card I * Fintype.card J := by
  classical
  calc
    _ ≤ ∑ _i : I, ∑ _j : J, L := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      split_ifs <;> omega
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]; ring

end
end ErdosGallai.Indexing

namespace ErdosGallai.Indexing
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

lemma list_pairwise_get {A : Type cycleUniverse14} {R : A → A → Prop} {L : List A}
    (h : L.Pairwise R) (hs : (∀ ⦃left right⦄, R left right → R right left)) : Pairwise fun i j : Fin L.length => R (L.get i) (L.get j) := by
  intro i j hij
  rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun he => hij (Fin.ext he)) with hlt | hgt
  · exact List.pairwise_iff_getElem.mp h i.val j.val i.isLt j.isLt hlt
  · exact hs (List.pairwise_iff_getElem.mp h j.val i.val j.isLt i.isLt hgt)

lemma list_sum_get {A : Type cycleUniverse15} {M : Type cycleUniverse16} [AddCommMonoid M] (L : List A) (f : A → M) :
    (∑ i : Fin L.length, f (L.get i)) = (L.map f).sum := by
  rw [← List.sum_ofFn]
  calc
    _ = (List.map f (List.ofFn L.get)).sum := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [List.ofFn_get]

structure GraphBatches {V : Type} (F : SimpleGraph V) (Y : Finset V) (B T : ℝ) where
  Index : Type
  finite : Fintype Index
  graph : Index → SimpleGraph V
  vertices : Index → Finset V
  graph_le : ∀ i, graph i ≤ F
  disjoint : Pairwise fun i j => Disjoint (graph i).edgeSet (graph j).edgeSet
  edge_cover : (⋃ i, (graph i).edgeSet) = F.edgeSet
  supported : ∀ i, ∀ ⦃x y⦄, (graph i).Adj x y → x ∈ vertices i ∧ y ∈ vertices i
  subset : ∀ i, vertices i ⊆ Y
  vertex_cover : Y ⊆ univ.biUnion vertices
  order_le : ∀ i, ((vertices i).card:ℝ) ≤ B
  mass_le : (∑ i, ((vertices i).card:ℝ)) ≤ T
  count_le : (Fintype.card Index:ℝ) ≤ 1+2*T/B
attribute [instance] GraphBatches.finite

theorem materialize_batches {V I : Type} [Fintype I]
    (F : SimpleGraph V) (Y : Finset V) (H : I → SimpleGraph V) (U : I → Finset V)
    (hHH : Pairwise fun i j => Disjoint (H i).edgeSet (H j).edgeSet)
    (hu : (⋃ i, (H i).edgeSet) = F.edgeSet)
    (hU : ∀ i, ∀ ⦃x y⦄, (H i).Adj x y → x ∈ U i ∧ y ∈ U i)
    (hUY : ∀ i, U i ⊆ Y) (hY : Y ⊆ univ.biUnion U)
    (B : ℝ) (hB : 0 < B) (hsmall : ∀ i, ((U i).card:ℝ) ≤ B/2) :
    Nonempty (GraphBatches F Y B (∑ i, ((U i).card:ℝ))) := by
  classical
  obtain ⟨L,hLd,hLc,hLn,hLm,hLnum⟩ := indexed_batch_partition (fun i => (U i).card) univ B hB (fun i _ => hsmall i)
  let A := Fin L.length
  let bag (a : A) : Finset I := L.get a
  let W (a : A) := (bag a).biUnion U
  let J (a : A) : SimpleGraph V := ⨆ i ∈ bag a, H i
  have hbagd : Pairwise fun a b => Disjoint (bag a) (bag b) := list_pairwise_get hLd (fun _ _ h => h.symm)
  have hbagcov (i : I) : ∃ a : A, i ∈ bag a := by
    obtain ⟨b,hb,hi⟩ := (hLc i).mp (mem_univ _)
    obtain ⟨k,hk⟩ := List.mem_iff_get.mp hb
    exact ⟨k,by change i ∈ L.get k; rwa [hk]⟩
  have hJedge (a : A) : (J a).edgeSet = ⋃ i ∈ bag a, (H i).edgeSet := by
    ext e
    induction e using Sym2.ind with
    | _ x y => simp [J,SimpleGraph.mem_edgeSet,SimpleGraph.iSup_adj]
  have hJsub (a : A) : (J a).edgeSet ⊆ F.edgeSet := by
    rw [hJedge,← hu]
    exact Set.iUnion₂_subset fun i _ => Set.subset_iUnion (fun j : I => (H j).edgeSet) i
  have hWweight (a : A) : ((W a).card:ℝ) ≤ batchWeight (fun i => (U i).card) (bag a) := by
    have hh := Finset.card_biUnion_le (s := bag a) (t := U)
    dsimp only [W,batchWeight]
    exact_mod_cast hh
  have hJd : Pairwise fun a b => Disjoint (J a).edgeSet (J b).edgeSet := by
    intro a b hab
    rw [hJedge,hJedge]
    apply Set.disjoint_left.mpr
    rintro e he he'
    obtain ⟨i,hi,he⟩ := Set.mem_iUnion₂.mp he
    obtain ⟨j,hj,he'⟩ := Set.mem_iUnion₂.mp he'
    have hij : i ≠ j := by rintro rfl; exact Finset.disjoint_left.mp (hbagd hab) hi hj
    exact Set.disjoint_left.mp (hHH hij) he he'
  refine ⟨{
    Index := A
    finite := inferInstance
    graph := J
    vertices := W
    graph_le := fun a => SimpleGraph.edgeSet_subset_edgeSet.mp (hJsub a)
    disjoint := hJd
    edge_cover := ?_
    supported := ?_
    subset := ?_
    vertex_cover := ?_
    order_le := ?_
    mass_le := ?_
    count_le := ?_ }⟩
  · apply Set.Subset.antisymm (Set.iUnion_subset hJsub)
    intro e he
    rw [← hu] at he
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp he
    obtain ⟨a,hia⟩ := hbagcov i
    exact Set.mem_iUnion.mpr ⟨a,by rw [hJedge]; exact Set.mem_iUnion₂.mpr ⟨i,hia,hi⟩⟩
  · intro a x y hxy
    have he : s(x,y) ∈ (J a).edgeSet := hxy
    rw [hJedge] at he
    obtain ⟨i,hi,he⟩ := Set.mem_iUnion₂.mp he
    exact ⟨Finset.mem_biUnion.mpr ⟨i,hi,(hU i he).1⟩,Finset.mem_biUnion.mpr ⟨i,hi,(hU i he).2⟩⟩
  · intro a v hv
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hv
    exact hUY i hi
  · intro v hv
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp (hY hv)
    obtain ⟨a,ha⟩ := hbagcov i
    exact Finset.mem_biUnion.mpr ⟨a,mem_univ _,Finset.mem_biUnion.mpr ⟨i,ha,hi⟩⟩
  · intro a
    exact (hWweight a).trans ((hLn (bag a) (L.get_mem a)).2)
  · calc
      _ ≤ ∑ a, batchWeight (fun i => (U i).card) (bag a) := Finset.sum_le_sum (fun a _ => hWweight a)
      _ = _ := by rw [list_sum_get,hLm]; rfl
  · simpa only [A,Fintype.card_fin,batchWeight] using hLnum

end
end ErdosGallai.Indexing

namespace ErdosGallai.Indexing
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

def goodVertices {V : Type} [Fintype V] (F : SimpleGraph V) (Y : Finset V) (a : ℝ) : Finset V :=
  Y.filter fun v => (F.degree v:ℝ) ≤ a

lemma bad_vertices_degree_bound {V : Type} [Fintype V] (F : SimpleGraph V) (Y : Finset V) (a : ℝ) :
    a * ((Y \ goodVertices F Y a).card:ℝ) ≤ 2 * (F.edgeFinset.card:ℝ) := by
  classical
  let bad := Y \ goodVertices F Y a
  have hbad (v) (hv : v ∈ bad) : a ≤ (F.degree v:ℝ) := by
    have hn := (Finset.mem_sdiff.mp hv).2
    exact le_of_lt (lt_of_not_ge (fun h => hn (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hv).1,h⟩)))
  calc
    _ = ∑ v ∈ bad, a := by simp [bad,mul_comm]
    _ ≤ ∑ v ∈ bad, (F.degree v:ℝ) := Finset.sum_le_sum hbad
    _ ≤ ∑ v, (F.degree v:ℝ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
    _ = _ := by exact_mod_cast F.sum_degrees_eq_twice_card_edges

structure ActiveFamily {V R B : Type} [Fintype V] [Fintype R] [Fintype B]
    (F : SimpleGraph V) (Y : Finset V) (W : B → Finset V) (U : R → Finset V) (a L : ℝ) where
  Index : B → Type
  finite : ∀ b, Fintype (Index b)
  vertices : ∀ b, Index b → Finset V
  router : ∀ b, Index b → R
  subset_batch : ∀ b i, vertices b i ⊆ W b
  subset_router : ∀ b i, vertices b i ⊆ U (router b i)
  disjoint : ∀ b, Pairwise fun i j => Disjoint (vertices b i) (vertices b j)
  degree_le : ∀ b i v, v ∈ vertices b i → (F.degree v:ℝ) ≤ a
  large : ∀ b i, L ≤ ((vertices b i).card:ℝ)
  lower : (∑ r, ((U r).card:ℝ)) - ((Y \ goodVertices F Y a).card:ℝ) -
    L * Fintype.card B * Fintype.card R ≤ ∑ b, ∑ i, ((vertices b i).card:ℝ)
  upper : (∑ b, ∑ i, ((vertices b i).card:ℝ)) + Y.card ≤
    (∑ r, ((U r).card:ℝ)) + ∑ b, ((W b).card:ℝ)
attribute [instance] ActiveFamily.finite

theorem choose_active_family {V R B : Type} [Fintype V] [Fintype R] [Fintype B]
    (F : SimpleGraph V) (Y : Finset V) (W : B → Finset V) (U : R → Finset V) (a L : ℝ)
    (hL : 0 ≤ L) (hW : ∀ b, W b ⊆ Y) (hU : ∀ r, U r ⊆ Y)
    (hcov : Y ⊆ univ.biUnion W) (hUd : Pairwise fun r s => Disjoint (U r) (U s)) :
    Nonempty (ActiveFamily F Y W U a L) := by
  classical
  let good := goodVertices F Y a
  let S (b : B) (r : R) := W b ∩ U r ∩ good
  let keep (b : B) (r : R) := L ≤ ((S b r).card:ℝ)
  let I (b : B) := {r : R // keep b r}
  let X (b : B) (i : I b) := S b i.val
  have hsum (b : B) : (∑ i : I b, ((X b i).card:ℝ)) =
      ∑ r, if keep b r then ((S b r).card:ℝ) else 0 := by
    rw [← Finset.sum_filter]
    simpa only [Finset.subtype_univ] using (Finset.sum_subtype_eq_sum_filter (s := univ) (p := keep b) (fun r => ((S b r).card:ℝ)))
  have hadd := active_occurrences Y good W U hW hU hcov hUd keep
  dsimp only at hadd
  have hlow : (∑ r, ((U r).card:ℝ)) ≤
      (∑ b, ∑ r, if keep b r then ((S b r).card:ℝ) else 0) +
      (∑ b, ∑ r, if keep b r then 0 else ((S b r).card:ℝ)) + ((Y \ good).card:ℝ) := by
    exact_mod_cast hadd.1
  have hhigh : (∑ b, ∑ r, if keep b r then ((S b r).card:ℝ) else 0) + Y.card ≤
      (∑ r, ((U r).card:ℝ)) + ∑ b, ((W b).card:ℝ) := by exact_mod_cast hadd.2
  have hskip : (∑ b, ∑ r, if keep b r then 0 else ((S b r).card:ℝ)) ≤
      L * Fintype.card B * Fintype.card R := by
    calc
      _ ≤ ∑ _b : B, ∑ _r : R, L := by
        apply Finset.sum_le_sum; intro b _
        apply Finset.sum_le_sum; intro r _
        split_ifs with hk
        · exact hL
        · exact le_of_lt (lt_of_not_ge hk)
      _ = _ := by simp; ring
  refine ⟨{
    Index := I
    finite := fun _ => inferInstance
    vertices := X
    router := fun _ i => i.val
    subset_batch := fun _ _ => Finset.inter_subset_left.trans Finset.inter_subset_left
    subset_router := fun _ _ => Finset.inter_subset_left.trans Finset.inter_subset_right
    disjoint := ?_
    degree_le := ?_
    large := fun _ i => i.property
    lower := ?_
    upper := ?_ }⟩
  · intro b i j hij
    exact (hUd (fun h => hij (Subtype.ext h))).mono
      (Finset.inter_subset_left.trans Finset.inter_subset_right)
      (Finset.inter_subset_left.trans Finset.inter_subset_right)
  · intro b i v hv
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp hv).2).2
  · simp_rw [hsum]
    dsimp only [good] at hlow hskip
    linarith
  · simpa only [hsum] using hhigh

lemma thirds_le_halves {k : ℕ} (hk : 8 ≤ k) : (k:ℝ)/3 ≤ (k/2:ℕ) := by
  have h : k ≤ 3*(k/2) := by omega
  have h' : (k:ℝ) ≤ 3*(k/2:ℕ) := by exact_mod_cast h
  linarith

end
end ErdosGallai.Indexing

end
end
end

end OAI
