import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.CardTreeVerticesLe

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter

namespace OrdinaryCorrelations.NumericalSubtrees
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.GraphKernel.PrimeSystem
open Finset Classical
open scoped symmDiff

def bitWeight {ι : Type*} [Fintype ι] (A β : ℝ) (x : ι → Bool) : ℝ :=
  ∏ i, if x i then A*β else β

def Demand {ι : Type*} [DecidableEq ι] (E O : Finset ι) (x : ι → Bool) : Prop :=
  ∀ i ∈ O, x i = decide (i ∈ E)

lemma bitWeight_nonneg {ι : Type*} [Fintype ι] (A β : ℝ)
    (hA : 0 ≤ A) (hβ : 0 ≤ β) (x : ι → Bool) : 0 ≤ bitWeight A β x := by
  unfold bitWeight
  apply prod_nonneg
  intro i hi
  split_ifs <;> positivity

lemma sum_bitWeight {ι : Type*} [Fintype ι] [DecidableEq ι] (A β : ℝ)
    (hβ : β * (1+A) = 1) : ∑ x : ι → Bool, bitWeight A β x = 1 := by
  unfold bitWeight
  rw [← Fintype.prod_sum (fun (_i : ι) (b : Bool) => if b then A*β else β)]
  have he : (∑ b : Bool, if b then A*β else β) = (1 : ℝ) := by
    simp only [Fintype.sum_bool,Bool.false_eq_true,ite_false,ite_true]
    nlinarith only [hβ]
  simp only [he,prod_const_one]

lemma demand_product {ι : Type*} [Fintype ι] [DecidableEq ι] (A β : ℝ)
    (E O : Finset ι) (x : ι → Bool) :
    (if Demand E O x then bitWeight A β x else 0) =
      ∏ i, if i ∈ O → x i = decide (i ∈ E) then (if x i then A*β else β) else 0 := by
  by_cases hx : Demand E O x
  · rw [ite_eq_left hx, bitWeight]
    apply prod_congr rfl
    intro i hi
    rw [ite_eq_left (hx i)]
  · rw [ite_eq_right hx]
    have hn : ∃ i, i ∈ O ∧ x i ≠ decide (i ∈ E) := by
      simpa only [Demand,not_forall,exists_prop] using hx
    obtain ⟨i,hi,hni⟩ := hn
    symm
    apply prod_eq_zero (mem_univ i)
    rw [ite_eq_right (fun h => hni (h hi))]

theorem demand_weight {ι : Type*} [Fintype ι] [DecidableEq ι] (A β : ℝ)
    (hβ : β * (1+A) = 1) (E O : Finset ι) (hEO : E ⊆ O) :
    (∑ x : ι → Bool, if Demand E O x then bitWeight A β x else 0) =
      A^E.card * β^O.card := by
  simp_rw [demand_product]
  rw [← Fintype.prod_sum (fun (i : ι) (b : Bool) =>
    if i ∈ O → b = decide (i ∈ E) then (if b then A*β else β) else 0)]
  have hi : ∀ i : ι,
      (∑ b : Bool, if i ∈ O → b = decide (i ∈ E) then (if b then A*β else β) else 0) =
        (if i ∈ E then A else 1) * (if i ∈ O then β else 1) := by
    intro i
    by_cases hE : i ∈ E
    · have hO := hEO hE
      simp [hE,hO]
    · by_cases hO : i ∈ O
      · simp [hE,hO]
      · simp only [hE,hO,false_implies,ite_true,Fintype.sum_bool,
          Bool.false_eq_true,ite_false]
        nlinarith only [hβ]
  simp_rw [hi]
  rw [prod_mul_distrib]
  simp only [prod_ite,filter_mem_eq_inter,univ_inter,prod_const_one,mul_one,prod_const]

variable {h ℓ : ℕ}

def Grows (w : ClosedLine h ℓ) (v : ℤ) (E : Finset (Fin ℓ)) : Prop :=
  E ⊆ w.treeSteps ∧ ∀ e ∈ E,
    w.offset e.castSucc = v ∨ ∃ j ∈ E, j < e ∧ w.offset j.succ = w.offset e.castSucc

def reached (w : ClosedLine h ℓ) (v : ℤ) (E : Finset (Fin ℓ)) : Finset ℤ :=
  insert v (E.image (fun e => w.offset e.succ))

def outgoing (w : ClosedLine h ℓ) (V : Finset ℤ) : Finset (Fin ℓ) :=
  w.treeSteps.filter (fun e => w.offset e.castSucc ∈ V)

lemma grows_edge_origins (w : ClosedLine h ℓ) {v : ℤ} {E : Finset (Fin ℓ)}
    (hg : Grows w v E) {e : Fin ℓ} (he : e ∈ E) : w.offset e.castSucc ∈ reached w v E := by
  rcases hg.2 e he with hr | ⟨j,hj,hje,hjv⟩
  · simp [reached,hr]
  · exact mem_insert_of_mem (mem_image.mpr ⟨j,hj,hjv⟩)

lemma grows_outgoing (w : ClosedLine h ℓ) {v : ℤ} {E : Finset (Fin ℓ)}
    (hg : Grows w v E) : E ⊆ outgoing w (reached w v E) := by
  intro e he
  exact mem_filter.mpr ⟨hg.1 he,grows_edge_origins w hg he⟩

theorem grows_demands_disjoint (w : ClosedLine h ℓ) {v : ℤ} {E F : Finset (Fin ℓ)}
    (hE : Grows w v E) (hF : Grows w v F) (hne : E ≠ F) (x : Fin ℓ → Bool) :
    ¬ (Demand E (outgoing w (reached w v E)) x ∧
       Demand F (outgoing w (reached w v F)) x) := by
  have hd : (E ∆ F).Nonempty := symmDiff_nonempty.mpr hne
  let e := (E ∆ F).min' hd
  have hem : e ∈ E ∆ F := min'_mem _ hd
  have hefirst : ∀ j, j < e → (j ∈ E ↔ j ∈ F) := by
    intro j hj
    by_contra hiff
    have hjm : j ∈ E ∆ F := mem_symmDiff.mpr (by tauto)
    have hle := min'_le (E ∆ F) j hjm
    exact (not_le.mpr hj) hle
  have aux : ∀ (U V : Finset (Fin ℓ)), Grows w v U → Grows w v V →
      (∀ j, j < e → (j ∈ U ↔ j ∈ V)) → e ∈ U → e ∉ V →
      ¬ (Demand U (outgoing w (reached w v U)) x ∧
         Demand V (outgoing w (reached w v V)) x) := by
    intro U V hU hV hprev heU heV hx
    have hov : w.offset e.castSucc ∈ reached w v V := by
      rcases hU.2 e heU with hr | ⟨j,hj,hje,hjv⟩
      · simp [reached,hr]
      · exact mem_insert_of_mem (mem_image.mpr ⟨j,(hprev j hje).mp hj,hjv⟩)
    have h1 := hx.1 e (grows_outgoing w hU heU)
    have h2 := hx.2 e (mem_filter.mpr ⟨hU.1 heU,hov⟩)
    simp only [heU,decide_true] at h1
    simp only [heV,decide_false] at h2
    exact Bool.noConfusion (h1.symm.trans h2)
  rcases mem_symmDiff.mp hem with he | he
  · exact aux E F hE hF hefirst he.1 he.2
  · intro hx
    exact aux F E hF hE (fun j hj => (hefirst j hj).symm) he.1 he.2 ⟨hx.2,hx.1⟩

def shapes (w : ClosedLine h ℓ) (v : ℤ) : Finset (Finset (Fin ℓ)) :=
  w.treeSteps.powerset.filter (Grows w v)

lemma mem_shapes (w : ClosedLine h ℓ) (v : ℤ) (E : Finset (Fin ℓ)) :
    E ∈ shapes w v ↔ Grows w v E := by
  simp only [shapes,mem_filter,mem_powerset]
  exact and_iff_right_of_imp (fun h => h.1)

lemma empty_mem_shapes (w : ClosedLine h ℓ) (v : ℤ) : ∅ ∈ shapes w v := by
  rw [mem_shapes]
  simp [Grows]

lemma sum_demands_pointwise (w : ClosedLine h ℓ) (v : ℤ) (A β : ℝ)
    (hA : 0 ≤ A) (hβ : 0 ≤ β) (x : Fin ℓ → Bool) :
    (∑ E ∈ shapes w v, if Demand E (outgoing w (reached w v E)) x
      then bitWeight A β x else 0) ≤ bitWeight A β x := by
  by_cases hx : ∃ E ∈ shapes w v, Demand E (outgoing w (reached w v E)) x
  · obtain ⟨E,hE,hx⟩ := hx
    rw [sum_eq_single E]
    · simp [hx]
    · intro F hF hFE
      have hn : ¬ Demand F (outgoing w (reached w v F)) x := by
        intro hf
        exact grows_demands_disjoint w ((mem_shapes ..).mp hF) ((mem_shapes ..).mp hE)
          hFE x ⟨hf,hx⟩
      simp only [ite_eq_right hn]
    · exact fun hn => False.elim (hn hE)
  · have hn : ∀ E ∈ shapes w v, ¬ Demand E (outgoing w (reached w v E)) x := by
      simpa only [not_exists,not_and] using hx
    calc
      _ = 0 := sum_eq_zero (fun E hE => ite_eq_right (hn E hE))
      _ ≤ _ := bitWeight_nonneg A β hA hβ x

lemma sum_shape_weights (w : ClosedLine h ℓ) (v : ℤ) (A β : ℝ)
    (hA : 0 ≤ A) (hβ : 0 ≤ β) (hunit : β*(1+A)=1) :
    ∑ E ∈ shapes w v, A^E.card * β^(outgoing w (reached w v E)).card ≤ 1 := by
  calc
    _ = ∑ E ∈ shapes w v, ∑ x : Fin ℓ → Bool,
        if Demand E (outgoing w (reached w v E)) x then bitWeight A β x else 0 := by
      apply sum_congr rfl
      intro E hE
      exact (demand_weight A β hunit E _ (grows_outgoing w ((mem_shapes ..).mp hE))).symm
    _ = ∑ x : Fin ℓ → Bool, ∑ E ∈ shapes w v,
        if Demand E (outgoing w (reached w v E)) x then bitWeight A β x else 0 := sum_comm
    _ ≤ ∑ x : Fin ℓ → Bool, bitWeight A β x :=
      sum_le_sum (fun x _ => sum_demands_pointwise w v A β hA hβ x)
    _ = 1 := sum_bitWeight (ι := Fin ℓ) A β hunit

lemma outgoing_card (w : ClosedLine h ℓ) (V : Finset ℤ) :
    (outgoing w V).card = ∑ v ∈ V, w.children v := by
  simpa only [outgoing,ClosedLine.children] using
    (sum_card_fiberwise_eq_card_filter w.treeSteps V (fun e => w.offset e.castSucc)).symm

lemma reached_empty (w : ClosedLine h ℓ) (v : ℤ) : reached w v ∅ = {v} := by
  simp [reached]

lemma sum_nonempty_shape_weights (w : ClosedLine h ℓ) (v : ℤ) (A β : ℝ)
    (hA : 0 ≤ A) (hβ : 0 ≤ β) (hunit : β*(1+A)=1) :
    ∑ E ∈ (shapes w v).erase ∅, A^E.card * β^(outgoing w (reached w v E)).card ≤
      1 - β^(w.children v) := by
  rw [sum_erase_eq_sub (empty_mem_shapes w v)]
  have hz : (outgoing w (reached w v ∅)).card = w.children v := by
    rw [reached_empty,outgoing_card,sum_singleton]
  simp only [card_empty,pow_zero,one_mul,hz]
  exact sub_le_sub_right (sum_shape_weights w v A β hA hβ hunit) _

lemma grows_min_origin (w : ClosedLine h ℓ) {v : ℤ} {E : Finset (Fin ℓ)}
    (hE : Grows w v E) (hne : E.Nonempty) : w.offset (E.min' hne).castSucc = v := by
  rcases hE.2 (E.min' hne) (min'_mem E hne) with hr | ⟨j,hj,hjmin,hjv⟩
  · exact hr
  · exact False.elim ((not_lt_of_ge (min'_le E j hj)) hjmin)

lemma reached_eq_edgeVertices (w : ClosedLine h ℓ) {v : ℤ} {E : Finset (Fin ℓ)}
    (hE : Grows w v E) (hne : E.Nonempty) : reached w v E = edgeVertices w E := by
  ext u
  constructor
  · intro hu
    rcases mem_insert.mp hu with hroot | hd
    · subst u
      exact mem_union_left _ (mem_image.mpr ⟨E.min' hne,min'_mem E hne,grows_min_origin w hE hne⟩)
    · exact mem_union_right _ hd
  · intro hu
    rcases mem_union.mp hu with ho | hd
    · obtain ⟨e,he,rfl⟩ := mem_image.mp ho
      exact grows_edge_origins w hE he
    · exact mem_insert_of_mem hd

theorem numerical_subtree_sum_le (w : ClosedLine h ℓ) (A β : ℝ)
    (hA : 0 ≤ A) (hβ : 0 ≤ β) (hunit : β*(1+A)=1) :
    (∑ v ∈ treeVertices w, ∑ E ∈ (shapes w v).erase ∅,
      A^E.card * ∏ u ∈ edgeVertices w E, β^(w.children u)) ≤ bandDefect w β := by
  unfold bandDefect
  apply sum_le_sum
  intro v hv
  have heq : (∑ E ∈ (shapes w v).erase ∅,
      A^E.card * ∏ u ∈ edgeVertices w E, β^(w.children u)) =
      ∑ E ∈ (shapes w v).erase ∅, A^E.card * β^(outgoing w (reached w v E)).card := by
    apply sum_congr rfl
    intro E hE
    obtain ⟨hne,hg⟩ := mem_erase.mp hE
    rw [outgoing_card,reached_eq_edgeVertices w ((mem_shapes ..).mp hg)
      (nonempty_iff_ne_empty.mpr hne),prod_pow_eq_pow_sum]
  rw [heq]
  exact sum_nonempty_shape_weights w v A β hA hβ hunit

end OrdinaryCorrelations.NumericalSubtrees

end

end OAI
