import OAI.Probability.SATVariance.IsolatedSupports

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma mem_take_ofFn.{u_1} {α : Type u_1} {M m : ℕ} (w : Fin M → α) (c : α) :
    c ∈ (List.ofFn w).take m ↔ ∃ i : Fin M, i.val < m ∧ w i = c := by
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨j,hj,he⟩
    have hj' : j < min m M := by simpa only [List.length_ofFn] using hj
    refine ⟨⟨j,lt_of_lt_of_le hj' (min_le_right _ _)⟩,lt_of_lt_of_le hj' (min_le_left _ _),?_⟩
    simpa only [List.getElem_ofFn] using he
  · rintro ⟨i,hi,he⟩
    refine ⟨i.val,?_,?_⟩
    · simpa only [List.length_ofFn,lt_min_iff] using And.intro hi i.isLt
    · simpa only [List.getElem_ofFn] using he

lemma listSAT_take_ofFn {n k M m : ℕ} (w : Fin M → Clause n k) :
    listSAT ((List.ofFn w).take m) ↔ finiteSAT w m := by
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,fun i hi => ha (w i) ((mem_take_ofFn w _).mpr ⟨i,hi,rfl⟩)⟩
  · rintro ⟨a,ha⟩
    refine ⟨a,fun c hc => ?_⟩
    obtain ⟨i,hi,rfl⟩ := (mem_take_ofFn w c).mp hc
    exact ha i hi

lemma lt_listStop_ofFn_iff {n k M m : ℕ} (w : Fin M → Clause n k) (hm : m ≤ M) :
    m < listStop (List.ofFn w) ↔ finiteSAT w m := by
  rw [lt_listStop_iff,List.length_ofFn,and_iff_right hm,listSAT_take_ofFn]

lemma listStop_eq_finiteTime {n k M : ℕ} (w : Fin M → Clause n k) :
    (listStop (List.ofFn w):ℝ) = finiteTime w + if finiteSAT w M then 1 else 0 := by
  have hs : listStop (List.ofFn w) ≤ M+1 := by simpa only [List.length_ofFn] using listStop_le (List.ofFn w)
  have hh (i : Fin (M+1)) : i.val < listStop (List.ofFn w) ↔ finiteSAT w i.val :=
    lt_listStop_ofFn_iff w (by omega)
  rw [← sum_fin_indicator_lt hs]
  simp only [hh]
  rw [Fin.sum_univ_castSucc]
  rfl

lemma sentinel_error {n k M : ℕ} (w : Fin M → Clause n k) :
    ((listStop (List.ofFn w):ℝ)-finiteTime w)^2 ≤ 1 := by
  rw [listStop_eq_finiteTime]
  split_ifs <;> norm_num

lemma fvariance_bridge.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (f g : α → ℝ) :
    fvariance f ≤ 2*fvariance g+2*favg (fun a => (f a-g a)^2) := by
  apply (fvariance_le_sq_sub f (favg g)).trans
  have hh := favg_mono (fun a : α => show (f a-favg g)^2 ≤ 2*(g a-favg g)^2+2*(f a-g a)^2 by
    nlinarith [sq_nonneg ((g a-favg g)-(f a-g a))])
  rw [favg_add,favg_mul,favg_mul,←fvariance_centered] at hh
  exact hh

lemma sentinel_variance_bridge {n k M : ℕ} [Nonempty (Clause n k)] :
    fvariance (fun w : Fin M → Clause n k => (listStop (List.ofFn w):ℝ)) ≤
      2*fvariance (finiteTime (n := n) (k := k) (L := M))+2 := by
  apply (fvariance_bridge _ _).trans
  have hh := favg_mono (fun w : Fin M → Clause n k => sentinel_error w)
  rw [favg_const] at hh
  linarith

end RandomKSAT

end

end OAI
