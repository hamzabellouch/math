import OAI.Combinatorics.PlanarL1.Fields

namespace OAI

section

namespace PlanarL1.Columns.Model

/-- One label of a nested-set system. Nesting and exact switching are the
set invariants, not any embedding or separation assumption. -/
structure Activity {n : ℕ} (M : Model n) where
  active : Fin n → ℝ → Prop
  increasing : ∀ i s t, s ≤ t → active i s → active i t
  switch : ∀ i j H, H ∈ M.heights i j → (active i H ↔ active j H)

namespace Activity

attribute [local instance] Classical.propDecidable

variable {n : ℕ} {M : Model n} (A : Activity M)

def graph : SimpleGraph (Fin n) where
  Adj i j := ∃ H, H ∈ M.heights i j ∧ A.active i H
  symm := ⟨by
    rintro i j ⟨H,hH,hA⟩
    exact ⟨H,by rwa [M.symm i j] at hH,(A.switch i j H hH).mp hA⟩⟩
  loopless := ⟨by
    rintro i ⟨H,hH,_⟩
    exact M.link.loopless.irrefl i (M.permitted i i H hH)⟩

lemma graph_le : A.graph ≤ M.link := by
  rintro i j ⟨H,hH,_⟩
  exact M.permitted i j H hH

def component (i : Fin n) : Set (Fin n) := {k | A.graph.Reachable i k}

lemma mem_component_self (i : Fin n) : i ∈ A.component i := .refl i

lemma component_eq_iff (i j : Fin n) : A.component i = A.component j ↔ A.graph.Reachable i j := by
  constructor
  · intro h
    change j ∈ A.component i
    rw [h]
    exact A.mem_component_self j
  · intro h
    ext k
    exact ⟨fun hik => h.symm.trans hik,fun hjk => h.trans hjk⟩

/-- Active points get a single component coordinate; inactive points get zero.
The finite coordinate set consists of all subsets of columns. -/
noncomputable def vector (i : Fin n) (H : ℝ) (S : Set (Fin n)) : ℝ :=
  if A.active i H ∧ S = A.component i then 1 else 0

noncomputable def indicator (i : Fin n) (H : ℝ) : ℝ := if A.active i H then 1 else 0

noncomputable def cost (i j : Fin n) (s t : ℝ) : ℝ :=
  ∑ S : Set (Fin n), |A.vector i s S - A.vector j t S|

lemma cost_nonneg (i j : Fin n) (s t : ℝ) : 0 ≤ A.cost i j s t := by
  unfold cost
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma vector_inactive {i : Fin n} {H : ℝ} (h : ¬ A.active i H) : A.vector i H = 0 := by
  funext S
  simp only [vector,h,false_and,ite_false,Pi.zero_apply]

lemma vector_active {i : Fin n} {H : ℝ} (h : A.active i H) (S : Set (Fin n)) :
    A.vector i H S = if S = A.component i then 1 else 0 := by
  simp only [vector,h,true_and]

lemma cost_comm (i j : Fin n) (s t : ℝ) : A.cost i j s t = A.cost j i t s := by
  unfold cost
  apply Finset.sum_congr rfl
  intro S _
  exact abs_sub_comm _ _

lemma sum_vector (i : Fin n) (H : ℝ) :
    ∑ S : Set (Fin n), A.vector i H S = A.indicator i H := by
  classical
  by_cases h : A.active i H
  · simp only [A.vector_active h, indicator,h,ite_true]
    simp
  · rw [A.vector_inactive h]
    simp only [Pi.zero_apply,Finset.sum_const_zero,indicator,h,ite_false]

lemma vector_nonneg (i : Fin n) (H : ℝ) (S : Set (Fin n)) : 0 ≤ A.vector i H S := by
  unfold vector
  split <;> norm_num

lemma dominates_indicator (i j : Fin n) (s t : ℝ) :
    |A.indicator i s-A.indicator j t| ≤ A.cost i j s t := by
  rw [← A.sum_vector i s,← A.sum_vector j t,← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

lemma cost_triangle (i j k : Fin n) (s t u : ℝ) :
    A.cost i k s u ≤ A.cost i j s t+A.cost j k t u := by
  unfold cost
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun S _ => abs_sub_le _ _ _

lemma cost_vertical (i : Fin n) (s t : ℝ) :
    A.cost i i s t = |A.indicator i s-A.indicator i t| := by
  classical
  by_cases hs : A.active i s <;> by_cases ht : A.active i t
  · simp only [cost,A.vector_active hs,A.vector_active ht,sub_self,abs_zero,
      Finset.sum_const_zero,indicator,hs,ht,ite_true]
  · simp only [cost,A.vector_active hs,A.vector_inactive ht,Pi.zero_apply,sub_zero,
      indicator,hs,ht,ite_true,ite_false]
    simp only [apply_ite abs,abs_one,abs_zero]
    simp
  · rw [A.cost_comm]
    simp only [cost,A.vector_active ht,A.vector_inactive hs,Pi.zero_apply,sub_zero,
      indicator,hs,ht,ite_true,ite_false]
    simp only [apply_ite abs,abs_one,abs_zero]
    simp
  · simp only [cost,A.vector_inactive hs,A.vector_inactive ht,Pi.zero_apply,sub_self,
      abs_zero,Finset.sum_const_zero,indicator,hs,ht,ite_false]

lemma vector_switch {i j : Fin n} {H : ℝ} (hH : H ∈ M.heights i j) :
    A.vector i H = A.vector j H := by
  classical
  by_cases hi : A.active i H
  · have hj := (A.switch i j H hH).mp hi
    have he := (A.component_eq_iff i j).mpr (SimpleGraph.Adj.reachable ⟨H,hH,hi⟩)
    funext S
    simp only [A.vector_active hi,A.vector_active hj,he]
  · rw [A.vector_inactive hi,A.vector_inactive (fun h => hi ((A.switch i j H hH).mpr h))]

lemma cost_switch {i j : Fin n} {H : ℝ} (hH : H ∈ M.heights i j) : A.cost i j H H = 0 := by
  simp only [cost,A.vector_switch hH,sub_self,abs_zero,Finset.sum_const_zero]

lemma cost_of_active_distinct {i j : Fin n} {s t : ℝ}
    (hi : A.active i s) (hj : A.active j t) (hne : A.component i ≠ A.component j) :
    A.cost i j s t = 2 := by
  classical
  have hr : ∀ S : Set (Fin n), |A.vector i s S-A.vector j t S| =
      (if S = A.component i then 1 else 0)+(if S = A.component j then 1 else 0) := by
    intro S
    rw [A.vector_active hi,A.vector_active hj]
    by_cases h₁ : S = A.component i <;> by_cases h₂ : S = A.component j
    · exact False.elim (hne (h₁.symm.trans h₂))
    · simp only [ite_eq_left h₁,ite_eq_right h₂]; norm_num
    · simp only [ite_eq_right h₁,ite_eq_left h₂]; norm_num
    · simp only [ite_eq_right h₁,ite_eq_right h₂]; norm_num
  simp only [cost,hr,Finset.sum_add_distrib]
  norm_num

/-- An inactive terminal tip isolates BOTH of its endpoint columns in the
active-link graph. This uses the terminal-switch standing hypothesis. -/
lemma terminal_isolated {a b : Fin n} {H : ℝ}
    (hH : H ∈ M.heights a b) (hn : ¬ Consecutive a b) (hA : ¬ A.active a H) :
    (∀ k, ¬ A.graph.Adj a k) ∧ (∀ k, ¬ A.graph.Adj b k) := by
  obtain ⟨T,hT,ht⟩ := M.terminal a b (M.permitted a b H hH) hn
  have he : H = T := by simpa only [hT,Set.mem_singleton_iff] using hH
  subst T
  constructor
  · rintro k ⟨U,hU,hu⟩
    exact hA (A.increasing a U H (ht k U (Or.inl hU)) hu)
  · rintro k ⟨U,hU,hu⟩
    exact hA ((A.switch a b H hH).mpr (A.increasing b U H (ht k U (Or.inr hU)) hu))

lemma separated_components {a b x y : Fin n} {H : ℝ}
    (hH : H ∈ M.heights a b) (hn : ¬ Consecutive a b) (hA : ¬ A.active a H)
    (hx : a < x ∧ x < b) (hy : y < a ∨ b < y) : A.component x ≠ A.component y := by
  intro he
  obtain ⟨p⟩ := (A.component_eq_iff x y).mp he
  have hxy : x ≠ y := by omega
  have hp := SimpleGraph.Walk.not_nil_of_ne (p := p) hxy
  obtain ⟨ha,hb⟩ := A.terminal_isolated hH hn hA
  have hsep := ColumnOrder.chord_separation M.noncrossing (M.permitted a b H hH)
    (p.mapLe A.graph_le) hx hy
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hsep
  rcases hsep with hsep | hsep
  · obtain ⟨k,_,hk⟩ := SimpleGraph.adj_of_mem_walk_support p hp hsep
    exact ha k hk
  · obtain ⟨k,_,hk⟩ := SimpleGraph.adj_of_mem_walk_support p hp hsep
    exact hb k hk

/-- Exact labelwise component-certificate separation (sets:component-refinement).
The other switches may change arbitrarily, subject only to the invariants. -/
lemma terminal_certificate {a b x y : Fin n} {H s t : ℝ}
    (hH : H ∈ M.heights a b) (hn : ¬ Consecutive a b) (hA : ¬ A.active a H)
    (hx : a < x ∧ x < b) (hy : y < a ∨ b < y)
    (hs : A.active x s) (ht : A.active y t) : A.cost x y s t = 2 :=
  A.cost_of_active_distinct hs ht (A.separated_components hH hn hA hx hy)

/-- The unrefined costs of the vertical pieces of an ACTUAL permitted path. -/
noncomputable def pathCost {J : Set ℝ} : {i j : Fin n} → M.Path J i j → ℝ → ℝ → ℝ
  | _, _, .nil i, s, t => |A.indicator i s-A.indicator i t|
  | i, _, .cons H _ _ p, s, t => |A.indicator i s-A.indicator i H|+pathCost p H t

lemma cost_le_pathCost {J : Set ℝ} {i j : Fin n} (p : M.Path J i j) (s t : ℝ) :
    A.cost i j s t ≤ A.pathCost p s t := by
  induction p generalizing s with
  | nil => exact le_of_eq (A.cost_vertical _ _ _)
  | @cons i k j H hH hs p ih =>
    have h₁ := A.cost_triangle i k j H H t
    rw [A.cost_switch hs,zero_add] at h₁
    have h₂ := A.cost_triangle i i j s H t
    rw [A.cost_vertical] at h₂
    change A.cost i j s t ≤ |A.indicator i s-A.indicator i H|+A.pathCost p H t
    linarith [ih H]

end Activity
end PlanarL1.Columns.Model

namespace PlanarL1.Columns.Model
open MeasureTheory

/-- The exact hypotheses in the component-refinement lemma, put on an actual
measure space. The vertical bound is the invariant of the cut construction. -/
structure SetSystem {n : ℕ} (M : Model n) (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) where
  activity : Ω → Activity M
  measurable_active : ∀ i H, MeasurableSet {ω | (activity ω).active i H}
  vertical_integrable : ∀ i s t,
    Integrable (fun ω => |(activity ω).indicator i s-(activity ω).indicator i t|) μ
  vertical_bound : ∀ i s t,
    (∫ ω, |(activity ω).indicator i s-(activity ω).indicator i t| ∂μ) ≤ |s-t|

namespace SetSystem
variable {n : ℕ} {M : Model n} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} (A : SetSystem M Ω μ)

lemma measurable_indicator (i : Fin n) (H : ℝ) :
    Measurable (fun ω => (A.activity ω).indicator i H) := by
  exact Measurable.ite (A.measurable_active i H) measurable_const measurable_const

/-- Compactness and monotonicity reduce active-link measurability to ONE fixed
height. There is no uncountable union of switching events. -/
lemma measurable_adj (i j : Fin n) :
    MeasurableSet {ω | (A.activity ω).graph.Adj i j} := by
  by_cases h : (M.heights i j).Nonempty
  · obtain ⟨H,hH,hmax⟩ := (M.compact i j).exists_isGreatest h
    have he : {ω | (A.activity ω).graph.Adj i j} =
        {ω | (A.activity ω).active i H} := by
      ext ω
      constructor
      · rintro ⟨T,hT,ha⟩
        exact (A.activity ω).increasing i T H (hmax hT) ha
      · intro ha
        exact ⟨H,hH,ha⟩
    rw [he]
    exact A.measurable_active i H
  · have he : {ω | (A.activity ω).graph.Adj i j} = ∅ := by
      ext ω
      constructor
      · rintro ⟨H,hH,_⟩
        exact h ⟨H,hH⟩
      · exact False.elim
    rw [he]
    exact MeasurableSet.empty

lemma measurable_graph_fiber (G : SimpleGraph (Fin n)) :
    MeasurableSet {ω | (A.activity ω).graph = G} := by
  have he : {ω | (A.activity ω).graph = G} =
      ⋂ i, ⋂ j, {ω | (A.activity ω).graph.Adj i j ↔ G.Adj i j} := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iInter]
    constructor
    · intro h; rw [h]; exact fun _ _ => Iff.rfl
    · intro h; exact SimpleGraph.ext (funext fun i => funext fun j => propext (h i j))
  rw [he]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  by_cases h : G.Adj i j
  · simpa only [h,iff_true] using A.measurable_adj i j
  · simpa only [h,iff_false,Set.compl_ofPred] using (A.measurable_adj i j).compl

lemma measurable_component (i : Fin n) (S : Set (Fin n)) :
    MeasurableSet {ω | (A.activity ω).component i = S} := by
  let : MeasurableSpace (SimpleGraph (Fin n)) := ⊤
  have hm : Measurable (fun ω => (A.activity ω).graph) :=
    measurable_to_countable' (A.measurable_graph_fiber)
  exact hm (t := {G | {k | G.Reachable i k} = S}) trivial

lemma measurable_vector (i : Fin n) (H : ℝ) (S : Set (Fin n)) :
    Measurable (fun ω => (A.activity ω).vector i H S) := by
  have hh : MeasurableSet {ω | S = (A.activity ω).component i} := by
    simpa only [eq_comm] using A.measurable_component i S
  exact Measurable.ite ((A.measurable_active i H).inter hh)
    measurable_const measurable_const

lemma measurable_cost (i j : Fin n) (s t : ℝ) :
    Measurable (fun ω => (A.activity ω).cost i j s t) := by
  classical
  exact Finset.measurable_sum _ fun S _ =>
    ((A.measurable_vector i s S).sub (A.measurable_vector j t S)).abs

lemma pathCost_integrable {J : Set ℝ} {i j : Fin n} (p : M.Path J i j) (s t : ℝ) :
    Integrable (fun ω => (A.activity ω).pathCost p s t) μ := by
  induction p generalizing s with
  | nil => exact A.vertical_integrable _ _ _
  | cons H _ _ p ih => exact (A.vertical_integrable _ _ _).add (ih H)

lemma integral_pathCost_le {J : Set ℝ} {i j : Fin n} (p : M.Path J i j) (s t : ℝ) :
    (∫ ω, (A.activity ω).pathCost p s t ∂μ) ≤ p.length s t := by
  induction p generalizing s with
  | nil => exact A.vertical_bound _ _ _
  | @cons i k j H _ _ p ih =>
    change (∫ ω, |(A.activity ω).indicator i s-(A.activity ω).indicator i H|+
      (A.activity ω).pathCost p H t ∂μ) ≤ |s-H|+p.length H t
    rw [integral_add (A.vertical_integrable i s H) (A.pathCost_integrable p H t)]
    exact add_le_add (A.vertical_bound i s H) (ih H)

lemma cost_integrable {J : Set ℝ} {i j : Fin n} (p : M.Path J i j) (s t : ℝ) :
    Integrable (fun ω => (A.activity ω).cost i j s t) μ := by
  apply (A.pathCost_integrable p s t).mono' (A.measurable_cost i j s t).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg ((A.activity ω).cost_nonneg i j s t)]
    exact (A.activity ω).cost_le_pathCost p s t

lemma integral_cost_le_length {J : Set ℝ} {i j : Fin n} (p : M.Path J i j) (s t : ℝ) :
    (∫ ω, (A.activity ω).cost i j s t ∂μ) ≤ p.length s t := by
  apply le_trans _ (A.integral_pathCost_le p s t)
  exact integral_mono (A.cost_integrable p s t) (A.pathCost_integrable p s t)
    (fun ω => (A.activity ω).cost_le_pathCost p s t)

lemma integral_cost_le_dist {J : Set ℝ} {root : Fin n} (hJ : IsClosed J)
    (x y : M.Point J root) :
    (∫ ω, (A.activity ω).cost x.column y.column x.height y.height ∂μ) ≤ dist x y := by
  obtain ⟨p,_,hp⟩ := x.exists_shortest hJ y
  exact (A.integral_cost_le_length p x.height y.height).trans_eq hp

/-- Finitely many coordinates, with the discrete sigma algebra. -/
local instance componentMeasurableSpace : MeasurableSpace (Set (Fin n)) := ⊤

noncomputable def coordinateDifference (i j : Fin n) (s t : ℝ)
    (z : Ω × Set (Fin n)) : ℝ :=
  (A.activity z.1).vector i s z.2-(A.activity z.1).vector j t z.2

lemma measurable_coordinateDifference (i j : Fin n) (s t : ℝ) :
    Measurable (A.coordinateDifference i j s t) := by
  apply measurable_from_prod_countable_left
  intro S
  exact (A.measurable_vector i s S).sub (A.measurable_vector j t S)

lemma integrable_coordinateDifference {J : Set ℝ} {i j : Fin n}
    (p : M.Path J i j) (s t : ℝ) :
    Integrable (A.coordinateDifference i j s t) (μ.prod Measure.count) := by
  classical
  apply (integrable_prod_iff (A.measurable_coordinateDifference i j s t).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun ω =>
      memLp_one_iff_integrable.mp MemLp.of_discrete
  · have he : (fun ω => ∫ S, ‖A.coordinateDifference i j s t (ω,S)‖ ∂Measure.count) =
        (fun ω => (A.activity ω).cost i j s t) := by
      funext ω
      rw [integral_count]
      simp only [coordinateDifference,Real.norm_eq_abs,Activity.cost]
    rw [he]
    exact A.cost_integrable p s t

variable [SFinite μ]

lemma integral_norm_coordinates {J : Set ℝ} {i j : Fin n}
    (p : M.Path J i j) (s t : ℝ) :
    (∫ z, ‖A.coordinateDifference i j s t z‖ ∂μ.prod Measure.count) =
      ∫ ω, (A.activity ω).cost i j s t ∂μ := by
  rw [integral_prod _ (A.integrable_coordinateDifference p s t).norm]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => by
    dsimp only
    rw [integral_count]
    simp only [coordinateDifference,Real.norm_eq_abs,Activity.cost]

/-- Subtracting the actual reference point makes the component assignment
integrable, even when the original label measure is infinite. -/
noncomputable def refinedMap {J : Set ℝ} {root : Fin n} (o x : M.Point J root) :
    Lp ℝ 1 (μ.prod (Measure.count : Measure (Set (Fin n)))) :=
  (A.integrable_coordinateDifference (Classical.choice (x.paths_nonempty o)) x.height o.height).toL1
    (A.coordinateDifference x.column o.column x.height o.height)

lemma norm_refinedMap_sub {J : Set ℝ} {root : Fin n} (o x y : M.Point J root) :
    ‖A.refinedMap o x-A.refinedMap o y‖ =
      ∫ ω, (A.activity ω).cost x.column y.column x.height y.height ∂μ := by
  rw [L1.norm_eq_integral_norm]
  calc
    (∫ z, ‖(A.refinedMap o x-A.refinedMap o y) z‖ ∂μ.prod Measure.count) =
        ∫ z, ‖A.coordinateDifference x.column y.column x.height y.height z‖ ∂μ.prod Measure.count := by
      apply integral_congr_ae
      have hx := (A.integrable_coordinateDifference (Classical.choice (x.paths_nonempty o))
        x.height o.height).coeFn_toL1
      have hy := (A.integrable_coordinateDifference (Classical.choice (y.paths_nonempty o))
        y.height o.height).coeFn_toL1
      filter_upwards [Lp.coeFn_sub (A.refinedMap o x) (A.refinedMap o y),hx,hy] with z hz hx hy
      change (A.refinedMap o x) z = _ at hx
      change (A.refinedMap o y) z = _ at hy
      rw [hz,Pi.sub_apply,hx,hy]
      congr 1
      simp only [coordinateDifference]
      ring
    _ = _ := A.integral_norm_coordinates (Classical.choice (x.paths_nonempty y)) x.height y.height

lemma refinedMap_lipschitz {J : Set ℝ} {root : Fin n} (hJ : IsClosed J)
    (o x y : M.Point J root) : ‖A.refinedMap o x-A.refinedMap o y‖ ≤ dist x y := by
  rw [A.norm_refinedMap_sub]
  exact A.integral_cost_le_dist hJ x y

omit [SFinite μ] in
lemma unrefined_integrable {J : Set ℝ} {i j : Fin n}
    (p : M.Path J i j) (s t : ℝ) :
    Integrable (fun ω => |(A.activity ω).indicator i s-(A.activity ω).indicator j t|) μ := by
  apply (A.cost_integrable p s t).mono' (((A.measurable_indicator i s).sub
    (A.measurable_indicator j t)).abs.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs,abs_abs]
    exact (A.activity ω).dominates_indicator i j s t

lemma refinedMap_dominates {J : Set ℝ} {root : Fin n} (o x y : M.Point J root) :
    (∫ ω, |(A.activity ω).indicator x.column x.height-
      (A.activity ω).indicator y.column y.height| ∂μ) ≤
      ‖A.refinedMap o x-A.refinedMap o y‖ := by
  rw [A.norm_refinedMap_sub]
  let p := Classical.choice (x.paths_nonempty y)
  exact integral_mono (A.unrefined_integrable p x.height y.height)
    (A.cost_integrable p x.height y.height)
    (fun ω => (A.activity ω).dominates_indicator _ _ _ _)

/-- The actual final certificate yields twice its label mass in the refined
real L1 map. Its mass is necessarily finite, although μ itself is infinite. -/
lemma refinedMap_terminal_certificate {J : Set ℝ} {root : Fin n} (o x y : M.Point J root)
    {a b : Fin n} {H : ℝ} (hH : H ∈ M.heights a b) (hn : ¬ Consecutive a b)
    (hx : a < x.column ∧ x.column < b) (hy : y.column < a ∨ b < y.column)
    (E : Set Ω) (hE : MeasurableSet E)
    (hA : ∀ ω ∈ E, ¬ (A.activity ω).active a H)
    (hX : ∀ ω ∈ E, (A.activity ω).active x.column x.height)
    (hY : ∀ ω ∈ E, (A.activity ω).active y.column y.height) :
    μ E < ⊤ ∧ 2*μ.real E ≤ ‖A.refinedMap o x-A.refinedMap o y‖ := by
  classical
  have hbnd : ∀ ω, ‖E.indicator (fun _ => (2:ℝ)) ω‖ ≤
      (A.activity ω).cost x.column y.column x.height y.height := by
    intro ω
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω,
        (A.activity ω).terminal_certificate hH hn (hA ω hω) hx hy (hX ω hω) (hY ω hω)]
      norm_num
    · rw [Set.indicator_of_notMem hω,norm_zero]
      exact (A.activity ω).cost_nonneg _ _ _ _
  have hi : Integrable (E.indicator (fun _ => (2:ℝ))) μ :=
    (A.cost_integrable (Classical.choice (x.paths_nonempty y)) x.height y.height).mono'
      (measurable_const.indicator hE).aestronglyMeasurable (Filter.Eventually.of_forall hbnd)
  constructor
  · have ht := (integrableOn_const_iff (C := (2:ℝ))).mp
      ((integrable_indicator_iff hE).mp hi)
    simpa using ht
  · rw [A.norm_refinedMap_sub]
    calc
      2*μ.real E = ∫ ω, E.indicator (fun _ => (2:ℝ)) ω ∂μ := by
        rw [integral_indicator_const _ hE,smul_eq_mul,mul_comm]
      _ ≤ _ := integral_mono hi
        (A.cost_integrable (Classical.choice (x.paths_nonempty y)) x.height y.height)
        (fun ω => (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hbnd ω))

end SetSystem
end PlanarL1.Columns.Model



end

section

namespace PlanarL1.Columns.Model
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace Activity
variable {n : ℕ} {M : Model n}

/-- Pointwise membership movement; component labels are deliberately not moved. -/
noncomputable def movement (A B : Activity M) (i : Fin n) (H : ℝ) : ℝ :=
  |B.indicator i H-A.indicator i H|

lemma movement_nonneg (A B : Activity M) (i : Fin n) (H : ℝ) : 0 ≤ A.movement B i H :=
  abs_nonneg _

lemma terminal_survival (A B : Activity M) {a b x y : Fin n} {H s t : ℝ}
    (hH : H ∈ M.heights a b) (hn : ¬ Consecutive a b)
    (hx : a<x ∧ x<b) (hy : y<a ∨ b<y)
    (ha : ¬ A.active a H) (hax : A.active x s) (hay : A.active y t) :
    2 ≤ B.cost x y s t+2*(A.movement B x s+A.movement B y t+A.movement B a H) := by
  by_cases hba : B.active a H
  · have hm : A.movement B a H=1 := by simp [movement,indicator,ha,hba]
    have h1 := A.movement_nonneg B x s
    have h2 := A.movement_nonneg B y t
    have h3 := B.cost_nonneg x y s t
    linarith
  by_cases hbx : B.active x s
  · by_cases hby : B.active y t
    · rw [B.terminal_certificate hH hn hba hx hy hbx hby]
      linarith [A.movement_nonneg B x s,A.movement_nonneg B y t,A.movement_nonneg B a H]
    · have hm : A.movement B y t=1 := by simp [movement,indicator,hay,hby]
      linarith [A.movement_nonneg B x s,A.movement_nonneg B a H,B.cost_nonneg x y s t]
  · have hm : A.movement B x s=1 := by simp [movement,indicator,hax,hbx]
    linarith [A.movement_nonneg B y t,A.movement_nonneg B a H,B.cost_nonneg x y s t]

end Activity
namespace SetSystem
variable {n : ℕ} {M : Model n} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A B : SetSystem M Ω μ)

noncomputable def movement (i : Fin n) (H : ℝ) : ℝ :=
  ∫ ω, (A.activity ω).movement (B.activity ω) i H ∂μ

lemma movement_nonneg (i : Fin n) (H : ℝ) : 0 ≤ A.movement B i H :=
  integral_nonneg (fun ω => (A.activity ω).movement_nonneg (B.activity ω) i H)

lemma movement_triangle (C : SetSystem M Ω μ) (i : Fin n) (H : ℝ)
    (hab : Integrable (fun ω => (B.activity ω).indicator i H-(A.activity ω).indicator i H) μ)
    (hbc : Integrable (fun ω => (C.activity ω).indicator i H-(B.activity ω).indicator i H) μ) :
    A.movement C i H ≤ A.movement B i H+B.movement C i H := by
  have hac : Integrable (fun ω => (C.activity ω).indicator i H-(A.activity ω).indicator i H) μ := by
    have he : (fun ω => (C.activity ω).indicator i H-(A.activity ω).indicator i H) =
        (fun ω => ((C.activity ω).indicator i H-(B.activity ω).indicator i H)+
          ((B.activity ω).indicator i H-(A.activity ω).indicator i H)) := by
      funext ω
      ring
    rw [he]
    exact hbc.add hab
  change (∫ ω, |(C.activity ω).indicator i H-(A.activity ω).indicator i H| ∂μ) ≤ _
  calc
    _ ≤ ∫ ω, |(B.activity ω).indicator i H-(A.activity ω).indicator i H|+
        |(C.activity ω).indicator i H-(B.activity ω).indicator i H| ∂μ := by
      apply integral_mono hac.abs
        (hab.abs.add hbc.abs)
      intro ω
      simpa only [Pi.add_apply,add_comm] using abs_sub_le ((C.activity ω).indicator i H)
        ((B.activity ω).indicator i H) ((A.activity ω).indicator i H)
    _ = _ := integral_add hab.abs
      hbc.abs

/-- Survival of the source's component certificate after arbitrary later
unrefined movements at the two vertices and the fixed bridge tip. No estimate
on changes of active-component labels is used or assumed. -/
lemma refined_certificate_survival [SFinite μ] {J : Set ℝ} {root : Fin n} (o x y : M.Point J root)
    {a b : Fin n} {H : ℝ} (hH : H ∈ M.heights a b) (hn : ¬ Consecutive a b)
    (hx : a<x.column ∧ x.column<b) (hy : y.column<a ∨ b<y.column)
    (E : Set Ω) (hE : MeasurableSet E)
    (ha : ∀ ω ∈ E, ¬ (A.activity ω).active a H)
    (hax : ∀ ω ∈ E, (A.activity ω).active x.column x.height)
    (hay : ∀ ω ∈ E, (A.activity ω).active y.column y.height)
    (hmove : ∀ i H, Integrable (fun ω => (B.activity ω).indicator i H-
      (A.activity ω).indicator i H) μ) :
    2*μ.real E ≤ ‖B.refinedMap o x-B.refinedMap o y‖+
      2*(A.movement B x.column x.height+A.movement B y.column y.height+A.movement B a H) := by
  have hfin := (A.refinedMap_terminal_certificate o x y hH hn hx hy E hE ha hax hay).1
  have hEI : Integrable (E.indicator (fun _ => (2:ℝ))) μ := by
    apply (integrable_indicator_iff hE).mpr
    exact (integrableOn_const_iff (C := (2:ℝ))).mpr (Or.inr hfin)
  have hmI (i : Fin n) (z : ℝ) : Integrable (fun ω =>
      (A.activity ω).movement (B.activity ω) i z) μ := by
    simpa only [Activity.movement,Real.norm_eq_abs] using (hmove i z).norm
  have hxI := hmI x.column x.height
  have hyI := hmI y.column y.height
  have haI := hmI a H
  let p := Classical.choice (x.paths_nonempty y)
  have hcost := B.cost_integrable p x.height y.height
  have hg := integral_mono hEI (hcost.add (((hxI.add hyI).add haI).const_mul 2))
    (fun ω => show E.indicator (fun _ => (2:ℝ)) ω ≤
      (B.activity ω).cost x.column y.column x.height y.height+
      2*((A.activity ω).movement (B.activity ω) x.column x.height+
        (A.activity ω).movement (B.activity ω) y.column y.height+
        (A.activity ω).movement (B.activity ω) a H) by
      by_cases he : ω ∈ E
      · rw [Set.indicator_of_mem he]
        exact (A.activity ω).terminal_survival (B.activity ω) hH hn hx hy
          (ha ω he) (hax ω he) (hay ω he)
      · rw [Set.indicator_of_notMem he]
        linarith [(B.activity ω).cost_nonneg x.column y.column x.height y.height,
          (A.activity ω).movement_nonneg (B.activity ω) x.column x.height,
          (A.activity ω).movement_nonneg (B.activity ω) y.column y.height,
          (A.activity ω).movement_nonneg (B.activity ω) a H])
  rw [integral_indicator_const _ hE,smul_eq_mul,mul_comm] at hg
  rw [B.norm_refinedMap_sub]
  change _ ≤ _+2*((∫ ω, |(B.activity ω).indicator x.column x.height-
      (A.activity ω).indicator x.column x.height| ∂μ)+
    (∫ ω, |(B.activity ω).indicator y.column y.height-
      (A.activity ω).indicator y.column y.height| ∂μ)+
    (∫ ω, |(B.activity ω).indicator a H-(A.activity ω).indicator a H| ∂μ))
  dsimp only [Pi.add_apply] at hg
  have e1 := integral_add hcost (((hxI.add hyI).add haI).const_mul 2)
  have e2 := integral_add (hxI.add hyI) haI
  have e3 := integral_add hxI hyI
  simp only [Pi.add_apply] at e1 e2 e3
  rw [e1,integral_const_mul,e2,e3] at hg
  exact hg

end SetSystem
end PlanarL1.Columns.Model



end

end OAI
