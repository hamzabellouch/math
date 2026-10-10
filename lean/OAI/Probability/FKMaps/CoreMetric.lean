import OAI.Probability.FKMaps.MarkedBounds

namespace OAI

noncomputable section
open List Equiv Equiv.Perm MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace FKCRT.Inventory
open MapCycles PermutationWedge TreeCoding
attribute [local instance] Classical.propDecidable

namespace Core

def matching (c : Core) : StackMatching c.val.get (List.finRange c.val.length) :=
  StackMatching.ofEmpty (by
    rw [List.map_get_finRange]
    exact coreWord_empty _ c.property)

def rotation (c : Core) : Perm (Fin c.val.length) :=
  (List.finRange c.val.length).formPerm*turns c.matching.first

def graph (c : Core) : SimpleGraph (PermutationWedge.Vertex c.rotation) :=
  dartGraph c.matching.mate c.rotation

instance (c : Core) : Fintype (PermutationWedge.Vertex c.rotation) := Fintype.ofFinite _

def entry (c : Core) : Fin c.val.length := ⟨0,coreWord_pos _ c.property⟩

/-- Entry-to-child-corner distance in the actual isolated core map. -/
def increment (c : Core) (j : Fin c.val.length) : ℕ :=
  c.graph.dist (vertex c.rotation c.entry)
    (vertex c.rotation ((List.finRange c.val.length).formPerm j))

lemma distance_le (c : Core) (i j : Fin c.val.length) :
    c.graph.dist (vertex c.rotation i) (vertex c.rotation j) ≤ c.val.length := by
  have hc : Fintype.card (PermutationWedge.Vertex c.rotation) ≤ c.val.length := by
    simpa using Fintype.card_le_of_surjective (vertex c.rotation) Quotient.mk_surjective
  by_cases h : c.graph.Reachable (vertex c.rotation i) (vertex c.rotation j)
  · obtain ⟨p,hp,he⟩ := h.exists_path_of_dist
    exact he ▸ (hp.length_lt.le.trans hc)
  · rw [SimpleGraph.dist_eq_zero_of_not_reachable h]
    omega

lemma increment_le (c : Core) (j : Fin c.val.length) : c.increment j≤c.val.length :=
  c.distance_le _ _

end Core

/-- Spine records index the chosen child from the right. Impossible arities
and slot labels are totalized by zero and never sampled by the actual law. -/
def coreIncrement (z : ℕ×ℕ) (a : CoreLabel) : ℝ :=
  match a with
  | none => 0
  | some c => if h : c.val.length=z.1 ∧ z.2<z.1 then
      (c.increment ⟨z.1-1-z.2,by omega⟩:ℝ) else 0

lemma coreIncrement_nonneg (z : ℕ×ℕ) (a : CoreLabel) : 0≤coreIncrement z a := by
  cases a <;> simp only [coreIncrement]
  · rfl
  · split_ifs <;> positivity

lemma coreIncrement_bound (z : ℕ×ℕ) (a : CoreLabel) : |coreIncrement z a|≤z.1 := by
  rw [abs_of_nonneg (coreIncrement_nonneg z a)]
  cases a with
  | none => simp [coreIncrement]
  | some c =>
    simp only [coreIncrement]
    split_ifs with h
    · exact_mod_cast (c.increment_le _).trans h.1.le
    · positivity

lemma coreIncrement_integrable (P : Parameters) (z : ℕ×ℕ) :
    Integrable (coreIncrement z) (CoreLabel.markLaw P z.1).toMeasure := by
  apply (integrable_const (z.1:ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
  exact ae_of_all _ (fun a => by simpa only [Real.norm_eq_abs] using coreIncrement_bound z a)

lemma coreIncrement_mean_bound (P : Parameters) (z : ℕ×ℕ) :
    |∫ a,coreIncrement z a ∂(CoreLabel.markLaw P z.1).toMeasure|≤z.1 := by
  have h := norm_integral_le_of_norm_le_const (μ := (CoreLabel.markLaw P z.1).toMeasure)
    (f := coreIncrement z) (C := (z.1:ℝ))
    (ae_of_all _ (fun a => by simpa only [Real.norm_eq_abs] using coreIncrement_bound z a))
  simpa only [Real.norm_eq_abs,Measure.real,measure_univ,ENNReal.toReal_one,one_mul,mul_one] using h

/-- The source block-distance mean; finiteness uses only offspring variance. -/
def metricMean (P : Parameters) : ℝ :=
  ∫ z,∫ a,coreIncrement z a ∂(CoreLabel.markLaw P z.1).toMeasure ∂(actualOffspring P).spineLaw

lemma metricMean_integrable (P : Parameters) :
    Integrable (fun z => ∫ a,coreIncrement z a ∂(CoreLabel.markLaw P z.1).toMeasure)
      (actualOffspring P).spineLaw :=
  (actualOffspring P).spine_integrable_dom _ (coreIncrement_mean_bound P)

lemma metricMean_nonneg (P : Parameters) : 0 ≤ metricMean P :=
  integral_nonneg (fun z => integral_nonneg (coreIncrement_nonneg z))

/-- Actual all-core labels satisfy the previously proved marked finite-variance
uniform ancestral law, not a bounded-size or exponential-moment substitute. -/
theorem actual_uniform_metric_spine (P : Parameters)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun n => ((actualOffspring P).markedCodeLaw
      (fun k => (CoreLabel.markLaw P k).toMeasure) n).real {x | ∃ v : Fin (2*n+1),
        ε*Real.sqrt ((2*n+1:ℕ):ℝ) < |markedSpineSum coreIncrement x.1 v.isLt.le x.2-
          metricMean P*height x.1.val v.val|}) atTop (𝓝 0) :=
  (actualOffspring P).uniform_integrable_marked_spine hB
    (fun k => (CoreLabel.markLaw P k).toMeasure) coreIncrement (fun _ => measurable_of_countable _)
    coreIncrement_bound hε

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable
variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
lemma vertex_perm_apply (p : Perm α) (x : α) : vertex p (p x)=vertex p x :=
  Quotient.sound (SameCycle.symm ⟨1,by simp⟩)

lemma StackMatching.reachable_first {w : α→TypedLetter} {l : List α}
    (M : StackMatching w l) (hn : l.Nodup) (p : Perm α) (x : α) :
    (dartGraph M.mate p).Reachable (vertex p x) (vertex p (turns M.first x)) := by
  by_cases hx : x∈endpoints M.first
  · rw [turns_sublist_apply (M.covers.nodup_iff.mpr hn) (List.sublist_append_left _ _) hx]
    by_cases he : vertex p x=vertex p (M.mate x)
    · rw [he]; exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable ⟨he,Or.inl ⟨x,rfl,rfl⟩⟩
  · rw [turns_fixed_of_notMem hx]

/-- A genuine successful matching's cyclic tour connects its actual rotation
vertices by original edges; disconnected-distance default values never enter
any isolated-core metric. -/
theorem StackMatching.connected [Fintype α] {w : α→TypedLetter} {l : List α}
    (M : StackMatching w l) (hn : l.Nodup) (hall : ∀ x,x∈l) (hne : l≠[]) :
    (dartGraph M.mate (l.formPerm*turns M.first)).Connected := by
  let p := l.formPerm*turns M.first
  obtain ⟨a,_ha⟩ := List.exists_mem_of_ne_nil l hne
  have hturn : turns M.first*turns M.first=1 :=
    turns_self ((M.covers.nodup_iff.mpr hn).sublist (by
      rw [endpoints_append];exact List.sublist_append_left _ _))
  have htour (x : α) : vertex p (l.formPerm x)=vertex p (turns M.first x) := by
    have he : l.formPerm x=p (turns M.first x) := by
      change l.formPerm x=(l.formPerm*turns M.first*turns M.first) x
      rw [mul_assoc,hturn,mul_one]
    rw [he,vertex_perm_apply]
  refine {preconnected := ?_,nonempty := ⟨vertex p a⟩}
  intro u v
  induction u using Quotient.inductionOn with | h d =>
    induction v using Quotient.inductionOn with | h e =>
      obtain ⟨k,hk⟩ := (sameCycle_formPerm_of_mem hn (hall d) (hall e)).exists_nat_pow_eq
      rw [← hk]
      have hp (j : ℕ) : (dartGraph M.mate p).Reachable
          (vertex p d) (vertex p ((l.formPerm^j) d)) := by
        induction j with
        | zero => exact SimpleGraph.Reachable.refl _
        | succ j ih =>
          rw [pow_succ',mul_apply,htour]
          exact ih.trans (M.reachable_first hn p _)
      exact hp k

namespace Core
lemma graph_connected (c : Core) : c.graph.Connected :=
  c.matching.connected (List.nodup_finRange _) List.mem_finRange (by
    intro h
    have hh := congrArg List.length h
    simp only [List.length_finRange,List.length_nil] at hh
    exact (coreWord_pos _ c.property).ne' hh)

lemma distance_eq_nat (c : Core) (x y : Fin c.val.length) :
    c.matching.distance x y=(c.graph.dist (vertex c.rotation x) (vertex c.rotation y):ℕ∞) := by
  exact (SimpleGraph.Reachable.coe_dist_eq_edist (c.graph_connected.preconnected _ _)).symm
end Core
end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable
variable {α : Type*} [DecidableEq α] [Fintype α]

omit [Fintype α] in
lemma StackMatching.distance_comm {w : α→TypedLetter} {l : List α}
    (M : StackMatching w l) (x y : α) : M.distance x y=M.distance y x :=
  SimpleGraph.edist_comm

/-- Fix one canonical isolated core matching; deleting all its successful
corner intervals gives its distances simultaneously at every pair of darts. -/
theorem StackMatching.core_distance_eq {w : α→TypedLetter}
    (l : List (α×List α)) (M : StackMatching w (dartInsert l))
    (hn : (dartInsert l).Nodup)
    (he : ∀ c∈l,stackTypedRun (c.2.map w) []=some [])
    (D : StackMatching w (l.map Prod.fst)) (x y : α)
    (hx : x∈l.map Prod.fst) (hy : y∈l.map Prod.fst) :
    M.distance x y=D.distance x y := by
  obtain ⟨E,hE⟩ := M.core_distance [] l hn he (List.ne_nil_of_mem hx) x y hx hy
  exact hE.trans (E.unique_distance D ((core_sublist_insert l).nodup hn) x y)

/-- Exact gate additivity in the actual full graph with the inserted component
replaced only by its genuine isolated matching. -/
theorem StackMatching.interval_distance_sum {w : α→TypedLetter}
    (u L z : List α) (a b : α) (R : List α)
    (M : StackMatching w (u++((a::L)++z))) (hn : (u++((a::L)++z)).Nodup)
    (hv : stackTypedRun ((a::L).map w) []=some []) (hcomp : z++u=b::R)
    (D : StackMatching w (a::L)) (x y : α) (hx : x∈a::L) (hy : y∉a::L) :
    M.distance y x=M.distance y b+D.distance a x := by
  have hp := M.empty_interval_pole u L z a b R hn hv hcomp
  have hg := M.empty_interval_gate u L z a b R hn hv hcomp x y hx hy
  change M.distance x y=M.distance x a+M.distance a y at hg
  rw [M.distance_comm x y,M.distance_comm x a,M.distance_comm a y,add_comm] at hg
  have hpb : M.distance y a=M.distance y b := by
    dsimp only [StackMatching.distance]
    rw [hp]
  rw [hpb] at hg
  have hi := M.keep_interval_distance u L z a b R hn hv hcomp a x (by simp) hx
  have hD := (M.keepInterval hn hv).unique_distance D hn.of_append_right.of_append_left a x
  exact hg.trans (congrArg (fun d => M.distance y b+d) (hi.trans hD))

/-- One recursive step of the source pole-distance identity, with literal
core and child darts and all other children still present. -/
theorem StackMatching.corner_distance_sum {w : α→TypedLetter}
    (l : List (α×List α)) (M : StackMatching w (dartInsert l))
    (hn : (dartInsert l).Nodup)
    (he : ∀ c∈l,stackTypedRun (c.2.map w) []=some [])
    (D : StackMatching w (l.map Prod.fst))
    (u L z : List α) (a b : α) (R : List α)
    (hword : dartInsert l=u++((a::L)++z))
    (hv : stackTypedRun ((a::L).map w) []=some []) (hcomp : z++u=b::R)
    (Q : StackMatching w (a::L)) (x r : α) (hx : x∈a::L)
    (hr : r∈l.map Prod.fst) (hrv : r∉a::L) (hb : b∈l.map Prod.fst) :
    M.distance r x=D.distance r b+Q.distance a x := by
  let M' : StackMatching w (u++((a::L)++z)) := hword ▸ M
  have h := M'.interval_distance_sum u L z a b R (hword ▸ hn) hv hcomp Q x r hx hrv
  have hx' := M.distance_cast hword r x
  have hb' := M.distance_cast hword r b
  change M'.distance r x=M.distance r x at hx'
  change M'.distance r b=M.distance r b at hb'
  rw [hx',hb',M.core_distance_eq l hn he D r b hr hb] at h
  exact h

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open MapCycles PermutationWedge TreeCoding
attribute [local instance] Classical.propDecidable

abbrev oneLinkCore : Core := ⟨[.burger true,.order true],oneLink_core⟩

def oneLinkMatching : StackMatching oneLinkCore.val.get (List.finRange oneLinkCore.val.length) where
  first := [(0,1)]
  second := []
  first_arches := Arches.pair 0 1 Arches.nil Arches.nil
  second_arches := Arches.empty _
  covers := by decide
  first_types := by simp [oneLinkCore]
  second_types := by simp

lemma oneLink_rotation : oneLinkCore.rotation=1 := by
  unfold Core.rotation
  rw [oneLinkCore.matching.unique_first oneLinkMatching (List.nodup_finRange _)]
  change (List.finRange 2).formPerm*turns [(0,1)]= (1 : Perm (Fin 2))
  decide

lemma oneLink_mate : oneLinkCore.matching.mate 0=1 := by
  rw [oneLinkCore.matching.unique_mate oneLinkMatching (List.nodup_finRange _)]
  rfl

lemma oneLink_increment : oneLinkCore.increment 0=1 := by
  apply SimpleGraph.dist_eq_one_iff_adj.mpr
  change (vertex oneLinkCore.rotation oneLinkCore.entry ≠
    vertex oneLinkCore.rotation ((List.finRange 2).formPerm 0)) ∧ _
  have hc : (List.finRange 2).formPerm 0=(1:Fin 2) := rfl
  have he : oneLinkCore.entry=(0:Fin 2) := rfl
  rw [hc,he]
  refine ⟨?_,Or.inl ⟨0,rfl,?_⟩⟩
  · intro h
    have hh := Quotient.exact h
    change oneLinkCore.rotation.SameCycle 0 1 at hh
    rw [oneLink_rotation,sameCycle_one] at hh
    exact (by decide : (0:Fin 2)≠1) hh
  · rw [oneLink_mate]
    exact congrArg (vertex oneLinkCore.rotation) hc.symm

lemma coreIncrement_oneLink : coreIncrement (2,1) (some oneLinkCore)=1 := by
  rw [coreIncrement,dite_eq_left (by decide)]
  change (oneLinkCore.increment 0 : ℝ)=1
  rw [oneLink_increment]
  norm_num

lemma coreIncrement_mean_pos (P : Parameters) :
    0 < ∫ a,coreIncrement (2,1) a ∂(CoreLabel.markLaw P 2).toMeasure := by
  apply (integral_pos_iff_support_of_nonneg (coreIncrement_nonneg (2,1))
    (coreIncrement_integrable P (2,1))).mpr
  have hs : {some oneLinkCore} ⊆ Function.support (coreIncrement (2,1)) := by
    intro a ha
    rcases ha with rfl
    change coreIncrement (2,1) (some oneLinkCore)≠0
    rw [coreIncrement_oneLink]
    exact one_ne_zero
  apply lt_of_lt_of_le _ (measure_mono hs)
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    CoreLabel.markLaw_apply P 2 ⟨some oneLinkCore,rfl⟩]
  simp only [CoreLabel.arity,oneLinkCore,List.length_cons,List.length_nil,zero_add,
    Nat.reduceAdd,ite_true]
  apply ENNReal.mul_pos
  · exact (CoreLabel.rootLaw_pos P _).ne'
  · exact ENNReal.inv_ne_zero.mpr (PMF.apply_ne_top _ _)

/-- Strict positivity follows from the positive-mass one-link block and its
nontrivial corner, not from an assumed metric scaling constant. -/
theorem metricMean_pos (P : Parameters) : 0 < metricMean P := by
  apply (integral_pos_iff_support_of_nonneg
    (fun z => integral_nonneg (coreIncrement_nonneg z)) (metricMean_integrable P)).mpr
  have hs : {(2,1)} ⊆ Function.support
      (fun z => ∫ a,coreIncrement z a ∂(CoreLabel.markLaw P z.1).toMeasure) := by
    intro z hz
    rcases hz with rfl
    exact (coreIncrement_mean_pos P).ne'
  apply lt_of_lt_of_le _ (measure_mono hs)
  rw [CriticalEvenOffspring.spineLaw_singleton,ite_eq_left (by decide : (1:ℕ)<2)]
  exact CoreLabel.offspring_pos_attainable P (some oneLinkCore)

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

/-- Literal darts of the recursively substituted word; no quotient identifies
any darts of distinct blocks. -/
def Dart : CoreTree → Type
  | .leaf => Empty
  | .branch c ts => Fin c.val.length ⊕ (Σ i : Fin c.val.length, Dart (ts i))

instance (t : CoreTree) : Fintype t.Dart := by
  induction t with
  | leaf => exact inferInstanceAs (Fintype Empty)
  | branch c ts ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Fin c.val.length ⊕ (Σ i, (ts i).Dart)))

instance (t : CoreTree) : DecidableEq t.Dart := Classical.decEq _

def dartLabel : (t : CoreTree) → t.Dart → TypedLetter
  | .leaf,d => d.elim
  | .branch c _ts,.inl i => c.val.get i
  | .branch _c ts,.inr ⟨i,d⟩ => dartLabel (ts i) d

def childDart {c : Core} (ts : Fin c.val.length→ CoreTree) (i : Fin c.val.length)
    (d : (ts i).Dart) : (branch c ts).Dart := .inr ⟨i,d⟩

def coreDart {c : Core} (ts : Fin c.val.length→ CoreTree) (i : Fin c.val.length) :
    (branch c ts).Dart := .inl i

lemma childDart_injective {c : Core} (ts : Fin c.val.length→ CoreTree) (i : Fin c.val.length) :
    Function.Injective (childDart ts i) := by
  intro x y h
  exact eq_of_heq (Sigma.mk.inj (Sum.inr.inj h)).2

lemma coreDart_injective {c : Core} (ts : Fin c.val.length→ CoreTree) :
    Function.Injective (coreDart ts) := Sum.inl_injective

def darts : (t : CoreTree) → List t.Dart
  | .leaf => []
  | .branch _ ts => (List.finRange _).flatMap fun i =>
      coreDart ts i::((ts i).darts.map (childDart ts i))

def dartCorners (c : Core) (ts : Fin c.val.length→ CoreTree) :
    List ((branch c ts).Dart × List (branch c ts).Dart) :=
  (List.finRange _).map fun i => (coreDart ts i,(ts i).darts.map (childDart ts i))

lemma darts_branch (c : Core) (ts : Fin c.val.length→ CoreTree) :
    (branch c ts).darts=dartInsert (dartCorners c ts) := by
  simp only [darts,dartInsert,dartCorners,List.flatMap_map]

lemma darts_word (t : CoreTree) : t.darts.map t.dartLabel=t.word := by
  induction t with
  | leaf => rfl
  | branch c ts ih =>
    simp only [darts,List.map_flatMap,List.map_cons,List.map_map]
    change (List.finRange c.val.length).flatMap (fun i =>
      c.val.get i :: List.map ((ts i).dartLabel) (ts i).darts)=_
    simp_rw [ih]
    simp only [word,cornerInsert,cornerList,List.ofFn_eq_map,List.flatMap_map]

lemma darts_mem (t : CoreTree) (d : t.Dart) : d∈t.darts := by
  induction t with
  | leaf => exact d.elim
  | branch c ts ih =>
    cases d with
    | inl i => exact List.mem_flatMap.mpr ⟨i,List.mem_finRange _,List.mem_cons_self⟩
    | inr d =>
      obtain ⟨i,d⟩ := d
      exact List.mem_flatMap.mpr ⟨i,List.mem_finRange _,by
        exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨d,ih i d,rfl⟩)⟩

lemma darts_nodup (t : CoreTree) : t.darts.Nodup := by
  induction t with
  | leaf => exact List.nodup_nil
  | branch c ts ih =>
    apply List.nodup_flatMap.mpr
    constructor
    · intro i _
      refine List.nodup_cons.mpr ⟨?_,(ih i).map (childDart_injective ts i)⟩
      intro h
      obtain ⟨x,_,hx⟩ := List.mem_map.mp h
      cases hx
    · refine (List.nodup_finRange c.val.length).imp (fun {i j} hij => ?_)
      change List.Disjoint (coreDart ts i::_) (coreDart ts j::_)
      intro x hx hy
      rcases List.mem_cons.mp hx with hx|hx
      · subst x
        rcases List.mem_cons.mp hy with h|h
        · exact hij (Sum.inl.inj h)
        · obtain ⟨e,_,h⟩ := List.mem_map.mp h
          cases h
      · obtain ⟨d,_,rfl⟩ := List.mem_map.mp hx
        rcases List.mem_cons.mp hy with h|h
        · cases h
        · obtain ⟨e,_,h⟩ := List.mem_map.mp h
          exact hij (congrArg Sigma.fst (Sum.inr.inj h)).symm
def matching (t : CoreTree) : StackMatching t.dartLabel t.darts :=
  StackMatching.ofEmpty (by rw [darts_word];exact t.word_empty)

lemma child_empty (c : Core) (ts : Fin c.val.length→ CoreTree)
    (p : (branch c ts).Dart × List (branch c ts).Dart) (hp : p∈dartCorners c ts) :
    stackTypedRun (p.2.map (branch c ts).dartLabel) []=some [] := by
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
  simpa only [List.map_map,dartLabel,childDart,Function.comp_def,darts_word] using (ts i).word_empty

lemma core_darts (c : Core) (ts : Fin c.val.length→ CoreTree) :
    (dartCorners c ts).map Prod.fst=(List.finRange _).map (coreDart ts) := by
  simp [dartCorners,List.map_map,Function.comp_def]

/-- Exact original graph metric on core darts before/after all substitutions. -/
theorem core_distance (c : Core) (ts : Fin c.val.length→ CoreTree)
    (i j : Fin c.val.length) :
    (branch c ts).matching.distance (coreDart ts i) (coreDart ts j)=c.matching.distance i j := by
  let Q := c.matching.map (coreDart ts) (branch c ts).dartLabel (fun _ _ => rfl)
  let D : StackMatching (branch c ts).dartLabel ((dartCorners c ts).map Prod.fst) :=
    (core_darts c ts).symm ▸ Q
  let M : StackMatching (branch c ts).dartLabel (dartInsert (dartCorners c ts)) :=
    darts_branch c ts ▸ (branch c ts).matching
  have h := M.core_distance_eq (dartCorners c ts) (darts_branch c ts ▸ (branch c ts).darts_nodup)
    (child_empty c ts) D (coreDart ts i) (coreDart ts j)
    (by rw [core_darts];exact List.mem_map.mpr ⟨i,List.mem_finRange _,rfl⟩)
    (by rw [core_darts];exact List.mem_map.mpr ⟨j,List.mem_finRange _,rfl⟩)
  have he := (branch c ts).matching.distance_cast (darts_branch c ts) (coreDart ts i) (coreDart ts j)
  have hD := Q.distance_cast (core_darts c ts).symm (coreDart ts i) (coreDart ts j)
  change D.distance _ _=Q.distance _ _ at hD
  change M.distance _ _=(branch c ts).matching.distance _ _ at he
  rw [he,hD] at h
  exact h.trans (c.matching.map_distance_of_full (List.nodup_finRange _) List.mem_finRange
    (coreDart ts) (coreDart_injective ts) (branch c ts).dartLabel (fun _ _ => rfl) i j)

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable
variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
lemma dartInsert_append (A B : List (α×List α)) :
    dartInsert (A++B)=dartInsert A++dartInsert B :=
  List.flatMap_append

/-- The entry dart following a child interval is exactly the next isolated
core dart in cyclic order, including the last-slot wrap to the root. -/
theorem corner_complement_head (A B : List (α×List α)) (d : α) (v : List α)
    (hn : (dartInsert (A++(d,v)::B)).Nodup) :
    ∃ R,dartInsert B++(dartInsert A++[d])=
      ((A++(d,v)::B).map Prod.fst).formPerm d::R := by
  let L := (A++(d,v)::B).map Prod.fst
  have hcn : L.Nodup := (core_sublist_insert _).nodup hn
  have hrot : L.formPerm=(d::((B++A).map Prod.fst)).formPerm := by
    dsimp [L]
    rw [List.map_append,List.map_cons]
    rw [formPerm_append_comm _ _ (by simpa [L] using hcn)]
    simp only [List.cons_append,List.map_append]
  rw [← List.append_assoc,← dartInsert_append,hrot]
  cases hba : B++A with
  | nil =>
    refine ⟨[],?_⟩
    simp [dartInsert]
  | cons e es =>
    have hn' : (d::e.1::es.map Prod.fst).Nodup := by
      have hh := (List.nodup_append.mp (show (A.map Prod.fst++d::B.map Prod.fst).Nodup by
        simpa [L] using hcn))
      have hh' : ((d::B.map Prod.fst)++A.map Prod.fst).Nodup :=
        List.nodup_append.mpr ⟨hh.2.1,hh.1,fun a ha b hb => (hh.2.2 b hb a ha).symm⟩
      simpa only [List.cons_append,← List.map_append,hba,List.map_cons] using hh'
    refine ⟨e.2++dartInsert es++[d],?_⟩
    rw [List.map_cons,List.formPerm_apply_head _ _ _ hn']
    simp only [dartInsert,List.flatMap_cons,List.cons_append,List.append_assoc]

variable [Fintype α]

/-- The exact selected-slot gate formula, with the cyclic successor computed
in the original isolated core order. -/
theorem StackMatching.selected_corner_distance {w : α→TypedLetter}
    (A B : List (α×List α)) (d a : α) (L : List α)
    (M : StackMatching w (dartInsert (A++(d,a::L)::B)))
    (hn : (dartInsert (A++(d,a::L)::B)).Nodup)
    (he : ∀ p∈A++(d,a::L)::B,stackTypedRun (p.2.map w) []=some [])
    (D : StackMatching w ((A++(d,a::L)::B).map Prod.fst))
    (Q : StackMatching w (a::L)) (r x : α)
    (hr : r∈(A++(d,a::L)::B).map Prod.fst) (hrv : r∉a::L) (hx : x∈a::L) :
    M.distance r x=D.distance r (((A++(d,a::L)::B).map Prod.fst).formPerm d)+Q.distance a x := by
  obtain ⟨R,hR⟩ := corner_complement_head A B d (a::L) hn
  apply M.corner_distance_sum (A++(d,a::L)::B) hn he D
    (dartInsert A++[d]) L (dartInsert B) a _ R
    (by simp [dartInsert,List.flatMap_append,List.append_assoc])
    (he (d,a::L) (by simp)) hR Q x r hx hr hrv
  exact List.formPerm_apply_mem_of_mem (by simp)

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

def nextSlot (c : Core) (i : Fin c.val.length) : Fin c.val.length :=
  (List.finRange c.val.length).formPerm i

lemma core_next (c : Core) (ts : Fin c.val.length → CoreTree) (i : Fin c.val.length) :
    ((dartCorners c ts).map Prod.fst).formPerm (coreDart ts i)=coreDart ts (nextSlot c i) := by
  rw [core_darts]
  exact formPerm_map_on _ (List.nodup_finRange _) (coreDart ts) (coreDart_injective ts) _ (List.mem_finRange _)

/-- Exact all-edge ancestor step for arbitrary literal child darts. -/
theorem child_distance_sum (c : Core) (ts : Fin c.val.length → CoreTree)
    (i r : Fin c.val.length) (a x : (ts i).Dart) (L : List (ts i).Dart)
    (hhead : (ts i).darts=a::L) :
    (branch c ts).matching.distance (coreDart ts r) (childDart ts i x)=
      c.matching.distance r (nextSlot c i)+(ts i).matching.distance a x := by
  let v := (ts i).darts.map (childDart ts i)
  have hm : (coreDart ts i,v)∈dartCorners c ts := List.mem_map.mpr ⟨i,List.mem_finRange _,rfl⟩
  obtain ⟨A,B,hAB⟩ := List.mem_iff_append.mp hm
  have hv : v=childDart ts i a::L.map (childDart ts i) := by simp only [v,hhead,List.map_cons]
  let u := dartInsert A++[coreDart ts i]
  let z := dartInsert B
  have hw : (branch c ts).darts=u++((childDart ts i a::L.map (childDart ts i))++z) := by
    rw [darts_branch,hAB]
    simp only [dartInsert,List.flatMap_append,List.flatMap_cons,List.cons_append,hv,u,z,List.append_assoc,
      List.nil_append]
  let M : StackMatching (branch c ts).dartLabel (u++((childDart ts i a::L.map (childDart ts i))++z)) :=
    hw ▸ (branch c ts).matching
  have hn := hw ▸ (branch c ts).darts_nodup
  have he : stackTypedRun ((childDart ts i a::L.map (childDart ts i)).map (branch c ts).dartLabel) []=some [] := by
    rw [← hv]
    exact child_empty c ts _ hm
  obtain ⟨R,hR⟩ := corner_complement_head A B (coreDart ts i) v
    (by rw [← hAB,← darts_branch];exact (branch c ts).darts_nodup)
  rw [← hAB,core_next] at hR
  let Q₀ := (ts i).matching.map (childDart ts i) (branch c ts).dartLabel (fun _ _ => rfl)
  let Q : StackMatching (branch c ts).dartLabel
      (childDart ts i a::L.map (childDart ts i)) := hv ▸ Q₀
  have hx : childDart ts i x∈childDart ts i a::L.map (childDart ts i) := by
    rw [← hv]
    exact List.mem_map.mpr ⟨x,(ts i).darts_mem x,rfl⟩
  have hr : coreDart ts r∉childDart ts i a::L.map (childDart ts i) := by
    rw [← hv]
    intro h
    obtain ⟨y,_,hy⟩ := List.mem_map.mp h
    cases hy
  have hg := M.interval_distance_sum u (L.map (childDart ts i)) z (childDart ts i a)
    (coreDart ts (nextSlot c i)) R hn he hR Q (childDart ts i x) (coreDart ts r) hx hr
  have hp (x y : (branch c ts).Dart) : M.distance x y=(branch c ts).matching.distance x y :=
    (branch c ts).matching.distance_cast hw x y
  have hq : Q.distance (childDart ts i a) (childDart ts i x)=
      (ts i).matching.distance a x := by
    rw [show Q.distance _ _=Q₀.distance (childDart ts i a) (childDart ts i x) from
      Q₀.distance_cast hv _ _]
    exact (ts i).matching.map_distance_of_full (ts i).darts_nodup (ts i).darts_mem
      (childDart ts i) (childDart_injective ts i) (branch c ts).dartLabel (fun _ _ => rfl) a x
  rw [hp,hp,hq,core_distance] at hg
  exact hg

end FKCRT.Inventory.CoreTree
end

end OAI
