import OAI.NumberTheory.Jacobsthal.Estimates.ReferenceCutoffRecurrence
import OAI.NumberTheory.Jacobsthal.Paths.CorrectSearchTags
import OAI.NumberTheory.Jacobsthal.Sieve.AlignedPrimeCongruence

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.StoppedCountVertex

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeHistories ReferenceAdmission ReferencePrefixRecurrence
open ReferenceForestTelescoping ReferencePruning SievePartition
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

structure Vertex where
  node : Node
  required : Finset ℕ
  available : Finset ℕ
  past : List ℕ
  scale : ℝ

noncomputable def child (w : ℝ) (v : Vertex) (p : ℕ) : Vertex where
  node := step w v.node p
  required := insert p v.required
  available := v.available.filter (fun q => q < p)
  past := v.past++[p]
  scale := v.scale/(p:ℝ)

noncomputable def includedPrimes (w : ℝ) (v : Vertex) : Finset ℕ :=
  v.available.filter fun p => childAdmitted v.node.side v.node.gap (primeExponent w p)

theorem included_subset (w : ℝ) (v : Vertex) : includedPrimes w v ⊆ v.available :=
  Finset.filter_subset _ _

theorem included_even (w : ℝ) (v : Vertex) (hi : v.node.side = .even) :
    includedPrimes w v = v.available := by simp [includedPrimes,hi,childAdmitted]

theorem child_rank_lt (w : ℝ) (v : Vertex) {p : ℕ} (hp : p ∈ v.available) :
    (child w v p).available.card < v.available.card :=
  Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨p,hp,lt_irrefl p⟩)

noncomputable def countMass (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (v : Vertex) : ℝ :=
  ((residueCandidates Y v.required small a).card : ℝ)

noncomputable def countSurvivors (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (v : Vertex) : ℝ :=
  ((survivors (residueCandidates Y v.required small a) v.available (residueBad a)).card : ℝ)

theorem countSurvivors_nonneg (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (v : Vertex) :
    0 ≤ countSurvivors Y small a v := Nat.cast_nonneg _

theorem count_partition (w : ℝ) (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (v : Vertex) :
    countSurvivors Y small a v = countMass Y small a v -
      ∑ p ∈ v.available,countSurvivors Y small a (child w v p) := by
  have h := residue_tree_identity Y v.required small v.available a
  unfold countSurvivors countMass child
  exact_mod_cast h

noncomputable def referenceValue (w : ℝ) (v : Vertex) : ℝ :=
  v.scale*referencePolynomial w v.available v.node.side v.node.gap

theorem reference_partition (w : ℝ) (v : Vertex) :
    referenceValue w v = v.scale - ∑ p ∈ includedPrimes w v,referenceValue w (child w v p) := by
  rw [referenceValue,reference_polynomial_recurrence,mul_sub,mul_one,Finset.mul_sum,
    includedPrimes,Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : childAdmitted v.node.side v.node.gap (primeExponent w p)
  · simp only [ite_eq_left hp,referenceValue,child,step]
    ring
  · simp only [ite_eq_right hp,mul_zero]

theorem count_leaf (w : ℝ) (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (v : Vertex)
    (hv : v.available = ∅) : countSurvivors Y small a v = countMass Y small a v := by
  simpa only [hv,Finset.sum_empty,sub_zero] using count_partition w Y small a v

theorem reference_leaf (w : ℝ) (v : Vertex) (hv : v.available = ∅) : referenceValue w v = v.scale := by
  simpa only [includedPrimes,hv,Finset.filter_empty,Finset.sum_empty,sub_zero] using reference_partition w v

end NumberTheoryLean.StoppedCountVertex



namespace NumberTheoryLean.StoppedEvaluation

open _root_.Finset
open FinitePathGeometry StoppedCountVertex
attribute [local instance] Classical.propDecidable

def lowerStop (stop : List ℕ → Prop) (v : Vertex) : Prop :=
  v.node.side = .even ∧ stop v.past

noncomputable def evaluate (w : ℝ) (stop : List ℕ → Prop)
    (mass exit : Vertex → ℝ) : ℕ → Vertex → ℝ
  | 0,v => if lowerStop stop v then exit v else mass v
  | n+1,v => if lowerStop stop v then exit v else
      mass v - ∑ p ∈ includedPrimes w v,evaluate w stop mass exit n (child w v p)

theorem evaluate_sub (w : ℝ) (stop : List ℕ → Prop) (M₁ M₂ E₁ E₂ : Vertex → ℝ)
    (n : ℕ) (v : Vertex) :
    evaluate w stop (fun v => M₁ v-M₂ v) (fun v => E₁ v-E₂ v) n v =
      evaluate w stop M₁ E₁ n v-evaluate w stop M₂ E₂ n v := by
  induction n generalizing v with
  | zero => simp only [evaluate]; split_ifs <;> rfl
  | succ n ih =>
    simp only [evaluate]
    split_ifs
    · rfl
    · simp only [ih,Finset.sum_sub_distrib]
      ring

theorem evaluate_add (w : ℝ) (stop : List ℕ → Prop) (M₁ M₂ E₁ E₂ : Vertex → ℝ)
    (n : ℕ) (v : Vertex) :
    evaluate w stop (fun v => M₁ v+M₂ v) (fun v => E₁ v+E₂ v) n v =
      evaluate w stop M₁ E₁ n v+evaluate w stop M₂ E₂ n v := by
  induction n generalizing v with
  | zero => simp only [evaluate]; split_ifs <;> rfl
  | succ n ih =>
    simp only [evaluate]
    split_ifs
    · rfl
    · simp only [ih,Finset.sum_add_distrib]
      ring

theorem evaluate_reference (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    (hn : v.available.card ≤ n) :
    evaluate w stop Vertex.scale (referenceValue w) n v = referenceValue w v := by
  induction n generalizing v with
  | zero =>
    have hv : v.available = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hn)
    simp only [evaluate]
    split_ifs
    · rfl
    · exact (reference_leaf w v hv).symm
  | succ n ih =>
    rw [evaluate]
    split_ifs
    · rfl
    · rw [reference_partition]
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      apply ih
      have hlt := child_rank_lt w v (included_subset w v hp)
      omega

noncomputable def stoppedCount (w : ℝ) (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (stop : List ℕ → Prop) (n : ℕ) (v : Vertex) : ℝ :=
  evaluate w stop (countMass Y small a) (countSurvivors Y small a) n v

theorem stopped_count_reference_difference (w : ℝ) (Y : ℕ) (small : Finset ℕ)
    (a : ℕ → ℕ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex) (hn : v.available.card ≤ n) :
    stoppedCount w Y small a stop n v-referenceValue w v =
      evaluate w stop (fun z => countMass Y small a z-z.scale) (fun _ => 0) n v +
      evaluate w stop (fun _ => 0) (fun z => countSurvivors Y small a z-referenceValue w z) n v := by
  rw [← evaluate_reference w stop n v hn]
  change evaluate w stop (countMass Y small a) (countSurvivors Y small a) n v - _ = _
  rw [← evaluate_sub]
  have h := evaluate_add w stop (fun z => countMass Y small a z-z.scale) (fun _ => 0)
    (fun _ => 0) (fun z => countSurvivors Y small a z-referenceValue w z) n v
  simpa only [add_zero,zero_add] using h

end NumberTheoryLean.StoppedEvaluation



namespace NumberTheoryLean.StoppedVertexHistory

open _root_.Finset
open FinitePathGeometry PrimeHistories StoppedCountVertex ReferenceForestTelescoping ReferencePruning
open ErdosPrimeInputs.PrimePrefixMass

noncomputable def after (w : ℝ) : Vertex → List ℕ → Vertex
  | v,[] => v
  | v,p::ps => after w (child w v p) ps

theorem after_node (w : ℝ) (v : Vertex) (ps : List ℕ) :
    (after w v ps).node = terminal w v.node ps := by
  induction ps generalizing v with
  | nil => rfl
  | cons p ps ih => exact ih (child w v p)

theorem after_past (w : ℝ) (v : Vertex) (ps : List ℕ) :
    (after w v ps).past = v.past++ps := by
  induction ps generalizing v with
  | nil => simp [after]
  | cons p ps ih =>
    change (after w (child w v p) ps).past = _
    rw [ih]
    simp [child,List.append_assoc]

theorem after_required (w : ℝ) (v : Vertex) (ps : List ℕ) :
    (after w v ps).required = v.required ∪ ps.toFinset := by
  induction ps generalizing v with
  | nil => simp [after]
  | cons p ps ih =>
    change (after w (child w v p) ps).required = _
    rw [ih]
    ext q
    simp only [child,List.toFinset_cons,Finset.mem_union,Finset.mem_insert]
    tauto

theorem after_available (w : ℝ) (v : Vertex) (ps : List ℕ) :
    (after w v ps).available = suffixPrimes v.available ps := by
  induction ps generalizing v with
  | nil => simp [after,suffixPrimes_nil]
  | cons p ps ih =>
    change (after w (child w v p) ps).available = _
    rw [ih,suffixPrimes_cons]
    rfl

theorem after_scale (w : ℝ) (v : Vertex) (ps : List ℕ) :
    (after w v ps).scale = v.scale*prefixWeight ps := by
  induction ps generalizing v with
  | nil => simp [after,prefixWeight]
  | cons p ps ih =>
    change (after w (child w v p) ps).scale = _
    rw [ih]
    change (v.scale/(p:ℝ))*prefixWeight ps = v.scale*((p:ℝ)⁻¹*prefixWeight ps)
    ring

theorem prefixWeight_product (ps : List ℕ) : prefixWeight ps = ((ps.prod:ℕ):ℝ)⁻¹ := by
  induction ps with
  | nil => simp [prefixWeight]
  | cons p ps ih =>
    change (p:ℝ)⁻¹*prefixWeight ps = ((p*ps.prod:ℕ):ℝ)⁻¹
    rw [ih,Nat.cast_mul,mul_inv_rev]
    ring

theorem after_scale_product (w : ℝ) (v : Vertex) (ps : List ℕ) :
    (after w v ps).scale = v.scale/((ps.prod:ℕ):ℝ) := by
  rw [after_scale,prefixWeight_product,div_eq_mul_inv]

end NumberTheoryLean.StoppedVertexHistory



namespace NumberTheoryLean.StoppedCountLowerBound

open _root_.Finset
open FinitePathGeometry PrimeHistories StoppedCountVertex StoppedEvaluation
attribute [local instance] Classical.propDecidable

theorem actual_stopped_bounds (w : ℝ) (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (stop : List ℕ → Prop) (n : ℕ) (v : Vertex) (hn : v.available.card ≤ n) :
    (v.node.side = .even → stoppedCount w Y small a stop n v ≤ countSurvivors Y small a v) ∧
    (v.node.side = .odd → countSurvivors Y small a v ≤ stoppedCount w Y small a stop n v) := by
  induction n generalizing v with
  | zero =>
    have hv : v.available = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hn)
    have he : stoppedCount w Y small a stop 0 v = countSurvivors Y small a v := by
      rw [stoppedCount,evaluate]
      split_ifs
      · rfl
      · exact (count_leaf w Y small a v hv).symm
    rw [he]
    exact ⟨fun _ => le_rfl,fun _ => le_rfl⟩
  | succ n ih =>
    have hRank : ∀ p ∈ v.available,(child w v p).available.card ≤ n := by
      intro p hp
      have hlt := child_rank_lt w v hp
      omega
    have hPart := count_partition w Y small a v
    constructor
    · intro hi
      unfold stoppedCount
      rw [evaluate]
      split_ifs
      · exact le_rfl
      · rw [included_even w v hi]
        have hsum : (∑ p ∈ v.available,countSurvivors Y small a (child w v p)) ≤
            ∑ p ∈ v.available,evaluate w stop (countMass Y small a) (countSurvivors Y small a) n (child w v p) := by
          apply Finset.sum_le_sum
          intro p hp
          exact (ih (child w v p) (hRank p hp)).2 (by simp [child,step,hi,Side.flip])
        linarith
    · intro hi
      have hstop : ¬lowerStop stop v := by simp [lowerStop,hi]
      unfold stoppedCount
      rw [evaluate,ite_eq_right hstop]
      have hsum : (∑ p ∈ includedPrimes w v,
          evaluate w stop (countMass Y small a) (countSurvivors Y small a) n (child w v p)) ≤
          ∑ p ∈ includedPrimes w v,countSurvivors Y small a (child w v p) := by
        apply Finset.sum_le_sum
        intro p hp
        exact (ih (child w v p) (hRank p (included_subset w v hp))).1 (by simp [child,step,hi,Side.flip])
      have hsub : (∑ p ∈ includedPrimes w v,countSurvivors Y small a (child w v p)) ≤
          ∑ p ∈ v.available,countSurvivors Y small a (child w v p) :=
        Finset.sum_le_sum_of_subset_of_nonneg (included_subset w v)
          (fun p _ _ => countSurvivors_nonneg Y small a (child w v p))
      linarith

theorem actual_stopped_lower_bound (w : ℝ) (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (stop : List ℕ → Prop) (v : Vertex) (hi : v.node.side = .even) :
    stoppedCount w Y small a stop v.available.card v ≤ countSurvivors Y small a v :=
  (actual_stopped_bounds w Y small a stop v.available.card v le_rfl).1 hi

end NumberTheoryLean.StoppedCountLowerBound



namespace NumberTheoryLean.StoppedTraceSets

open _root_.Set _root_.Finset
open FinitePathGeometry StoppedCountVertex StoppedEvaluation StoppedVertexHistory
attribute [local instance] Classical.propDecidable

noncomputable def childrenTraces (P : Finset ℕ) (T : ℕ → Finset (List ℕ)) : Finset (List ℕ) :=
  P.biUnion (fun p => (T p).image (List.cons p))

theorem nil_not_childrenTraces (P : Finset ℕ) (T : ℕ → Finset (List ℕ)) :
    [] ∉ childrenTraces P T := by simp [childrenTraces]

theorem sum_childrenTraces (P : Finset ℕ) (T : ℕ → Finset (List ℕ)) (F : List ℕ → ℝ) :
    (∑ ps ∈ childrenTraces P T,F ps) = ∑ p ∈ P,∑ ps ∈ T p,F (p::ps) := by
  have hd : (P:Set ℕ).PairwiseDisjoint (fun p => (T p).image (List.cons p)) := by
    intro p _ q _ hpq
    apply Finset.disjoint_left.mpr
    intro ps hp hq
    obtain ⟨xp,_hxp,hxp⟩ := Finset.mem_image.mp hp
    obtain ⟨xq,_hxq,hxq⟩ := Finset.mem_image.mp hq
    exact hpq (List.cons.inj (hxp.trans hxq.symm)).1
  rw [childrenTraces,Finset.sum_biUnion hd]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_image]
  intro a _ b _ heq
  exact (List.cons.inj heq).2

noncomputable def traces (w : ℝ) (stop : List ℕ → Prop) : ℕ → Vertex →
    Finset (List ℕ) × Finset (List ℕ)
  | 0,v => if lowerStop stop v then (∅,{[]}) else ({[]},∅)
  | n+1,v => if lowerStop stop v then (∅,{[]}) else
      (insert [] (childrenTraces (includedPrimes w v) (fun p => (traces w stop n (child w v p)).1)),
        childrenTraces (includedPrimes w v) (fun p => (traces w stop n (child w v p)).2))

noncomputable def expanded (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex) : Finset (List ℕ) :=
  (traces w stop n v).1

noncomputable def stopped (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex) : Finset (List ℕ) :=
  (traces w stop n v).2

theorem stopped_lower (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    {ps : List ℕ} (hp : ps ∈ stopped w stop n v) : (after w v ps).node.side = .even := by
  induction n generalizing v ps with
  | zero =>
    unfold stopped at hp
    rw [traces] at hp
    split_ifs at hp with hs
    · have heq : ps = [] := Finset.mem_singleton.mp hp
      subst ps
      exact hs.1
    · exact False.elim (Finset.notMem_empty _ hp)
  | succ n ih =>
    unfold stopped at hp
    rw [traces] at hp
    split_ifs at hp with hs
    · have heq : ps = [] := Finset.mem_singleton.mp hp
      subst ps
      exact hs.1
    · obtain ⟨p,_hp,hps⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨tail,ht,rfl⟩ := Finset.mem_image.mp hps
      exact ih (child w v p) ht

theorem signed_childrenTraces (w : ℝ) (v : Vertex) (P : Finset ℕ)
    (T : ℕ → Finset (List ℕ)) (G : Vertex → ℝ) :
    (∑ ps ∈ childrenTraces P T,(-1:ℝ)^ps.length*G (after w v ps)) =
      -(∑ p ∈ P,∑ ps ∈ T p,(-1:ℝ)^ps.length*G (after w (child w v p) ps)) := by
  rw [sum_childrenTraces,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro ps _
  simp only [List.length_cons,pow_succ,after]
  ring

end NumberTheoryLean.StoppedTraceSets



namespace NumberTheoryLean.FirstStopSemantics

open _root_.Finset
open StoppedCountVertex StoppedEvaluation StoppedVertexHistory StoppedTraceSets
attribute [local instance] Classical.propDecidable

def FirstStop (w : ℝ) (stop : List ℕ → Prop) (v : Vertex) (ps : List ℕ) : Prop :=
  lowerStop stop (after w v ps) ∧ ∀ pre tail : List ℕ,
    ps = pre++tail → tail ≠ [] → ¬lowerStop stop (after w v pre)

theorem firstStop_nil (w : ℝ) (stop : List ℕ → Prop) (v : Vertex) (hs : lowerStop stop v) :
    FirstStop w stop v [] := by
  refine ⟨hs,?_⟩
  intro pre tail heq ht
  exact False.elim (ht (List.append_eq_nil_iff.mp heq.symm).2)

theorem stopped_first (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    {ps : List ℕ} (hp : ps ∈ stopped w stop n v) : FirstStop w stop v ps := by
  induction n generalizing v ps with
  | zero =>
    unfold stopped at hp
    rw [traces] at hp
    split_ifs at hp with hs
    · have heq : ps = [] := Finset.mem_singleton.mp hp
      subst ps
      exact firstStop_nil w stop v hs
    · exact False.elim (Finset.notMem_empty _ hp)
  | succ n ih =>
    unfold stopped at hp
    rw [traces] at hp
    split_ifs at hp with hs
    · have heq : ps = [] := Finset.mem_singleton.mp hp
      subst ps
      exact firstStop_nil w stop v hs
    · obtain ⟨p,_hp,hps⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨tail,ht,rfl⟩ := Finset.mem_image.mp hps
      have hfirst := ih (child w v p) ht
      refine ⟨hfirst.1,?_⟩
      intro pre suffix heq hsuffix
      cases pre with
      | nil => exact hs
      | cons q qs =>
        rw [List.cons_append] at heq
        have hhead := (List.cons.inj heq).1
        have htail := (List.cons.inj heq).2
        subst q
        exact hfirst.2 qs suffix htail hsuffix

theorem stopped_prefix_free (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    {ps qs : List ℕ} (hp : ps ∈ stopped w stop n v) (hq : qs ∈ stopped w stop n v)
    (hpre : ∃ tail : List ℕ,qs = ps++tail) : ps = qs := by
  obtain ⟨tail,heq⟩ := hpre
  by_cases ht : tail = []
  · simpa only [ht,List.append_nil] using heq.symm
  · exact False.elim ((stopped_first w stop n v hq).2 ps tail heq ht
      (stopped_first w stop n v hp).1)

end NumberTheoryLean.FirstStopSemantics



namespace NumberTheoryLean.FlatStoppedIdentity

open _root_.Finset
open FinitePathGeometry StoppedCountVertex StoppedEvaluation StoppedVertexHistory StoppedTraceSets
attribute [local instance] Classical.propDecidable

theorem flat_evaluate (w : ℝ) (stop : List ℕ → Prop) (M E : Vertex → ℝ) (n : ℕ) (v : Vertex) :
    evaluate w stop M E n v =
      (∑ ps ∈ expanded w stop n v,(-1:ℝ)^ps.length*M (after w v ps)) +
      (∑ ps ∈ stopped w stop n v,(-1:ℝ)^ps.length*E (after w v ps)) := by
  induction n generalizing v with
  | zero =>
    by_cases hs : lowerStop stop v <;> simp [evaluate,expanded,stopped,traces,hs,after]
  | succ n ih =>
    by_cases hs : lowerStop stop v
    · simp [evaluate,expanded,stopped,traces,hs,after]
    · simp only [evaluate,hs,ite_false,expanded,stopped,traces]
      rw [Finset.sum_insert (nil_not_childrenTraces _ _),signed_childrenTraces,signed_childrenTraces]
      simp only [List.length_nil,pow_zero,after,one_mul]
      have hsum : (∑ p ∈ includedPrimes w v,evaluate w stop M E n (child w v p)) =
          ∑ p ∈ includedPrimes w v,
            ((∑ ps ∈ expanded w stop n (child w v p),(-1:ℝ)^ps.length*M (after w (child w v p) ps)) +
            (∑ ps ∈ stopped w stop n (child w v p),(-1:ℝ)^ps.length*E (after w (child w v p) ps))) :=
        Finset.sum_congr rfl (fun p _ => ih (child w v p))
      rw [hsum,Finset.sum_add_distrib]
      simp only [expanded,stopped]
      ring

def sideSign : Side → ℝ
  | .even => 1
  | .odd => -1

theorem sideSign_after (w : ℝ) (v : Vertex) (ps : List ℕ) :
    sideSign (after w v ps).node.side = sideSign v.node.side*(-1:ℝ)^ps.length := by
  induction ps generalizing v with
  | nil => simp [after]
  | cons p ps ih =>
    change sideSign (after w (child w v p) ps).node.side = _
    rw [ih]
    simp only [child,PrimeHistories.step,List.length_cons,pow_succ]
    cases v.node.side <;> simp only [Side.flip,sideSign] <;> ring

theorem stopped_sign_one (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    (hi : v.node.side = .even) {ps : List ℕ} (hp : ps ∈ stopped w stop n v) :
    (-1:ℝ)^ps.length = 1 := by
  have h := sideSign_after w v ps
  rw [stopped_lower w stop n v hp,hi] at h
  simpa only [sideSign,one_mul] using h.symm

theorem literal_stopped_difference (w : ℝ) (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    (hn : v.available.card ≤ n) (hi : v.node.side = .even) :
    stoppedCount w Y small a stop n v-referenceValue w v =
      (∑ ps ∈ expanded w stop n v,(-1:ℝ)^ps.length*
        (countMass Y small a (after w v ps)-(after w v ps).scale)) +
      (∑ ps ∈ stopped w stop n v,
        (countSurvivors Y small a (after w v ps)-referenceValue w (after w v ps))) := by
  rw [stopped_count_reference_difference w Y small a stop n v hn,
    flat_evaluate w stop (fun z => countMass Y small a z-z.scale) (fun _ => 0),
    flat_evaluate w stop (fun _ => 0) (fun z => countSurvivors Y small a z-referenceValue w z)]
  simp only [mul_zero,Finset.sum_const_zero,add_zero,zero_add]
  congr 1
  apply Finset.sum_congr rfl
  intro ps hp
  rw [stopped_sign_one w stop n v hi hp,one_mul]

theorem actual_reference_error_lower_bound (w : ℝ) (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    (hn : v.available.card ≤ n) (hi : v.node.side = .even) :
    referenceValue w v +
      (∑ ps ∈ expanded w stop n v,(-1:ℝ)^ps.length*
        (countMass Y small a (after w v ps)-(after w v ps).scale)) +
      (∑ ps ∈ stopped w stop n v,
        (countSurvivors Y small a (after w v ps)-referenceValue w (after w v ps))) ≤
      countSurvivors Y small a v := by
  have h := literal_stopped_difference w Y small a stop n v hn hi
  have hL := (StoppedCountLowerBound.actual_stopped_bounds w Y small a stop n v hn).1 hi
  linarith

end NumberTheoryLean.FlatStoppedIdentity



namespace NumberTheoryLean.StoppedTraceAdmission

open _root_.Finset
open FinitePathGeometry PrimeHistories StoppedCountVertex StoppedTraceSets
open ReferenceAdmission ReferencePruning ReferencePrefixRecurrence
open ErdosPrimeInputs.PrimePrefixMass
attribute [local instance] Classical.propDecidable

theorem reference_nil_mem (w : ℝ) (v : Vertex) :
    [] ∈ referencePrefixes w v.available v.node.side v.node.gap := by
  apply Finset.mem_filter.mpr
  exact ⟨mem_decreasingPrefixes.mpr ⟨by simp,by simp⟩,trivial⟩

theorem reference_child_cons (w : ℝ) (v : Vertex) {p : ℕ} (hp : p ∈ includedPrimes w v)
    {ps : List ℕ} (hps : ps ∈ referencePrefixes w (child w v p).available
      (child w v p).node.side (child w v p).node.gap) :
    p::ps ∈ referencePrefixes w v.available v.node.side v.node.gap := by
  have hchild := Finset.mem_filter.mp hp
  have htail := Finset.mem_filter.mp hps
  have hSuf : ps ∈ decreasingPrefixes (suffixPrimes v.available [p]) := by
    simpa only [suffixPrimes,List.mem_singleton,forall_eq,child] using htail.1
  have hdec := (append_mem_decreasing_iff (singleton_prefix_mem hchild.1)).mpr hSuf
  apply Finset.mem_filter.mpr
  refine ⟨by simpa only [List.singleton_append] using hdec,?_⟩
  exact ⟨hchild.2,htail.2⟩

theorem trace_reference_member (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    {ps : List ℕ} (hp : ps ∈ expanded w stop n v ∨ ps ∈ stopped w stop n v) :
    ps ∈ referencePrefixes w v.available v.node.side v.node.gap := by
  induction n generalizing v ps with
  | zero =>
    by_cases hs : StoppedEvaluation.lowerStop stop v
    · have heq : ps = [] := by simpa [expanded,stopped,traces,hs] using hp
      subst ps
      exact reference_nil_mem w v
    · have heq : ps = [] := by simpa [expanded,stopped,traces,hs] using hp
      subst ps
      exact reference_nil_mem w v
  | succ n ih =>
    by_cases hs : StoppedEvaluation.lowerStop stop v
    · have heq : ps = [] := by simpa [expanded,stopped,traces,hs] using hp
      subst ps
      exact reference_nil_mem w v
    · rcases hp with hExp | hStop
      · simp only [expanded,traces,hs,ite_false,Finset.mem_insert] at hExp
        rcases hExp with rfl | hExp
        · exact reference_nil_mem w v
        · obtain ⟨p,hp,hps⟩ := Finset.mem_biUnion.mp hExp
          obtain ⟨tail,ht,rfl⟩ := Finset.mem_image.mp hps
          exact reference_child_cons w v hp (ih (child w v p) (Or.inl ht))
      · simp only [stopped,traces,hs,ite_false] at hStop
        obtain ⟨p,hp,hps⟩ := Finset.mem_biUnion.mp hStop
        obtain ⟨tail,ht,rfl⟩ := Finset.mem_image.mp hps
        exact reference_child_cons w v hp (ih (child w v p) (Or.inr ht))

theorem trace_nodup (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    {ps : List ℕ} (hp : ps ∈ expanded w stop n v ∨ ps ∈ stopped w stop n v) : ps.Nodup := by
  have h := (mem_decreasingPrefixes.mp (Finset.mem_filter.mp (trace_reference_member w stop n v hp)).1).1
  exact h.imp (fun h => ne_of_gt h)

theorem trace_primes (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    (hP : ∀ p ∈ v.available,Nat.Prime p) {ps : List ℕ}
    (hp : ps ∈ expanded w stop n v ∨ ps ∈ stopped w stop n v) : ∀ p ∈ ps,Nat.Prime p := by
  have h := (mem_decreasingPrefixes.mp (Finset.mem_filter.mp (trace_reference_member w stop n v hp)).1).2
  intro p hps
  exact hP p (h p hps)

end NumberTheoryLean.StoppedTraceAdmission



namespace NumberTheoryLean.StoppedCountAdapters

open _root_.Finset
open FinitePathGeometry PrimeHistories StoppedCountVertex StoppedEvaluation StoppedVertexHistory
open StoppedTraceSets FlatStoppedIdentity ReferenceAdmission ReferencePruning
attribute [local instance] Classical.propDecidable

noncomputable def rootVertex (z : Node) (H P : Finset ℕ) (mu : ℝ) : Vertex :=
  ⟨z,H,P,[],mu⟩

theorem countMass_eq_tree_mass (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (v : Vertex) :
    countMass Y small a v = (ResidueSieveTree.mass Y small a (v.required,v.available) : ℝ) := by
  simp only [countMass,ResidueSieveTree.mass,Int.cast_natCast]

theorem countSurvivors_eq_tree_survivors (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (v : Vertex) :
    countSurvivors Y small a v =
      (ResidueSieveTree.survivorCount Y small a (v.required,v.available) : ℝ) := by
  simp only [countSurvivors,ResidueSieveTree.survivorCount,Int.cast_natCast]

theorem root_after_mass (w : ℝ) (Y : ℕ) (small H P : Finset ℕ) (a : ℕ → ℕ)
    (z : Node) (mu : ℝ) (ps : List ℕ) :
    countMass Y small a (after w (rootVertex z H P mu) ps) =
      (ResidueSieveTree.mass Y small a (H ∪ ps.toFinset,suffixPrimes P ps) : ℝ) := by
  rw [countMass_eq_tree_mass,after_required,after_available]
  rfl

theorem root_after_survivors (w : ℝ) (Y : ℕ) (small H P : Finset ℕ) (a : ℕ → ℕ)
    (z : Node) (mu : ℝ) (ps : List ℕ) :
    countSurvivors Y small a (after w (rootVertex z H P mu) ps) =
      (ResidueSieveTree.survivorCount Y small a (H ∪ ps.toFinset,suffixPrimes P ps) : ℝ) := by
  rw [countSurvivors_eq_tree_survivors,after_required,after_available]
  rfl

theorem root_after_reference (w : ℝ) (H P : Finset ℕ) (z : Node) (mu : ℝ) (ps : List ℕ) :
    referenceValue w (after w (rootVertex z H P mu) ps) =
      (mu/(ps.prod:ℝ))*referencePolynomial w (suffixPrimes P ps)
        (terminal w z ps).side (terminal w z ps).gap := by
  rw [referenceValue,after_scale_product,after_available,after_node]
  rfl

theorem literal_root_lower_comparison (w : ℝ) (Y : ℕ) (small H P : Finset ℕ)
    (a : ℕ → ℕ) (z : Node) (mu : ℝ) (stop : List ℕ → Prop) (hi : z.side = .even) :
    mu*referencePolynomial w P z.side z.gap +
      (∑ ps ∈ expanded w stop P.card (rootVertex z H P mu),(-1:ℝ)^ps.length*
        ((ResidueSieveTree.mass Y small a (H ∪ ps.toFinset,suffixPrimes P ps) : ℝ)-mu/(ps.prod:ℝ))) +
      (∑ ps ∈ stopped w stop P.card (rootVertex z H P mu),
        ((ResidueSieveTree.survivorCount Y small a (H ∪ ps.toFinset,suffixPrimes P ps) : ℝ)-
          (mu/(ps.prod:ℝ))*referencePolynomial w (suffixPrimes P ps)
            (terminal w z ps).side (terminal w z ps).gap)) ≤
      (ResidueSieveTree.survivorCount Y small a (H,P) : ℝ) := by
  have h := actual_reference_error_lower_bound w Y small a stop P.card (rootVertex z H P mu) le_rfl hi
  simp only [root_after_mass,root_after_survivors,root_after_reference,after_scale_product] at h
  simpa only [countSurvivors_eq_tree_survivors,referenceValue,rootVertex] using h

end NumberTheoryLean.StoppedCountAdapters



namespace NumberTheoryLean.SourceStopPredicate

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeHistories ReferenceAdmission RepresentativeAdmission RepresentativeStopGeometry
open PrimeBinRepresentatives ActualSourceTags ActualBinOwners FiniteFirstTag
open ErdosInversePrimeBin ErdosInverseAlignment ErdosPrimeInputs.HarmonicPrimeMeasure
attribute [local instance] Classical.propDecidable

def sourceClass (a : ℕ → ℕ) (p : ℕ) : ℤ := a p

noncomputable def representative {n : ℕ} (w : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (p : ℕ) : ℝ := rightExponent w (lower (label p)) (width (label p))

def boxed {n : ℕ} (lower width : Fin n → ℝ) (label : ℕ → Fin n) (ps : List ℕ) : Prop :=
  ∀ p ∈ ps,p ∈ primeBin (lower (label p)) (width (label p))

def representativeSafe (w : ℝ) (rep : ℕ → ℝ) (z : Node) (Delta : ℝ) (ps : List ℕ) : Prop :=
  ∀ qs ∈ ps.inits,qs ≠ [] → (terminal w z qs).side = .even →
    sourceHeight (rep (qs.getLastD 0))+3*Delta ≤ representativeGap rep z.gap qs

noncomputable def representativeWindow (rep : ℕ → ℝ) (z : Node) (b₀ b₁ : ℝ) (ps : List ℕ) : Prop :=
  b₀ ≤ rep (ps.getLastD 0) ∧ rep (ps.getLastD 0) ≤ b₁ ∧
    206/100 ≤ representativeGap rep z.gap ps/rep (ps.getLastD 0) ∧
    representativeGap rep z.gap ps/rep (ps.getLastD 0) ≤ 216/100

noncomputable def stopCandidate {n : ℕ} (Y : ℕ) (w Cs eta Clen B xi b₀ b₁ : ℝ)
    (lower width : Fin n → ℝ) (label : ℕ → Fin n) (a : ℕ → ℕ) (z : Node) (ps : List ℕ) : Prop :=
  ps ≠ [] ∧ (ps.length:ℝ) ≤ Clen*Real.log B ∧ boxed lower width label ps ∧
    representativeSafe w (representative w lower width label) z (2*Clen*xi) ps ∧
    representativeWindow (representative w lower width label) z b₀ b₁ ps ∧
    ∃ t : Tag n,sourceTag (Y:ℝ) w Cs eta lower width label (sourceClass a) ps = some t ∧
      (ps.map label).count t.bin = 1 ∧ ∀ p ∈ ps,aligns (sourceClass a) t.rational p

theorem empty_not_candidate {n : ℕ} (Y : ℕ) (w Cs eta Clen B xi b₀ b₁ : ℝ)
    (lower width : Fin n → ℝ) (label : ℕ → Fin n) (a : ℕ → ℕ) (z : Node) :
    ¬stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z [] := by
  simp [stopCandidate]

theorem finite_safe_admits (w : ℝ) (rep : ℕ → ℝ) (z : Node) (Delta : ℝ) (ps : List ℕ)
    (hDelta : 0 ≤ Delta) (hrep : ∀ p ∈ ps,primeExponent w p ≤ rep p)
    (hs : representativeSafe w rep z Delta ps) : admitted w z.side z.gap ps := by
  apply representative_safety_preserves_admission w rep z ps hDelta hrep
  intro pre p tail heq hside
  have hmem : pre++[p] ∈ ps.inits := by
    apply (List.mem_inits _ _).mpr
    exact ⟨tail,by simpa only [List.append_assoc,List.singleton_append] using heq.symm⟩
  have h := hs (pre++[p]) hmem (by simp) hside
  rwa [List.getLastD_concat] at h

theorem candidate_admitted {n : ℕ} (Y : ℕ) (w Cs eta Clen B xi b₀ b₁ : ℝ)
    (lower width : Fin n → ℝ) (label : ℕ → Fin n) (a : ℕ → ℕ) (z : Node) (ps : List ℕ)
    (hw : 1 < w) (hC : 0 ≤ Clen) (hxi : 0 ≤ xi)
    (hlo : ∀ b,0 < lower b) (hwidth : ∀ b,0 ≤ width b)
    (hc : stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z ps) :
    admitted w z.side z.gap ps := by
  apply finite_safe_admits w (representative w lower width label) z (2*Clen*xi) ps (by positivity)
  · intro p hp
    exact (bin_exponent_bounds hw (hlo (label p)) (hwidth (label p)) (hc.2.2.1 p hp)).2
  · exact hc.2.2.2.1

theorem candidate_owner_witness {n : ℕ} (Y : ℕ) (w Cs eta Clen B xi b₀ b₁ : ℝ)
    (lower width : Fin n → ℝ) (label : ℕ → Fin n) (a : ℕ → ℕ) (z : Node) (ps : List ℕ)
    (hw : 1 < w) (hc : stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z ps) :
    ∃ t : Tag n,sourceTag (Y:ℝ) w Cs eta lower width label (sourceClass a) ps = some t ∧
      (ps.map label).count t.bin = 1 ∧ eligible (Y:ℝ) w Cs t.rational ∧
      (1-eta)*((primeBin (lower t.bin) (width t.bin)).card:ℝ) ≤
        (((primeBin (lower t.bin) (width t.bin)).filter (aligns (sourceClass a) t.rational)).card:ℝ) ∧
      ∀ p ∈ ps,aligns (sourceClass a) t.rational p := by
  obtain ⟨t,ht,hm,ha⟩ := hc.2.2.2.2.2
  obtain ⟨_pre,_p,_tail,_hps,_hidx,hbin,_hp,_hsearch,ho,_hpa,_hbefore⟩ :=
    sourceTag_witness (Y:ℝ) w Cs eta lower width label (sourceClass a) ps ht
  have hOwner := actual_owner_witness (Nat.cast_nonneg Y) hw (sourceClass a) ho
  rw [← hbin] at hOwner
  exact ⟨t,ht,hm,hOwner.1,hOwner.2,ha⟩

end NumberTheoryLean.SourceStopPredicate



namespace NumberTheoryLean.ActualTagFreezing

open ActualSourceTags FiniteFirstTag SourceStopPredicate ErdosInversePrimeBin ErdosInverseAlignment

theorem sourceTag_replacement {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (pre tail : List ℕ) (p p' : ℕ) {b : Fin n} {q : ℚ}
    (ht : tagCandidate Y w Cs eta lower width label a p = some (b,q))
    (hlabel : label p' = label p)
    (hp' : p' ∈ primeBin (lower (label p')) (width (label p'))) (ha : aligns a q p') :
    sourceTag Y w Cs eta lower width label a (pre++p::tail) =
      sourceTag Y w Cs eta lower width label a (pre++p'::tail) := by
  have hc := candidate_replacement Y w Cs eta lower width label a p p' ht hlabel hp' ha
  exact tag_replacement_invariant _ pre tail p p' hc.symm

theorem all_prefix_tags_replacement {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (pre tail : List ℕ) (p p' : ℕ) {b : Fin n} {q : ℚ}
    (ht : tagCandidate Y w Cs eta lower width label a p = some (b,q))
    (hlabel : label p' = label p)
    (hp' : p' ∈ primeBin (lower (label p')) (width (label p'))) (ha : aligns a q p') (k : ℕ) :
    sourceTag Y w Cs eta lower width label a ((pre++p::tail).take k) =
      sourceTag Y w Cs eta lower width label a ((pre++p'::tail).take k) := by
  have hc := candidate_replacement Y w Cs eta lower width label a p p' ht hlabel hp' ha
  apply tag_prefix_invariant
  simp only [List.map_append,List.map_cons,hc]

theorem replacement_labels {n : ℕ} (label : ℕ → Fin n) (pre tail : List ℕ) (p p' : ℕ)
    (hlabel : label p' = label p) : (pre++p::tail).map label = (pre++p'::tail).map label := by
  simp only [List.map_append,List.map_cons,hlabel]

theorem replacement_representatives {n : ℕ} (w : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (pre tail : List ℕ) (p p' : ℕ) (hlabel : label p' = label p) :
    (pre++p::tail).map (representative w lower width label) =
      (pre++p'::tail).map (representative w lower width label) := by
  simp only [List.map_append,List.map_cons,representative,hlabel]

theorem forall_mem_replacement_iff (A : ℕ → Prop) (pre tail : List ℕ) (p q : ℕ)
    (hp : A p) (hq : A q) :
    (∀ r ∈ pre++p::tail,A r) ↔ (∀ r ∈ pre++q::tail,A r) := by
  have h (p q : ℕ) (hq : A q) (H : ∀ r ∈ pre++p::tail,A r) : ∀ r ∈ pre++q::tail,A r := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact H r (List.mem_append.mpr (Or.inl hr))
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact hq
      · exact H r (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hr)))
  exact ⟨h p q hq,h q p hp⟩

end NumberTheoryLean.ActualTagFreezing


end Erdos970

end OAI
