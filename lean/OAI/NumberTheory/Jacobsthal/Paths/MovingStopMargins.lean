import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.Jacobsthal.Sieve.LastPrimeModulusCount

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ActualSourceStopBinding

open _root_.Finset
open FinitePathGeometry PrimeHistories SourceStopPredicate StoppedCountVertex StoppedEvaluation
open StoppedVertexHistory StoppedTraceSets StoppedCountAdapters StoppedModulusCount FlatStoppedIdentity
open ReferenceAdmission ReferencePruning ErdosInverseCounts
attribute [local instance] Classical.propDecidable

theorem actual_source_stops_first {n : ℕ} (Y : ℕ) (w Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (lower width : Fin n → ℝ) (label : ℕ → Fin n) (a : ℕ → ℕ) (z : Node) (P : Finset ℕ)
    {ps : List ℕ}
    (hp : ps ∈ stopped w (stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z)
      P.card (rootVertex z ∅ P mu)) :
    (terminal w z ps).side = .even ∧
      stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z ps ∧
      ∀ pre tail : List ℕ,ps = pre++tail → tail ≠ [] →
        ¬((terminal w z pre).side = .even ∧
          stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z pre) := by
  have h := FirstStopSemantics.stopped_first w
    (stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z) P.card (rootVertex z ∅ P mu) hp
  simpa only [FirstStopSemantics.FirstStop,lowerStop,after_node,after_past,rootVertex,List.nil_append,and_assoc] using h

theorem actual_source_stopped_lower {n : ℕ} (Y : ℕ) (small P : Finset ℕ)
    (w Cs eta Clen B xi b₀ b₁ mu : ℝ) (lower width : Fin n → ℝ) (label : ℕ → Fin n)
    (a : ℕ → ℕ) (z : Node) (hi : z.side = .even) :
    stoppedCount w Y small a (stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z)
      P.card (rootVertex z ∅ P mu) ≤ (ResidueSieveTree.survivorCount Y small a (∅,P):ℝ) := by
  have h := StoppedCountLowerBound.actual_stopped_lower_bound w Y small a
    (stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z) (rootVertex z ∅ P mu) hi
  simpa only [countSurvivors_eq_tree_survivors,rootVertex] using h

theorem actual_source_stopped_comparison {n : ℕ} (Y : ℕ) (small P : Finset ℕ)
    (w Cs eta Clen B xi b₀ b₁ mu : ℝ) (lower width : Fin n → ℝ) (label : ℕ → Fin n)
    (a : ℕ → ℕ) (z : Node) (hi : z.side = .even) (hP : ∀ p ∈ P,Nat.Prime p) :
    let stop := stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z
    let v := rootVertex z ∅ P mu
    stoppedCount w Y small a stop P.card v-mu*referencePolynomial w P z.side z.gap =
      (∑ ps ∈ expanded w stop P.card v,(-1:ℝ)^ps.length*
        ((modulusCount Y small a ps.prod:ℝ)-mu/(ps.prod:ℝ))) +
      (∑ ps ∈ stopped w stop P.card v,
        ((ResidueSieveTree.survivorCount Y small a (ps.prod.primeFactors,suffixPrimes P ps):ℝ)-
          (mu/(ps.prod:ℝ))*referencePolynomial w (suffixPrimes P ps)
            (terminal w z ps).side (terminal w z ps).gap)) := by
  dsimp only
  let stop := stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z
  let v := rootVertex z ∅ P mu
  change stoppedCount w Y small a stop P.card v-referenceValue w v = _
  rw [literal_stopped_difference w Y small a stop P.card v le_rfl hi]
  congr 1
  · apply Finset.sum_congr rfl
    intro ps hp
    rw [trace_mass_eq_modulusCount w Y small P a z mu stop P.card hP (Or.inl hp),after_scale_product]
    rfl
  · apply Finset.sum_congr rfl
    intro ps hp
    rw [trace_survivors_eq_product_node w Y small P a z mu stop P.card hP (Or.inr hp),root_after_reference]

end NumberTheoryLean.ActualSourceStopBinding

end

section

namespace NumberTheoryLean.FirstStopFreezing
open FinitePathGeometry PrimeHistories SourceStopPredicate ActualSourceTags FiniteFirstTag
open SourceCandidateFreezing RepresentativeTraceInvariance
open StoppedCountVertex StoppedVertexHistory StoppedEvaluation StoppedCountAdapters FirstStopSemantics
open ErdosInversePrimeBin ErdosInverseAlignment

theorem firstStop_iff_takes (w : ℝ) (stop : List ℕ → Prop) (v : Vertex) (ps : List ℕ) :
    FirstStop w stop v ps ↔ lowerStop stop (after w v ps) ∧
      ∀ k < ps.length,¬lowerStop stop (after w v (ps.take k)) := by
  constructor
  · intro h
    refine ⟨h.1,?_⟩
    intro k hk
    apply h.2 (ps.take k) (ps.drop k) (List.take_append_drop k ps).symm
    intro hz
    have hh := congrArg List.length hz
    simp only [List.length_drop,List.length_nil] at hh
    omega
  · rintro ⟨h,hs⟩
    refine ⟨h,?_⟩
    intro pre tail heq htail
    have htpos : 0 < tail.length := List.length_pos_iff.mpr htail
    have hlen : pre.length < ps.length := by rw [heq,List.length_append]; omega
    have hh := hs pre.length hlen
    simpa only [heq,List.take_append,List.take_length,Nat.sub_self,List.take_zero,List.append_nil] using hh

theorem first_source_stop_replacement {n : ℕ} (Y : ℕ) (w Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (lower width : Fin n → ℝ) (label : ℕ → Fin n) (a : ℕ → ℕ) (z : Node) (P : Finset ℕ)
    (pre tail : List ℕ) (p p' : ℕ) {t : Tag n}
    (ht : sourceTag (Y:ℝ) w Cs eta lower width label (sourceClass a) (pre++p::tail) = some t)
    (hc : tagCandidate (Y:ℝ) w Cs eta lower width label (sourceClass a) p = some (t.bin,t.rational))
    (hlabel : label p' = label p)
    (hp' : p' ∈ primeBin (lower (label p')) (width (label p')))
    (ha' : aligns (sourceClass a) t.rational p') :
    FirstStop w (stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z)
      (rootVertex z ∅ P mu) (pre++p::tail) ↔
    FirstStop w (stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z)
      (rootVertex z ∅ P mu) (pre++p'::tail) := by
  let stop := stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z
  let v := rootVertex z ∅ P mu
  have hlen : (pre++p::tail).length = (pre++p'::tail).length := by simp
  have he (k : ℕ) : lowerStop stop (after w v ((pre++p::tail).take k)) ↔
      lowerStop stop (after w v ((pre++p'::tail).take k)) := by
    have hside := terminal_side_length w z z ((pre++p::tail).take k) ((pre++p'::tail).take k) rfl
      (by simp only [List.length_take,hlen])
    have hh := all_prefix_candidate_replacement Y w Cs eta Clen B xi b₀ b₁ lower width label a z
      pre tail p p' ht hc hlabel hp' ha' k
    simp only [lowerStop,after_node,after_past,v,rootVertex,List.nil_append,hside]
    exact and_congr_right (fun _ => hh)
  have hlast := he (pre++p::tail).length
  simp only [List.take_length] at hlast
  rw [hlen,List.take_length] at hlast
  rw [firstStop_iff_takes,firstStop_iff_takes]
  change (lowerStop stop (after w v (pre++p::tail)) ∧ _) ↔
    (lowerStop stop (after w v (pre++p'::tail)) ∧ _)
  rw [hlast]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro k
  rw [hlen,he k]
end NumberTheoryLean.FirstStopFreezing

end

section

namespace NumberTheoryLean.StoppedTraceMembership
open FinitePathGeometry PrimeHistories StoppedCountVertex StoppedVertexHistory StoppedEvaluation
open StoppedTraceSets StoppedTraceAdmission FirstStopSemantics ReferenceAdmission ReferencePruning
open ReferencePrefixRecurrence ErdosPrimeInputs.PrimePrefixMass
attribute [local instance] Classical.propDecidable

theorem reference_cons_iff (w : ℝ) (v : Vertex) (p : ℕ) (ps : List ℕ) :
    p::ps ∈ referencePrefixes w v.available v.node.side v.node.gap ↔
    p ∈ includedPrimes w v ∧ ps ∈ referencePrefixes w (child w v p).available
      (child w v p).node.side (child w v p).node.gap := by
  constructor
  · intro h
    obtain ⟨hD,hA⟩ := Finset.mem_filter.mp h
    have hp := (mem_decreasingPrefixes.mp hD).2 p (by simp)
    have htail := (append_mem_decreasing_iff (singleton_prefix_mem hp)).mp hD
    refine ⟨Finset.mem_filter.mpr ⟨hp,hA.1⟩,Finset.mem_filter.mpr ⟨?_,hA.2⟩⟩
    simpa only [suffixPrimes,List.mem_singleton,forall_eq,child] using htail
  · rintro ⟨hp,hps⟩
    exact reference_child_cons w v hp hps

theorem stopped_length (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    {ps : List ℕ} (hp : ps ∈ stopped w stop n v) : ps.length ≤ n := by
  induction n generalizing v ps with
  | zero =>
    by_cases hs : lowerStop stop v
    · have he : ps=[] := by simpa only [stopped,traces,hs,ite_true,Finset.mem_singleton] using hp
      simp [he]
    · simp [stopped,traces,hs] at hp
  | succ n ih =>
    by_cases hs : lowerStop stop v
    · have he : ps=[] := by simpa only [stopped,traces,hs,ite_true,Finset.mem_singleton] using hp
      simp [he]
    · simp only [stopped,traces,hs,ite_false] at hp
      obtain ⟨p,_hp,hps⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨tail,ht,rfl⟩ := Finset.mem_image.mp hps
      exact Nat.succ_le_succ (ih (child w v p) ht)

theorem stopped_of_reference_first (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    (ps : List ℕ) (hlen : ps.length ≤ n)
    (href : ps ∈ referencePrefixes w v.available v.node.side v.node.gap)
    (hf : FirstStop w stop v ps) : ps ∈ stopped w stop n v := by
  induction ps generalizing n v with
  | nil =>
    have hs : lowerStop stop v := hf.1
    cases n <;> simp [stopped,traces,hs]
  | cons p ps ih =>
    obtain ⟨hp,ht⟩ := (reference_cons_iff w v p ps).mp href
    have hroot : ¬lowerStop stop v := hf.2 [] (p::ps) rfl (by simp)
    have hfirst : FirstStop w stop (child w v p) ps := by
      refine ⟨hf.1,?_⟩
      intro pre tail heq htail
      exact hf.2 (p::pre) tail (by simp only [List.cons_append,heq]) htail
    cases n with
    | zero => simp at hlen
    | succ n =>
      have hh := ih n (child w v p) (by simpa using hlen) ht hfirst
      simp only [stopped,traces,hroot,ite_false]
      exact Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_image.mpr ⟨ps,hh,rfl⟩⟩

theorem stopped_iff_reference_first (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    (ps : List ℕ) : ps ∈ stopped w stop n v ↔ ps.length ≤ n ∧
      ps ∈ referencePrefixes w v.available v.node.side v.node.gap ∧ FirstStop w stop v ps := by
  exact ⟨fun h => ⟨stopped_length w stop n v h,
    trace_reference_member w stop n v (Or.inr h),stopped_first w stop n v h⟩,
    fun h => stopped_of_reference_first w stop n v ps h.1 h.2.1 h.2.2⟩
end NumberTheoryLean.StoppedTraceMembership

end

section

namespace NumberTheoryLean.TagBelowStopWindow
open _root_.Filter FinitePathGeometry PrimeHistories SourceStopPredicate ActualSourceTags FiniteFirstTag
open PrimeBinRepresentatives ErdosInversePrimeBin ErdosInverseAlignment

theorem source_tag_nonterminal {n : ℕ} (Y : ℕ) (w Cs eta Clen B xi b₀ b₁ : ℝ)
    (lower width : Fin n → ℝ) (label : ℕ → Fin n) (a : ℕ → ℕ) (z : Node)
    (pre tail : List ℕ) (p : ℕ) {t : Tag n}
    (hw : 1 < w) (hlo : ∀ b,0 < lower b) (hwidth : ∀ b,0 ≤ width b)
    (hwindow : b₁ < w^((1/4:ℝ)))
    (hc : tagCandidate (Y:ℝ) w Cs eta lower width label (sourceClass a) p = some (t.bin,t.rational))
    (hs : stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z (pre++p::tail)) :
    tail ≠ [] := by
  intro ht
  subst tail
  have hh := candidate_witness (Y:ℝ) w Cs eta lower width label (sourceClass a) p hc
  have hb := bin_exponent_bounds hw (hlo (label p)) (hwidth (label p)) hh.2.1
  have hr : representative w lower width label p ≤ b₁ := by
    have hx := hs.2.2.2.2.1.2.1
    simpa only [List.getLastD_concat] using hx
  have hsearch := hh.2.2.1
  change w^((1/4:ℝ)) ≤ leftExponent w (lower (label p)) at hsearch
  change rightExponent w (lower (label p)) (width (label p)) ≤ b₁ at hr
  linarith

theorem moving_window_below_search (rho K : ℝ) (hrho : 0 < rho) (hK : 0 < K) :
    ∀ᶠ w : ℝ in atTop,rho*K*(Real.log w)^2 < w^((1/4:ℝ)) := by
  have hC : 0 < rho*K := mul_pos hrho hK
  have hh := (isLittleO_log_rpow_rpow_atTop (s := (1/4:ℝ)) 2 (by norm_num)).bound
    (by positivity : (0:ℝ)<1/(2*(rho*K)))
  filter_upwards [hh,eventually_gt_atTop (0:ℝ)] with w hw hw0
  have hp : 0 < w^((1/4:ℝ)) := Real.rpow_pos_of_pos hw0 _
  rw [Real.rpow_two,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),abs_of_pos hp] at hw
  have hm := mul_le_mul_of_nonneg_left hw hC.le
  have he : (rho*K)*(1/(2*(rho*K))*w^((1/4:ℝ))) = w^((1/4:ℝ))/2 := by field_simp
  rw [he] at hm
  exact hm.trans_lt (by linarith)

theorem replacement_product (pre tail : List ℕ) (p : ℕ) :
    (pre++p::tail).prod=p*(pre.prod*tail.prod) := by
  rw [List.prod_append,List.prod_cons]
  ac_rfl

theorem replacement_last_and_scale (w : ℝ) (v : StoppedCountVertex.Vertex)
    (pre middle : List ℕ) (p u : ℕ) :
    (pre++p::(middle++[u])).getLastD 0=u ∧
    (StoppedVertexHistory.after w v (pre++p::(middle++[u]))).scale =
      v.scale/((p:ℝ)*(pre.prod*(middle++[u]).prod:ℕ)) := by
  constructor
  · simpa only [List.cons_append,List.append_assoc] using
      (show ((pre++p::middle)++[u]).getLastD 0=u from List.getLastD_concat)
  · rw [StoppedVertexHistory.after_scale_product,replacement_product,Nat.cast_mul]
end NumberTheoryLean.TagBelowStopWindow

end

section

namespace NumberTheoryLean.StoppedPrefixExistence
open StoppedCountVertex StoppedVertexHistory StoppedEvaluation StoppedTraceSets StoppedTraceMembership
open ReferenceAdmission ErdosPrimeInputs.PrimePrefixMass
attribute [local instance] Classical.propDecidable

theorem reference_length_le_card (w : ℝ) (v : Vertex) (ps : List ℕ)
    (hp : ps ∈ referencePrefixes w v.available v.node.side v.node.gap) : ps.length ≤ v.available.card := by
  have hd := mem_decreasingPrefixes.mp (Finset.mem_filter.mp hp).1
  have hn : ps.Nodup := hd.1.imp (fun h => ne_of_gt h)
  have hsub : ps.toFinset ⊆ v.available := fun p hp => hd.2 p (List.mem_toFinset.mp hp)
  have hh := Finset.card_le_card hsub
  simpa only [List.toFinset_card_of_nodup hn] using hh

theorem exists_stopped_prefix (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex) (ps : List ℕ)
    (hlen : ps.length ≤ n) (href : ps ∈ referencePrefixes w v.available v.node.side v.node.gap)
    (hhit : ∃ pre tail : List ℕ,ps=pre++tail ∧ lowerStop stop (after w v pre)) :
    ∃ pre tail : List ℕ,ps=pre++tail ∧ pre ∈ stopped w stop n v := by
  induction ps generalizing n v with
  | nil =>
    obtain ⟨pre,tail,heq,hs⟩ := hhit
    have hp : pre=[] := (List.append_eq_nil_iff.mp heq.symm).1
    subst pre
    refine ⟨[],[],rfl,?_⟩
    cases n <;> simp [stopped,traces,show lowerStop stop v from hs]
  | cons p ps ih =>
    by_cases hs : lowerStop stop v
    · refine ⟨[],p::ps,rfl,?_⟩
      cases n <;> simp [stopped,traces,hs]
    · obtain ⟨hp,htail⟩ := (reference_cons_iff w v p ps).mp href
      have hchildHit : ∃ pre tail : List ℕ,ps=pre++tail ∧ lowerStop stop (after w (child w v p) pre) := by
        obtain ⟨pre,tail,heq,hstop⟩ := hhit
        cases pre with
        | nil => exact False.elim (hs hstop)
        | cons q pre =>
          rw [List.cons_append] at heq
          have he := List.cons.inj heq
          have hehead := he.1
          subst q
          exact ⟨pre,tail,he.2,hstop⟩
      cases n with
      | zero => simp at hlen
      | succ n =>
        obtain ⟨pre,tail,heq,hpre⟩ := ih n (child w v p) (by simpa using hlen) htail hchildHit
        refine ⟨p::pre,tail,by simp only [List.cons_append,heq],?_⟩
        simp only [stopped,traces,hs,ite_false]
        exact Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_image.mpr ⟨pre,hpre,rfl⟩⟩

theorem reference_candidate_forces_stop (w : ℝ) (stop : List ℕ → Prop) (v : Vertex) (ps : List ℕ)
    (href : ps ∈ referencePrefixes w v.available v.node.side v.node.gap)
    (hhit : ∃ pre tail : List ℕ,ps=pre++tail ∧ lowerStop stop (after w v pre)) :
    ∃ pre tail : List ℕ,ps=pre++tail ∧ pre ∈ stopped w stop v.available.card v :=
  exists_stopped_prefix w stop v.available.card v ps (reference_length_le_card w v ps href) href hhit
end NumberTheoryLean.StoppedPrefixExistence

end

section

namespace NumberTheoryLean.ActualFrozenStopFamily
open FinitePathGeometry PrimeHistories SourceStopPredicate ActualSourceTags FiniteFirstTag
open StoppedCountVertex StoppedVertexHistory StoppedEvaluation StoppedCountAdapters StoppedTraceSets
open FirstStopSemantics StoppedTraceAdmission StoppedTraceMembership FirstStopFreezing
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open BinReplacementOrder ReferenceAdmission ActualSourceStopBinding ErdosInversePrimeBin ErdosInverseAlignment
open ErdosPrimeInputs.PrimePrefixMass
attribute [local instance] Classical.propDecidable

theorem actual_stopped_replacement (Y : ℕ) (w top Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (hw : 1 < w) (hwtop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen)
    (a : ℕ → ℕ) (z : Node) (pre tail : List ℕ) (p p' : ℕ)
    {t : Tag (binCount w top xi)}
    (hs : pre++p::tail ∈ stopped w
      (stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) hwtop hxi) a z)
      (sourcePrimeSet w top).card (rootVertex z ∅ (sourcePrimeSet w top) mu))
    (ht : sourceTag (Y:ℝ) w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) hwtop hxi) (sourceClass a) (pre++p::tail) = some t)
    (hc : tagCandidate (Y:ℝ) w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) hwtop hxi) (sourceClass a) p = some (t.bin,t.rational))
    (hp' : p' ∈ primeBin (lower w top xi t.bin) (width w top xi t.bin))
    (ha' : aligns (sourceClass a) t.rational p') :
    pre++p'::tail ∈ stopped w
      (stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) hwtop hxi) a z)
      (sourcePrimeSet w top).card (rootVertex z ∅ (sourcePrimeSet w top) mu) := by
  let lo := lower w top xi
  let wi := width w top xi
  let lab := label (zero_lt_one.trans hw) hwtop hxi
  let P := sourcePrimeSet w top
  let stop := stopCandidate Y w Cs eta Clen B xi b₀ b₁ lo wi lab a z
  let v := rootVertex z ∅ P mu
  have hw0 : 0 < w := zero_lt_one.trans hw
  have htag := candidate_witness (Y:ℝ) w Cs eta lo wi lab (sourceClass a) p hc
  have hnew := (bin_mem_iff_label hw0 hwtop hxi t.bin p').mp hp'
  have hlabel : lab p' = lab p := hnew.2.2.2.trans htag.1
  have hp'own : p' ∈ primeBin (lo (lab p')) (wi (lab p')) := by
    change p' ∈ primeBin (lower w top xi (lab p')) (width w top xi (lab p'))
    have hnewlabel : lab p' = t.bin := hnew.2.2.2
    rw [hnewlabel]
    exact hp'
  have hp'S : p' ∈ P := (mem_sourcePrimeSet hw0 hwtop p').mpr ⟨hnew.1,hnew.2.1,hnew.2.2.1⟩
  have href := trace_reference_member w stop P.card v (Or.inr hs)
  have hD := mem_decreasingPrefixes.mp (Finset.mem_filter.mp href).1
  have hall : ∀ q ∈ pre++p::tail,q ∈ P := hD.2
  have hf := stopped_first w stop P.card v hs
  have hcand : stop (pre++p::tail) := by
    have hh := hf.1.2
    simpa only [after_past,v,rootVertex,List.nil_append] using hh
  have hcount : ((pre++p::tail).map lab).count (lab p)=1 := by
    obtain ⟨u,hu,huCount,_huAlign⟩ := hcand.2.2.2.2.2
    have hut : u=t := Option.some.inj (hu.symm.trans ht)
    subst u
    rw [← htag.1]
    exact huCount
  have hdec := (decreasing_replacement hw0 hwtop hxi pre tail p p' hall hp'S hlabel hcount).mp hD.1
  have hfirst : FirstStop w stop v (pre++p'::tail) :=
    (first_source_stop_replacement Y w Cs eta Clen B xi b₀ b₁ mu lo wi lab a z P pre tail p p'
      ht hc hlabel hp'own ha').mp hf
  have hnewCand : stop (pre++p'::tail) := by
    have hh := hfirst.1.2
    simpa only [after_past,v,rootVertex,List.nil_append] using hh
  have hadmit := candidate_admitted Y w Cs eta Clen B xi b₀ b₁ lo wi lab a z (pre++p'::tail)
    hw hC hxi.le (fun i => endpoint_pos hw0 _) (fun i => (effectiveWidth_pos hw0 hwtop hxi).le) hnewCand
  have hmem : ∀ q ∈ pre++p'::tail,q ∈ P :=
    (ActualTagFreezing.forall_mem_replacement_iff (fun q => q ∈ P) pre tail p p'
      (hall p (by simp)) hp'S).mp hall
  apply stopped_of_reference_first w stop P.card v (pre++p'::tail)
  · have hl := stopped_length w stop P.card v hs
    simpa only [List.length_append,List.length_cons] using hl
  · exact Finset.mem_filter.mpr ⟨mem_decreasingPrefixes.mpr ⟨hdec,hmem⟩,hadmit⟩
  · exact hfirst

theorem stopped_has_full_frozen_group (Y : ℕ) (w top Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (hw : 1 < w) (hwtop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen)
    (a : ℕ → ℕ) (z : Node) (ps : List ℕ)
    (hs : ps ∈ stopped w
      (stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) hwtop hxi) a z)
      (sourcePrimeSet w top).card (rootVertex z ∅ (sourcePrimeSet w top) mu)) :
    ∃ pre tail : List ℕ,∃ p : ℕ,∃ t : Tag (binCount w top xi),
      ps=pre++p::tail ∧ t.index=pre.length ∧
      sourceTag (Y:ℝ) w Cs eta (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) hwtop hxi) (sourceClass a) ps=some t ∧
      ∀ p' ∈ primeBin (lower w top xi t.bin) (width w top xi t.bin),
        aligns (sourceClass a) t.rational p' →
        pre++p'::tail ∈ stopped w
          (stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
            (label (zero_lt_one.trans hw) hwtop hxi) a z)
          (sourcePrimeSet w top).card (rootVertex z ∅ (sourcePrimeSet w top) mu) := by
  have hfull := actual_source_stops_first Y w Cs eta Clen B xi b₀ b₁ mu (lower w top xi)
    (width w top xi) (label (zero_lt_one.trans hw) hwtop hxi) a z (sourcePrimeSet w top) hs
  obtain ⟨t,ht,_hc,_ha⟩ := hfull.2.1.2.2.2.2.2
  obtain ⟨pre,p,tail,heq,hindex,hcand,_hpre⟩ := firstTagFrom_witness
    (tagCandidate (Y:ℝ) w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) hwtop hxi) (sourceClass a)) 0 ps ht
  refine ⟨pre,tail,p,t,heq,by simpa using hindex,ht,?_⟩
  intro p' hp' ha'
  subst ps
  exact actual_stopped_replacement Y w top Cs eta Clen B xi b₀ b₁ mu hw hwtop hxi hC a z pre tail p p'
    hs ht hcand hp' ha'
end NumberTheoryLean.ActualFrozenStopFamily

end

section

namespace NumberTheoryLean.MovingStopMargins
open _root_.Filter MarkedSourceSmallness TagBelowStopWindow

theorem moving_stop_margins (Cs Clen xi : ℝ) (hxi : 0 < xi)
    {rho K : ℝ} (hrho : 0 < rho) (hK : 0 < K) :
    ∀ᶠ w : ℝ in atTop,1 < w ∧ 1 ≤ Real.log w ∧
      0 < K*(Real.log w)^2 ∧ Cs < 2*(K*(Real.log w)^2) ∧
      rho*K*(Real.log w)^2 < w^((1/4:ℝ)) ∧
      xi/Real.log w ≤ K*(Real.log w)^2 ∧
      2*Clen*xi+(206/100)*(xi/Real.log w) ≤ (4/100)*(K*(Real.log w)^2) ∧
      ∀ B : ℝ,w ≤ B → (rho*K*(Real.log w)^2)/2 < B := by
  let M := max xi (max (Cs+1) (max 1 (25*(2*Clen*xi+(206/100)*xi)+1)))
  filter_upwards [moving_compact_gap_small (6*M) hK,
    moving_window_below_search rho K hrho hK,
    Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_gt_atTop (1:ℝ)] with w hm hs hlog hw
  have hb : M < K*(Real.log w)^2 := by linarith
  have hxiM : xi ≤ M := le_max_left _ _
  have hCsM : Cs+1 ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hOneM : 1 ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hNumM : 25*(2*Clen*xi+(206/100)*xi)+1 ≤ M :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hdiv : xi/Real.log w ≤ xi := div_le_self hxi.le hlog
  refine ⟨hw,hlog,by linarith,by linarith,hs,by linarith,by linarith,?_⟩
  intro B hB
  have hpow : w^((1/4:ℝ)) ≤ w := by
    calc
      _ ≤ w^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hw.le (by norm_num)
      _ = w := Real.rpow_one w
  have hb₁ : 0 < rho*K*(Real.log w)^2 := by positivity
  linarith
end NumberTheoryLean.MovingStopMargins

end

end Erdos970

end OAI
