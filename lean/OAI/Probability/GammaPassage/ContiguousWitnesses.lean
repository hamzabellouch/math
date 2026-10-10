import OAI.Probability.GammaPassage.SpatialPositiveChunk

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set

lemma trace_append (p : Vertex) (ds es : List Step) :
    trace p (ds++es)=trace p ds++trace (p+displacement ds) es := by
  induction ds generalizing p with
  | nil => simp [trace]
  | cons d ds ih => simp [trace,ih,add_assoc]

/-- A contiguous split of actual traversals is a split into actual paths. -/
lemma trace_split (p : Vertex) (ds : List Step) (xs ys : List Traversal)
    (h : trace p ds=xs++ys) :
    ∃ pre rest : List Step, ds=pre++rest ∧ trace p pre=xs ∧
      trace (p+displacement pre) rest=ys := by
  induction xs generalizing p ds with
  | nil => exact ⟨[],ds,rfl,rfl,by simpa using h⟩
  | cons x xs ih =>
    cases ds with
    | nil => simp [trace] at h
    | cons d ds =>
      obtain ⟨hx,ht⟩ := List.cons.inj h
      obtain ⟨pre,rest,he,hpre,hrest⟩ := ih (p+d.delta) ds ht
      refine ⟨d::pre,rest,by simp [he],?_,?_⟩
      · simp only [trace,hpre,hx]
      · simpa only [displacement_cons,add_assoc] using hrest

lemma trace_edges (p : Vertex) (ds : List Step) :
    ((trace p ds).map traversalEdge).toFinset=pathEdges p ds := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih => simp [trace,traversalEdge,pathEdges,ih]

lemma simple_append_edges (p : Vertex) (ds es : List Step)
    (h : ((trace p (ds++es)).map traversalEdge).Nodup) :
    ((trace p ds).map traversalEdge).Nodup ∧
    ((trace (p+displacement ds) es).map traversalEdge).Nodup ∧
    Disjoint (pathEdges p ds) (pathEdges (p+displacement ds) es) := by
  rw [trace_append,List.map_append,List.nodup_append] at h
  refine ⟨h.1,h.2.1,?_⟩
  rw [← trace_edges,← trace_edges]
  exact Finset.disjoint_left.mpr (fun e he hf =>
    h.2.2 e (List.mem_toFinset.mp he) e (List.mem_toFinset.mp hf) rfl)

/-- Source wi:chunk-defect. Construct actual labelled negative-prefix witnesses
inside the original box, with disjoint physical edges and the basic bound. -/
theorem spatial_negative_prefix_witnesses (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (b m₀ am ap K η : ℝ) (ha : am ≤ ap) (hη : 0 ≤ η)
    (k m : ℕ) (ih : ℤ×ℤ)
    (hscale : max |m₀-((am+ap)/2)*b| |(am+ap)/2| ≤ η*(2 : ℝ)^k)
    (p : Vertex) (ds : List Step)
    (hin : PathIn p ds {z | z-spatialTranslate b k m ih ∈ endpointBox b 4 4 k m})
    (hsimple : ((trace p ds).map traversalEdge).Nodup) :
    ∃ ws : List GammaFPP.BK.StrictPathWitness,
      ws.Pairwise (fun q r => Disjoint q.edges r.edges) ∧
      (∀ q ∈ ws, q ∈ spatialWitnessFamily b m₀ am ap K η k m ih ∧
        q.Good w ∧ q.edges ⊆ pathEdges p ds) ∧
      -η*(2 : ℝ)^k-2*η*(2 : ℝ)^k*ws.length ≤ defect w b m₀ ((am+ap)/2) p ds := by
  have hηs : 0 ≤ η*(2 : ℝ)^k := mul_nonneg hη (by positivity)
  induction hn : ds.length using Nat.strong_induction_on generalizing p ds with
  | h n rec =>
    by_cases hlo : -η*(2 : ℝ)^k ≤ defect w b m₀ ((am+ap)/2) p ds
    · exact ⟨[],by simp,by simp,by simpa using hlo⟩
    · have hstep : ∀ t ∈ trace p ds, -(η*(2 : ℝ)^k) ≤ stepDefect w b m₀ ((am+ap)/2) t := by
        intro t _
        have ht := hw (traversalEdge t)
        have hs := (support_step_bound b m₀ ((am+ap)/2) t.2).trans hscale
        unfold stepDefect
        linarith
      obtain ⟨xs,ys,he,hne,hxslo,hxshi⟩ := first_drop (stepDefect w b m₀ ((am+ap)/2))
        (η*(2 : ℝ)^k) (trace p ds) hstep 0 (by linarith)
        (by rw [trace_total_defect]; linarith)
      obtain ⟨pre,rest,heq,hpre,hrest⟩ := trace_split p ds xs ys he
      have hpreNe : pre ≠ [] := by intro hz; subst pre; simp [trace] at hpre; exact hne hpre
      have hlen : rest.length < n := by
        have hh := List.length_pos_iff.mpr hpreNe
        rw [heq,List.length_append] at hn
        omega
      have hsimp := simple_append_edges p pre rest (by rw [← heq]; exact hsimple)
      have hin' : PathIn p (pre++rest) {z | z-spatialTranslate b k m ih ∈ endpointBox b 4 4 k m} := by rw [← heq]; exact hin
      have hprelo : -2*(η*(2 : ℝ)^k) ≤ defect w b m₀ ((am+ap)/2) p pre := by
        rw [← trace_total_defect,hpre]; simpa using hxslo
      have hprehi : defect w b m₀ ((am+ap)/2) p pre < -η*(2 : ℝ)^k := by
        rw [← trace_total_defect,hpre]; simpa [neg_mul] using hxshi
      obtain ⟨q,hq,hqs,hqd,hqg⟩ := negative_midpoint_spatial_witness w b m₀ am ap K η ha k m ih p pre
        (pathIn_append_left p pre rest _ hin') hprehi
      have hqe : q.edges=pathEdges p pre := by change pathEdges q.start q.steps=_; rw [hqs,hqd]
      obtain ⟨ws,hpair,hws,hbound⟩ := rec rest.length hlen (p+displacement pre) rest
        (pathIn_append_right p pre rest _ hin') hsimp.2.1 rfl
      refine ⟨q::ws,List.pairwise_cons.mpr ⟨?_,hpair⟩,?_,?_⟩
      · intro r hr
        rw [hqe]
        exact hsimp.2.2.mono_right (hws r hr).2.2
      · intro r hr
        rw [heq,pathEdges_append]
        rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨hq,hqg,by rw [hqe]; exact Finset.subset_union_left⟩
        · exact ⟨(hws r hr).1,(hws r hr).2.1,(hws r hr).2.2.trans Finset.subset_union_right⟩
      · rw [heq,defect_append]
        simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
        nlinarith

end GammaFPP.CrossingBridge

end OAI
