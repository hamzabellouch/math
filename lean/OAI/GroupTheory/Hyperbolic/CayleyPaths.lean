import OAI.GroupTheory.Hyperbolic.CayleyMetric

namespace OAI

namespace Release075.BlockPresentation
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

/-- The original edge is based using the fixed two-edge spanning tree. -/
def generatorWord : d.Edge → List d.OrientedEdge
  | .inl e => [(d.treeL,true),(.inl e,true),(d.treeR,false)]
  | .inr (.inl e) => [(.inr (.inl e),true),(d.treeL,false)]
  | .inr (.inr e) => [(.inr (.inr e),true),(d.treeR,false)]

theorem generatorWord_typed (e : d.Edge) :
    WordPath d.flipEdge d.edgeTarget .o .o (d.generatorWord e) := by
  rcases e with e | e | e
  · exact WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (d.treeL,true)
      (WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (Sum.inl e,true)
        (WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (d.treeR,false) (WordPath.nil Vertex.o)))
  · exact WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget)
      (.inr (.inl e),true) (WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (d.treeL,false) (WordPath.nil Vertex.o))
  · exact WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget)
      (.inr (.inr e),true) (WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (d.treeR,false) (WordPath.nil Vertex.o))

@[simp] theorem generatorWord_value (e : d.Edge) : d.wordValue (d.generatorWord e) = d.edge e := by
  rcases e with e | e | e <;>
    simp [generatorWord,edgeValue,d.treeL_eq_one,d.treeR_eq_one]

theorem generatorWord_length (e : d.Edge) : (d.generatorWord e).length ≤ 3 := by
  rcases e with e | e | e <;> simp [generatorWord]

/-- Collapsed tree edges have zero integral, leaving precisely the Cayley edge. -/
theorem generatorWord_integral (e : d.Edge) (g o a : d.GroupType) (T : ℕ) :
    ((d.liftWord g (d.generatorWord e)).map (d.liftedForm o a T)).sum =
      d.cayleyMetric.form o a T g (g*d.edge e) := by
  rcases e with e | e | e <;>
    simp [generatorWord,liftWord,liftedForm,liftedFlip,edgeValue,
      d.treeL_eq_one,d.treeR_eq_one,Discrete.Metric.form_self]

theorem liftedForm_reverse (w : List d.LiftedEdge) (o a : d.GroupType) (T : ℕ) :
    ((reverseWord d.liftedFlip w).map (d.liftedForm o a T)).sum =
      -(w.map (d.liftedForm o a T)).sum := by
  induction w with
  | nil => simp
  | cons e w ih =>
    rw [reverseWord_cons,List.map_append,List.sum_append,ih]
    simp only [d.liftedForm_flip,List.map_cons,List.sum_cons]
    abel

theorem exists_generator_step (g : d.GroupType) (e : d.Edge) :
    ∃ w : List d.LiftedEdge,
      WordPath d.liftedFlip d.liftedTarget (.o,g) (.o,g*d.edge e) w ∧
      w.length ≤ 3 ∧ ∀ (o a : d.GroupType) (T : ℕ),
        (w.map (d.liftedForm o a T)).sum = d.cayleyMetric.form o a T g (g*d.edge e) := by
  refine ⟨d.liftWord g (d.generatorWord e),?_,?_,d.generatorWord_integral e g⟩
  · simpa only [generatorWord_value] using d.liftWord_typed (d.generatorWord_typed e) g
  · simpa only [liftWord_length] using d.generatorWord_length e

theorem exists_cayley_step {g h : d.GroupType} (hgh : d.cayleyMetric.dist g h ≤ 1) :
    ∃ w : List d.LiftedEdge,
      WordPath d.liftedFlip d.liftedTarget (.o,g) (.o,h) w ∧
      w.length ≤ 3 ∧ ∀ (o a : d.GroupType) (T : ℕ),
        (w.map (d.liftedForm o a T)).sum = d.cayleyMetric.form o a T g h := by
  by_cases he : g = h
  · subst h
    exact ⟨[],.nil _,by simp,fun o a T => by simp [Discrete.Metric.form_self]⟩
  have hadj : d.cayley.Adj g h := by
    apply d.cayley.dist_eq_one_iff_adj.mp
    have hpos := d.cayley_connected.pos_dist_of_ne he
    change d.cayley.dist g h ≤ 1 at hgh
    exact Nat.le_antisymm hgh hpos
  obtain ⟨_,v,⟨e,rfl⟩,he|he⟩ := (SimpleGraph.mulCayley_adj' _ _ _).mp hadj
  · subst h
    exact d.exists_generator_step g e
  · subst g
    obtain ⟨w,hw,hlen,hwF⟩ := d.exists_generator_step h e
    refine ⟨reverseWord d.liftedFlip w,hw.reverse d.liftedFlip_flip,?_,?_⟩
    · simpa only [reverseWord,List.length_map,List.length_reverse] using hlen
    · intro o a T
      rw [d.liftedForm_reverse,hwF,d.cayleyMetric.form_flip,neg_neg]

theorem exists_path_word {g h : d.GroupType} (p : Discrete.Path d.cayleyMetric g h) :
    ∃ w : List d.LiftedEdge,
      WordPath d.liftedFlip d.liftedTarget (.o,g) (.o,h) w ∧
      w.length ≤ 3*p.length ∧ ∀ (o a : d.GroupType) (T : ℕ),
        (w.map (d.liftedForm o a T)).sum = p.integral (d.cayleyMetric.form o a T) := by
  have hprefix : ∀ n, n ≤ p.length → ∃ w : List d.LiftedEdge,
      WordPath d.liftedFlip d.liftedTarget (.o,p.point 0) (.o,p.point n) w ∧
      w.length ≤ 3*n ∧ ∀ (o a : d.GroupType) (T : ℕ),
        (w.map (d.liftedForm o a T)).sum =
          ∑ i ∈ Finset.range n, d.cayleyMetric.form o a T (p.point i) (p.point (i+1)) := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨[],.nil _,by simp,fun o a T => by simp⟩
    | succ n ih =>
      intro hn
      obtain ⟨u,hu,hulen,huF⟩ := ih (by omega)
      obtain ⟨v,hv, hvlen,hvF⟩ := d.exists_cayley_step (p.step n (by omega))
      refine ⟨u++v,hu.append hv,?_,?_⟩
      · rw [List.length_append]
        omega
      · intro o a T
        rw [List.map_append,List.sum_append,huF,hvF,Finset.sum_range_succ]
  obtain ⟨w,hw,hlen,hF⟩ := hprefix p.length le_rfl
  exact ⟨w,by simpa only [p.zero,p.last] using hw,hlen,hF⟩

end Release075.BlockPresentation

end OAI
