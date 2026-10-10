import OAI.GroupTheory.Hyperbolic.ThinTriangles

namespace OAI

namespace Release075.Discrete
variable {V : Type} (X : SimpleGraph V) (hX : X.Connected)

noncomputable def graphMetric : Metric V where
  dist := X.dist
  self _ := X.dist_self
  symm _ _ := X.dist_comm
  triangle _ _ _ := hX.dist_triangle

noncomputable def walkPath {a b : V} (p : X.Walk a b) : Path (graphMetric X hX) a b where
  length := p.length
  point := p.getVert
  zero := p.getVert_zero
  stable _ h := p.getVert_of_length_le h
  step _ h := by
    change X.dist _ _ ≤ 1
    exact (X.dist_eq_one_iff_adj.mpr (p.adj_getVert_succ h)).le

@[simp] theorem walkPath_mem {a b x : V} (p : X.Walk a b) :
    (walkPath X hX p).Mem x ↔ x ∈ p.support := by
  classical
  constructor
  · rintro ⟨i,_,rfl⟩
    exact p.getVert_mem_support i
  · intro hx
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hx
    refine ⟨i,by change i ≤ p.length; rw [p.length_support] at hi; omega,?_⟩
    exact (p.getVert_eq_support_getElem (by rw [p.length_support] at hi; omega)).trans he

theorem graphMetric_geodesicSpace : GeodesicSpace (graphMetric X hX) := by
  intro a b
  obtain ⟨p,hp⟩ := hX.exists_walk_length_eq_dist a b
  exact ⟨walkPath X hX p,hp⟩

end Release075.Discrete

namespace Release075.BlockPresentation
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

abbrev cayley : SimpleGraph d.GroupType := SimpleGraph.mulCayley (Set.range d.edge)
noncomputable abbrev cayleyMetric : Discrete.Metric d.GroupType :=
  Discrete.graphMetric d.cayley d.cayley_connected

theorem cayley_dist_mul (g : d.GroupType) (e : d.OrientedEdge) :
    d.cayleyMetric.dist g (g*d.edgeValue e) ≤ 1 := by
  by_cases he : g = g*d.edgeValue e
  · rw [←he]
    exact (d.cayleyMetric.self g).le.trans (by omega)
  · suffices d.cayley.Adj g (g*d.edgeValue e) by
      exact (d.cayley.dist_eq_one_iff_adj.mpr this).le
    apply (SimpleGraph.mulCayley_adj' _ _ _).mpr
    refine ⟨he,d.edge e.1,⟨e.1,rfl⟩,?_⟩
    rcases e with ⟨e,s⟩
    cases s
    · right
      simp [edgeValue]
    · left
      simp [edgeValue]

theorem cayley_dist_liftedEdge (e : d.LiftedEdge) :
    d.cayleyMetric.dist (d.liftedFlip e).2 e.2 ≤ 1 := by
  have h := d.cayley_dist_mul (e.2*(d.edgeValue e.1)⁻¹) e.1
  simpa only [inv_mul_cancel_right,liftedFlip] using h

noncomputable def liftedForm (o a : d.GroupType) (T : ℕ) (e : d.LiftedEdge) : ℤ :=
  d.cayleyMetric.form o a T (d.liftedFlip e).2 e.2

theorem liftedForm_flip (o a : d.GroupType) (T : ℕ) (e : d.LiftedEdge) :
    d.liftedForm o a T (d.liftedFlip e) = -d.liftedForm o a T e := by
  rw [liftedForm,d.liftedFlip_flip,Discrete.Metric.form_flip]
  rfl

theorem liftedForm_face_bound (o z : d.GroupType) (T : ℕ)
    {a b c : d.LiftedEdge} (hf : d.LiftedFace a b c) :
    |d.liftedForm o z T a+d.liftedForm o z T b+d.liftedForm o z T c| ≤ 2 := by
  have hab := congrArg Prod.snd hf.2.1
  have hbc := congrArg Prod.snd hf.2.2.1
  have hca := congrArg Prod.snd hf.2.2.2
  change (d.liftedFlip b).2 = a.2 at hab
  change (d.liftedFlip c).2 = b.2 at hbc
  change (d.liftedFlip a).2 = c.2 at hca
  have ha := d.cayley_dist_liftedEdge a
  have hb := d.cayley_dist_liftedEdge b
  have hc := d.cayley_dist_liftedEdge c
  rw [hca] at ha
  rw [hab] at hb
  rw [hbc] at hc
  simpa only [liftedForm,hab,hbc,hca] using
    d.cayleyMetric.form_triangle_bound o z c.2 a.2 b.2 T ha hb hc

end Release075.BlockPresentation

namespace Release075.TriangleFilling
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

/-- Bounded triangular coboundary gives a bound on every actual disk boundary. -/
theorem edge_sum_bound {w : List E} (D : TriangleFilling flip color face w)
    (F : E → ℤ) (hflip : ∀ e, F (flip e) = -F e)
    (hface : ∀ a b c, face a b c → |F a+F b+F c| ≤ 2) :
    |(w.map F).sum| ≤ 2*D.activeCount := by
  classical
  have hcyc := D.full.trace_cyclic_sum (fun a ha => (D.full_triangular a ha).1)
    (fun a _ _ => F a)
  rw [D.full.trace_edge F hflip] at hcyc
  have hcard : Fintype.card D.full.Dart = D.activeCount := Fintype.card_subtype _
  have hbound : |D.full.trace (fun a b c => F a+F b+F c)| ≤ 2*D.activeCount := by
    unfold FullFilling.trace
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _a : D.full.Dart, (2:ℤ) := by
        apply Finset.sum_le_sum
        intro a _
        split_ifs with ha
        · norm_num
        · exact hface _ _ _ (D.full_triangular a ha).2.2
      _ = 2*D.activeCount := by simp only [Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul]; ring
  rw [hcyc] at hbound
  norm_num only [nsmul_eq_mul,abs_mul,abs_neg] at hbound
  have hn := abs_nonneg ((w.map F).sum)
  omega

end Release075.TriangleFilling

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

theorem liftedForm_loop_bound {x : (d.presentation hr).LiftedVertex}
    {w : List (d.presentation hr).LiftedEdge}
    (hw : WordPath (d.presentation hr).liftedFlip (d.presentation hr).liftedTarget x x w)
    (o a : (d.presentation hr).GroupType) (T : ℕ) :
    |(w.map ((d.presentation hr).liftedForm o a T)).sum| ≤ 38*w.length := by
  obtain ⟨D,hD⟩ := d.exists_lifted_linear_filling hr ((d.presentation hr).lifted_closed_fillable hw)
  have h := D.edge_sum_bound ((d.presentation hr).liftedForm o a T)
    ((d.presentation hr).liftedForm_flip o a T)
    (fun _ _ _ hf => (d.presentation hr).liftedForm_face_bound o a T hf)
  omega

end Release075.MarkedLineData

end OAI
