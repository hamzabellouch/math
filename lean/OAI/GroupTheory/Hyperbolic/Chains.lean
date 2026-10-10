import OAI.GroupTheory.Hyperbolic.FullGluing

namespace OAI

namespace Release075

/-- The free integral module on copies of the regular left group action. -/
abbrev FreeChain (A G : Type) := (A × G) →₀ ℤ

noncomputable def chainShift {A G : Type} [Group G] (g : G) :
    FreeChain A G ≃ₗ[ℤ] FreeChain A G :=
  Finsupp.domLCongr (Equiv.prodCongr (Equiv.refl A) (Equiv.mulLeft g))

@[simp] theorem chainShift_single {A G : Type} [Group G] (g : G) (a : A) (h : G) (n : ℤ) :
    chainShift g (Finsupp.single (a,h) n) = Finsupp.single (a,g*h) n :=
  Finsupp.domLCongr_single _ _ _

namespace BlockPresentation
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

abbrev C₀ := FreeChain d.Vertex d.GroupType
abbrev C₁ := FreeChain d.Edge d.GroupType

def PositiveFace (t : d.OrientedEdge × d.OrientedEdge × d.OrientedEdge) : Prop :=
  d.TriangleFace t.1 t.2.1 t.2.2 ∧ d.edgeTarget t.1 = .v ∧
    d.edgeTarget t.2.1 = .w ∧ d.edgeTarget t.2.2 = .o

abbrev FaceBase := {t : d.OrientedEdge × d.OrientedEdge × d.OrientedEdge // d.PositiveFace t}
abbrev C₂ := FreeChain d.FaceBase d.GroupType

/-- An oriented edge is represented in a free module on the positive orientations. -/
noncomputable def edgeChain (e : d.LiftedEdge) : d.C₁ :=
  if e.1.2 then Finsupp.single (e.1.1,e.2) 1 else
    -Finsupp.single (e.1.1,(d.liftedFlip e).2) 1

@[simp] theorem edgeChain_flip (e : d.LiftedEdge) :
    d.edgeChain (d.liftedFlip e) = -d.edgeChain e := by
  rcases e with ⟨⟨e,s⟩,g⟩
  cases s <;> simp [edgeChain,liftedFlip,flipEdge,edgeValue]

noncomputable def boundary₁ : d.C₁ →ₗ[ℤ] d.C₀ :=
  Finsupp.linearCombination ℤ (fun e =>
    Finsupp.single (d.edgeTarget (e.1,true), e.2) 1 -
      Finsupp.single (d.edgeTarget (d.flipEdge (e.1,true)),e.2*(d.edge (e.1))⁻¹) 1)

theorem boundary₁_edgeChain (e : d.LiftedEdge) :
    d.boundary₁ (d.edgeChain e) = Finsupp.single (d.liftedTarget e) 1 -
      Finsupp.single (d.liftedTarget (d.liftedFlip e)) 1 := by
  rcases e with ⟨⟨e,s⟩,g⟩
  cases s <;> simp [edgeChain,boundary₁,liftedFlip,liftedTarget,flipEdge,edgeValue]

noncomputable def boundary₂ : d.C₂ →ₗ[ℤ] d.C₁ :=
  Finsupp.linearCombination ℤ (fun t =>
    d.edgeChain (t.1.val.1,t.2*d.edgeValue t.1.val.1) +
      d.edgeChain (t.1.val.2.1,t.2*d.edgeValue t.1.val.1*d.edgeValue t.1.val.2.1) +
        d.edgeChain (t.1.val.2.2,t.2))

theorem boundary₁_boundary₂ (c : d.C₂) : d.boundary₁ (d.boundary₂ c) = 0 := by
  have he : d.boundary₁.comp d.boundary₂ = 0 := by
    apply Finsupp.lhom_ext
    intro t n
    obtain ⟨t,g⟩ := t
    have h := TriangleFace.lift d t.property.1 g
    simp only [LinearMap.comp_apply,boundary₂,Finsupp.linearCombination_single,map_smul,
      map_add,boundary₁_edgeChain,LinearMap.zero_apply]
    rw [h.2.1,h.2.2.1,h.2.2.2]
    have hz :
        (Finsupp.single (d.liftedTarget (t.val.1,g*d.edgeValue t.val.1)) 1 -
          Finsupp.single (d.liftedTarget (t.val.2.2,g)) 1) +
        (Finsupp.single (d.liftedTarget (t.val.2.1,g*d.edgeValue t.val.1*d.edgeValue t.val.2.1)) 1 -
          Finsupp.single (d.liftedTarget (t.val.1,g*d.edgeValue t.val.1)) 1) +
        (Finsupp.single (d.liftedTarget (t.val.2.2,g)) 1 -
          Finsupp.single (d.liftedTarget (t.val.2.1,g*d.edgeValue t.val.1*d.edgeValue t.val.2.1)) 1) = (0 : d.C₀) := by abel
    rw [hz,smul_zero]
  exact LinearMap.congr_fun he c

/-- The positively oriented, O-based atom. Nonfaces give zero. -/
noncomputable def positiveAtom (a b c : d.LiftedEdge) : d.C₂ :=
  if h : d.PositiveFace (a.1,b.1,c.1) then Finsupp.single (⟨(a.1,b.1,c.1),h⟩,c.2) 1 else 0

/-- Exactly one O-corner, with its orientation sign. -/
noncomputable def orderedEval (a b c : d.LiftedEdge) : d.C₂ :=
  d.positiveAtom a b c - d.positiveAtom (d.liftedFlip c) (d.liftedFlip b) (d.liftedFlip a)

/-- Cyclic evaluation of one oriented face. -/
noncomputable def faceEval (a b c : d.LiftedEdge) : d.C₂ :=
  d.orderedEval a b c + d.orderedEval b c a + d.orderedEval c a b

theorem faceEval_rotate (a b c : d.LiftedEdge) : d.faceEval b c a = d.faceEval a b c := by
  unfold faceEval
  abel

theorem orderedEval_mirror (a b c : d.LiftedEdge) :
    d.orderedEval (d.liftedFlip a) (d.liftedFlip c) (d.liftedFlip b) = - d.orderedEval b c a := by
  simp only [orderedEval,liftedFlip_flip]
  abel

theorem faceEval_mirror (a b c : d.LiftedEdge) :
    d.faceEval (d.liftedFlip a) (d.liftedFlip c) (d.liftedFlip b) = -d.faceEval a b c := by
  simp only [faceEval,orderedEval_mirror]
  abel

theorem positiveAtom_eq_zero {a b c : d.LiftedEdge}
    (h : ¬d.TriangleFace a.1 b.1 c.1) : d.positiveAtom a b c = 0 := by
  simp only [positiveAtom]
  split_ifs with hh
  · exact False.elim (h hh.1)
  · rfl

theorem positiveAtom_degenerate (a b : d.LiftedEdge) :
    d.positiveAtom a b a = 0 ∧ d.positiveAtom a a b = 0 ∧ d.positiveAtom b a a = 0 := by
  refine ⟨d.positiveAtom_eq_zero ?_,d.positiveAtom_eq_zero ?_,d.positiveAtom_eq_zero ?_⟩
  · intro h; exact (TriangleFace.colors d h).2.2 rfl
  · intro h; exact (TriangleFace.colors d h).1 rfl
  · intro h; exact (TriangleFace.colors d h).2.1 rfl

theorem faceEval_degenerate (a b : d.LiftedEdge) : d.faceEval a b a = 0 := by
  obtain ⟨ha,hb,hc⟩ := d.positiveAtom_degenerate a b
  obtain ⟨ha',hb',hc'⟩ := d.positiveAtom_degenerate (d.liftedFlip a) (d.liftedFlip b)
  simp only [faceEval,orderedEval,ha,hb,hc,ha',hb',hc',sub_self,add_zero]

end BlockPresentation
end Release075

namespace Release075.BlockPresentation
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

theorem positiveAtom_zero_first {a b c : d.LiftedEdge} (h : d.edgeTarget a.1 ≠ .v) :
    d.positiveAtom a b c = 0 := by
  unfold positiveAtom
  split_ifs with hh
  · exact False.elim (h hh.2.1)
  · rfl

theorem positiveAtom_zero_second {a b c : d.LiftedEdge} (h : d.edgeTarget b.1 ≠ .w) :
    d.positiveAtom a b c = 0 := by
  unfold positiveAtom
  split_ifs with hh
  · exact False.elim (h hh.2.2.1)
  · rfl

theorem faceEval_positive {a b c : d.LiftedEdge} (h : d.LiftedFace a b c)
    (hp : d.PositiveFace (a.1,b.1,c.1)) : d.faceEval a b c = d.positiveAtom a b c := by
  have hva : d.edgeTarget (d.liftedFlip a).1 = .o :=
    (congrArg Prod.fst h.2.2.2).trans hp.2.2.2
  have hvc : d.edgeTarget (d.liftedFlip c).1 = .w :=
    (congrArg Prod.fst h.2.2.1).trans hp.2.2.1
  have hb := d.positiveAtom_zero_first (a := b) (b := c) (c := a) (by rw [hp.2.2.1]; intro he; cases he)
  have hc := d.positiveAtom_zero_first (a := c) (b := a) (c := b) (by rw [hp.2.2.2]; intro he; cases he)
  have h₁ := d.positiveAtom_zero_first (a := d.liftedFlip c) (b := d.liftedFlip b)
    (c := d.liftedFlip a) (by rw [hvc]; intro he; cases he)
  have h₂ := d.positiveAtom_zero_first (a := d.liftedFlip a) (b := d.liftedFlip c)
    (c := d.liftedFlip b) (by rw [hva]; intro he; cases he)
  have h₃ := d.positiveAtom_zero_second (a := d.liftedFlip b) (b := d.liftedFlip a)
    (c := d.liftedFlip c) (by rw [hva]; intro he; cases he)
  simp only [faceEval,orderedEval,hb,hc,h₁,h₂,h₃,sub_zero,add_zero]

theorem boundary₂_positiveAtom {a b c : d.LiftedEdge} (h : d.LiftedFace a b c)
    (hp : d.PositiveFace (a.1,b.1,c.1)) :
    d.boundary₂ (d.positiveAtom a b c) = d.edgeChain a + d.edgeChain b + d.edgeChain c := by
  have ha : a.2 = c.2*d.edgeValue a.1 :=
    mul_inv_eq_iff_eq_mul.mp (congrArg Prod.snd h.2.2.2)
  have hb : b.2 = a.2*d.edgeValue b.1 :=
    mul_inv_eq_iff_eq_mul.mp (congrArg Prod.snd h.2.1)
  simp only [positiveAtom,dite_eq_left hp,boundary₂,Finsupp.linearCombination_single,one_smul]
  rw [← ha,← hb]

theorem TriangleFace.positive_orient {a b c : d.OrientedEdge} (h : d.TriangleFace a b c) :
    d.PositiveFace (a,b,c) ∨ d.PositiveFace (b,c,a) ∨ d.PositiveFace (c,a,b) ∨
    d.PositiveFace (d.flipEdge a,d.flipEdge c,d.flipEdge b) ∨
    d.PositiveFace (d.flipEdge b,d.flipEdge a,d.flipEdge c) ∨
    d.PositiveFace (d.flipEdge c,d.flipEdge b,d.flipEdge a) := by
  have hp (b : B) (i : (d.block b).labels) (u v : Fin r) :
      d.PositiveFace (d.orientedL b i u v,d.orientedX i u v,d.flipEdge (d.orientedR b i u v)) := by
    refine ⟨TriangleFace.pos₀ _ _ _ _,?_,?_,?_⟩ <;> rfl
  cases h with
  | pos₀ b i u v => exact Or.inl (hp _ _ _ _)
  | pos₁ b i u v => exact Or.inr (Or.inr (Or.inl (hp _ _ _ _)))
  | pos₂ b i u v => exact Or.inr (Or.inl (hp _ _ _ _))
  | neg₀ b i u v =>
    exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [flipEdge_flipEdge] using hp b i u v))))
  | neg₁ b i u v =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simpa only [flipEdge_flipEdge] using hp b i u v)))))
  | neg₂ b i u v =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [flipEdge_flipEdge] using hp b i u v)))))

theorem boundary₂_faceEval {a b c : d.LiftedEdge} (h : d.LiftedFace a b c) :
    d.boundary₂ (d.faceEval a b c) = d.edgeChain a + d.edgeChain b + d.edgeChain c := by
  have pos {a b c : d.LiftedEdge} (h : d.LiftedFace a b c)
      (hp : d.PositiveFace (a.1,b.1,c.1)) :
      d.boundary₂ (d.faceEval a b c) = d.edgeChain a + d.edgeChain b + d.edgeChain c := by
    rw [d.faceEval_positive h hp]
    exact d.boundary₂_positiveAtom h hp
  have circ {a b c : d.LiftedEdge}
      (hp : d.boundary₂ (d.faceEval b c a) = d.edgeChain b + d.edgeChain c + d.edgeChain a) :
      d.boundary₂ (d.faceEval a b c) = d.edgeChain a + d.edgeChain b + d.edgeChain c := by
    rw [faceEval_rotate] at hp
    rw [hp]
    abel
  have mir {a b c : d.LiftedEdge}
      (hp : d.boundary₂ (d.faceEval (d.liftedFlip a) (d.liftedFlip c) (d.liftedFlip b)) =
        d.edgeChain (d.liftedFlip a) + d.edgeChain (d.liftedFlip c) + d.edgeChain (d.liftedFlip b)) :
      d.boundary₂ (d.faceEval a b c) = d.edgeChain a + d.edgeChain b + d.edgeChain c := by
    rw [faceEval_mirror,map_neg,edgeChain_flip,edgeChain_flip,edgeChain_flip] at hp
    apply neg_injective
    rw [hp]
    abel
  rcases TriangleFace.positive_orient d h.1 with hp | hp | hp | hp | hp | hp
  · exact pos h hp
  · exact circ (pos (h.rotate d) hp)
  · exact circ (circ (pos ((h.rotate d).rotate d) hp))
  · exact mir (pos (h.mirror d) hp)
  · exact circ (mir (pos ((h.rotate d).mirror d) hp))
  · exact circ (circ (mir (pos (((h.rotate d).rotate d).mirror d) hp)))

end Release075.BlockPresentation

namespace Release075.BlockPresentation
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

noncomputable def wordChain (w : List d.LiftedEdge) : d.C₁ := (w.map d.edgeChain).sum

noncomputable def diskChain {w : List d.LiftedEdge}
    (D : TriangleFilling d.liftedFlip d.liftedTarget d.LiftedFace w) : d.C₂ :=
  -D.full.trace d.orderedEval

theorem triple_diskChain {w : List d.LiftedEdge}
    (D : TriangleFilling d.liftedFlip d.liftedTarget d.LiftedFace w) :
    3 • d.diskChain D = -D.full.trace d.faceEval := by
  rw [diskChain,smul_neg]
  refine congrArg Neg.neg ?_
  exact (D.full.trace_cyclic_sum (fun a ha => (D.full_triangular a ha).1) d.orderedEval).symm

theorem boundary₂_diskChain {w : List d.LiftedEdge}
    (D : TriangleFilling d.liftedFlip d.liftedTarget d.LiftedFace w) :
    d.boundary₂ (d.diskChain D) = d.wordChain w := by
  apply nsmul_right_injective (by decide : 3 ≠ 0)
  change (3 : ℕ) • d.boundary₂ (d.diskChain D) = 3 • d.wordChain w
  rw [← map_nsmul,triple_diskChain,map_neg]
  change -d.boundary₂.toAddMonoidHom (D.full.trace d.faceEval) = _
  rw [D.full.trace_map d.faceEval d.boundary₂.toAddMonoidHom]
  have he : D.full.trace (fun a b c => d.boundary₂ (d.faceEval a b c)) =
      D.full.trace (fun a b c => d.edgeChain a + d.edgeChain b + d.edgeChain c) := by
    apply D.full.trace_congr
    intro a ha
    exact d.boundary₂_faceEval (D.full_triangular a ha).2.2
  change -D.full.trace (fun a b c => d.boundary₂ (d.faceEval a b c)) = _
  rw [he,D.full.trace_cyclic_sum (fun a ha => (D.full_triangular a ha).1)
    (fun a _ _ => d.edgeChain a),FullFilling.trace_edge _ d.edgeChain d.edgeChain_flip]
  simp only [smul_neg,neg_neg,wordChain]

end Release075.BlockPresentation

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

theorem diskChain_unique {w : List (d.presentation hr).LiftedEdge}
    {x : (d.presentation hr).LiftedVertex}
    (hw : WordPath (d.presentation hr).liftedFlip (d.presentation hr).liftedTarget x x w)
    (D D' : TriangleFilling (d.presentation hr).liftedFlip (d.presentation hr).liftedTarget
      (d.presentation hr).LiftedFace w) :
    (d.presentation hr).diskChain D = (d.presentation hr).diskChain D' := by
  let P := d.presentation hr
  apply nsmul_right_injective (by decide : 3 ≠ 0)
  change (3 : ℕ) • (d.presentation hr).diskChain D = 3 • (d.presentation hr).diskChain D'
  rw [BlockPresentation.triple_diskChain,BlockPresentation.triple_diskChain]
  apply congrArg Neg.neg
  exact FullFilling.trace_unique (d.lifted_sphere_empty_of_noDipole hr)
    P.liftedFlip_flip P.liftedTarget_ne (fun _ _ _ h => h.mirror P) P.faceEval
    (fun a b c _ => P.faceEval_rotate a b c) (fun a b c _ => P.faceEval_mirror a b c)
    P.faceEval_degenerate hw D.full D'.full

end Release075.MarkedLineData

end OAI
