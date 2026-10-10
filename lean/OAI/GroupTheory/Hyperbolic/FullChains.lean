import OAI.GroupTheory.Hyperbolic.CyclicAction

namespace OAI

namespace Release075.BlockPresentation
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

def shiftEdge (g : d.GroupType) (e : d.LiftedEdge) : d.LiftedEdge := (e.1,g*e.2)
def shiftVertex (g : d.GroupType) (x : d.LiftedVertex) : d.LiftedVertex := (x.1,g*x.2)

@[simp] theorem shiftEdge_one (e : d.LiftedEdge) : d.shiftEdge 1 e = e := by
  simp [shiftEdge]

@[simp] theorem shiftEdge_mul (g h : d.GroupType) (e : d.LiftedEdge) :
    d.shiftEdge (g*h) e = d.shiftEdge g (d.shiftEdge h e) := by
  simp only [shiftEdge,mul_assoc]

@[simp] theorem shiftEdge_flip (g : d.GroupType) (e : d.LiftedEdge) :
    d.shiftEdge g (d.liftedFlip e) = d.liftedFlip (d.shiftEdge g e) := by
  simp only [shiftEdge,liftedFlip,mul_assoc]

@[simp] theorem shiftEdge_target (g : d.GroupType) (e : d.LiftedEdge) :
    d.liftedTarget (d.shiftEdge g e) = d.shiftVertex g (d.liftedTarget e) := rfl

theorem LiftedFace.shift {a b c : d.LiftedEdge} (h : d.LiftedFace a b c) (g : d.GroupType) :
    d.LiftedFace (d.shiftEdge g a) (d.shiftEdge g b) (d.shiftEdge g c) := by
  refine ⟨h.1,?_,?_,?_⟩
  all_goals rw [← shiftEdge_flip,shiftEdge_target,shiftEdge_target]
  · exact congrArg (d.shiftVertex g) h.2.1
  · exact congrArg (d.shiftVertex g) h.2.2.1
  · exact congrArg (d.shiftVertex g) h.2.2.2

@[simp] theorem edgeChain_shift (g : d.GroupType) (e : d.LiftedEdge) :
    d.edgeChain (d.shiftEdge g e) = chainShift g (d.edgeChain e) := by
  unfold edgeChain
  change (if e.1.2 then _ else _) = _
  split_ifs <;> simp [shiftEdge,liftedFlip,chainShift_single,mul_assoc]

@[simp] theorem positiveAtom_shift (g : d.GroupType) (a b c : d.LiftedEdge) :
    d.positiveAtom (d.shiftEdge g a) (d.shiftEdge g b) (d.shiftEdge g c) =
      chainShift g (d.positiveAtom a b c) := by
  unfold positiveAtom
  change (if h : d.PositiveFace (a.1,b.1,c.1) then _ else _) = _
  split_ifs <;> simp [shiftEdge,chainShift_single]

@[simp] theorem orderedEval_shift (g : d.GroupType) (a b c : d.LiftedEdge) :
    d.orderedEval (d.shiftEdge g a) (d.shiftEdge g b) (d.shiftEdge g c) =
      chainShift g (d.orderedEval a b c) := by
  simp only [orderedEval,←shiftEdge_flip,positiveAtom_shift,map_sub]

@[simp] theorem faceEval_shift (g : d.GroupType) (a b c : d.LiftedEdge) :
    d.faceEval (d.shiftEdge g a) (d.shiftEdge g b) (d.shiftEdge g c) =
      chainShift g (d.faceEval a b c) := by
  simp only [faceEval,orderedEval_shift,map_add]

@[simp] theorem boundary₁_shift (g : d.GroupType) (c : d.C₁) :
    d.boundary₁ (chainShift g c) = chainShift g (d.boundary₁ c) := by
  have he : d.boundary₁.comp (chainShift g).toLinearMap =
      (chainShift g).toLinearMap.comp d.boundary₁ := by
    apply Finsupp.lhom_ext
    intro ⟨e,x⟩ n
    simp [boundary₁,chainShift_single,mul_assoc]
  exact LinearMap.congr_fun he c

@[simp] theorem boundary₂_shift (g : d.GroupType) (c : d.C₂) :
    d.boundary₂ (chainShift g c) = chainShift g (d.boundary₂ c) := by
  have he : d.boundary₂.comp (chainShift g).toLinearMap =
      (chainShift g).toLinearMap.comp d.boundary₂ := by
    apply Finsupp.lhom_ext
    intro ⟨t,x⟩ n
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,chainShift_single,boundary₂,
      Finsupp.linearCombination_single,map_smul,map_add]
    simp only [← d.edgeChain_shift,shiftEdge,mul_assoc]
  exact LinearMap.congr_fun he c

@[simp] theorem augmentation_boundary₁ (c : d.C₁) :
    FreeChain.augmentation (d.boundary₁ c) = 0 := by
  have he : FreeChain.augmentation.comp d.boundary₁ = 0 := by
    apply Finsupp.lhom_ext
    intro ⟨e,x⟩ n
    simp [boundary₁]
  exact LinearMap.congr_fun he c

@[simp] theorem wordChain_append (u v : List d.LiftedEdge) :
    d.wordChain (u++v) = d.wordChain u + d.wordChain v := by
  simp [wordChain]

@[simp] theorem wordChain_shift (g : d.GroupType) (w : List d.LiftedEdge) :
    d.wordChain (w.map (d.shiftEdge g)) = chainShift g (d.wordChain w) := by
  simp only [wordChain,List.map_map,Function.comp_def,edgeChain_shift,map_list_sum]

end Release075.BlockPresentation

namespace Release075.FullFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I B : Type} {r : ℕ} {d : BlockPresentation I B r}
variable {w : List d.LiftedEdge} (D : FullFilling d.liftedFlip d.liftedTarget d.LiftedFace w)

def AllTriangles : Prop := ∀ a, a ∉ D.boundary → (D.next^3) a = a ∧ D.next a ≠ a ∧
  d.LiftedFace (D.label a) (D.label (D.next a)) (D.label ((D.next^2) a))

noncomputable def faceChain : d.C₂ := -D.trace d.orderedEval

theorem triple_faceChain (hD : D.AllTriangles) : 3 • D.faceChain = -D.trace d.faceEval := by
  rw [faceChain,smul_neg]
  refine congrArg Neg.neg ?_
  exact (D.trace_cyclic_sum (fun a ha => (hD a ha).1) d.orderedEval).symm

theorem boundary₂_faceChain (hD : D.AllTriangles) : d.boundary₂ D.faceChain = d.wordChain w := by
  apply nsmul_right_injective (by decide : 3 ≠ 0)
  change (3:ℕ) • d.boundary₂ D.faceChain = 3 • d.wordChain w
  rw [← map_nsmul,D.triple_faceChain hD,map_neg]
  change -d.boundary₂.toAddMonoidHom (D.trace d.faceEval) = _
  rw [D.trace_map d.faceEval d.boundary₂.toAddMonoidHom]
  have he : D.trace (fun a b c => d.boundary₂ (d.faceEval a b c)) =
      D.trace (fun a b c => d.edgeChain a + d.edgeChain b + d.edgeChain c) := by
    apply D.trace_congr
    intro a ha
    exact d.boundary₂_faceEval (hD a ha).2.2
  change -D.trace (fun a b c => d.boundary₂ (d.faceEval a b c)) = _
  rw [he,D.trace_cyclic_sum (fun a ha => (hD a ha).1) (fun a _ _ => d.edgeChain a),
    trace_edge _ d.edgeChain d.edgeChain_flip]
  simp only [smul_neg,neg_neg,BlockPresentation.wordChain]

noncomputable abbrev shift (g : d.GroupType) :
    FullFilling d.liftedFlip d.liftedTarget d.LiftedFace (w.map (d.shiftEdge g)) where
  Dart := D.Dart
  reverse := D.reverse
  next := D.next
  reverse_involutive := D.reverse_involutive
  reverse_ne := D.reverse_ne
  label a := d.shiftEdge g (D.label a)
  reverse_label a := by rw [D.reverse_label,d.shiftEdge_flip]
  color_next a := by simp only [d.shiftEdge_target,D.color_next]
  planar := D.planar
  boundary := D.boundary
  boundary_cycle := D.boundary_cycle
  boundary_word := by
    simpa only [List.map_map,Function.comp_def] using
      congrArg (List.map (d.shiftEdge g)) D.boundary_word
  cells := by
    intro a ha
    rcases D.cells a ha with ht | ht
    · exact Or.inl ⟨ht.1,ht.2.1,ht.2.2.shift d g⟩
    · exact Or.inr ht

theorem allTriangles_shift (hD : D.AllTriangles) (g : d.GroupType) : (D.shift g).AllTriangles :=
  fun a ha => ⟨(hD a ha).1,(hD a ha).2.1,(hD a ha).2.2.shift d g⟩

theorem allTriangles_rotate (hD : D.AllTriangles) (n : ℕ) : (D.rotate n).AllTriangles := by
  intro a ha
  exact hD a (by simpa only [List.mem_rotate] using ha)

@[simp] theorem faceChain_rotate (n : ℕ) : (D.rotate n).faceChain = D.faceChain := by
  rw [faceChain,trace_rotate,faceChain]

@[simp] theorem faceChain_shift (g : d.GroupType) :
    (D.shift g).faceChain = chainShift g D.faceChain := by
  unfold faceChain
  rw [map_neg]
  apply congrArg Neg.neg
  calc
    (D.shift g).trace d.orderedEval =
        D.trace (fun a b c => chainShift g (d.orderedEval a b c)) := by
      unfold trace
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp only [BlockPresentation.orderedEval_shift]
    _ = chainShift g (D.trace d.orderedEval) :=
      (D.trace_map d.orderedEval (chainShift g).toAddMonoidHom).symm

end Release075.FullFilling

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

theorem fullChain_unique {w : List (d.presentation hr).LiftedEdge}
    {x : (d.presentation hr).LiftedVertex}
    (hw : WordPath (d.presentation hr).liftedFlip (d.presentation hr).liftedTarget x x w)
    (D D' : FullFilling (d.presentation hr).liftedFlip (d.presentation hr).liftedTarget
      (d.presentation hr).LiftedFace w) (ht : D.AllTriangles) (ht' : D'.AllTriangles) :
    D.faceChain = D'.faceChain := by
  let P := d.presentation hr
  apply nsmul_right_injective (by decide : 3 ≠ 0)
  change (3 : ℕ) • D.faceChain = 3 • D'.faceChain
  rw [D.triple_faceChain ht,D'.triple_faceChain ht']
  apply congrArg Neg.neg
  exact FullFilling.trace_unique (d.lifted_sphere_empty_of_noDipole hr)
    P.liftedFlip_flip P.liftedTarget_ne (fun _ _ _ h => h.mirror P) P.faceEval
    (fun a b c _ => P.faceEval_rotate a b c) (fun a b c _ => P.faceEval_mirror a b c)
    P.faceEval_degenerate hw D D'

end Release075.MarkedLineData

end OAI
