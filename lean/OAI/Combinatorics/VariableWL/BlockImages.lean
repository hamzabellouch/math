import OAI.Combinatorics.VariableWL.Blocks

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10 uVariable11 uVariable12

namespace VariableWL.Blocks
open scoped CharTwo
open VariableWL.Affine Subdivision
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} (J : ProductImages.Instance r P E)

def dimension : Vertex P E n → ℕ
  | .inl p => J.dimension p
  | .inr _ => 1

abbrev Value (t : Vertex P E n) := Vec (dimension J t)

def vectorShift (h : J.Shifts n) : ∀ t : Vertex P E n, Value J t
  | .inl p => h.1 p
  | .inr q => fun _ => h.2 q

def linkLeft (l : Link E n) : Value J (left J.source l) →ₗ[Bit] Bit := by
  unfold left
  split_ifs with hz
  · rw [dite_eq_left hz]
    exact J.linearLeft l.1
  · rw [dite_eq_right hz]
    exact LinearMap.proj (0 : Fin 1)

def linkRight (l : Link E n) : Value J (right J.target l) →ₗ[Bit] Bit := by
  unfold right
  split_ifs with hz
  · rw [dite_eq_left hz]
    exact J.linearRight l.1
  · rw [dite_eq_right hz]
    exact LinearMap.proj (0 : Fin 1)

def leftConstant (l : Link E n) : Bit := if l.2.val = 0 then J.constantLeft l.1 else 0
def rightConstant (l : Link E n) : Bit := if l.2.val = n then J.constantRight l.1 else 0

def linkConstant (l : Link E n) : Bit := leftConstant J l + rightConstant J l

theorem dependent_linear_apply {A : Type uVariable3} (d : A → ℕ) {i j : A} (he : i = j)
    (L : Vec (d i) →ₗ[Bit] Bit) (v : ∀ t, Vec (d t)) :
    (cast (congrArg (fun t => Vec (d t) →ₗ[Bit] Bit) he) L) (v j) = L (v i) := by
  subst j; rfl

theorem linkLeft_eval (h : J.Shifts n) (l : Link E n) :
    linkLeft J l (vectorShift J h (left J.source l)) + leftConstant J l =
      J.shiftLeft h l := by
  by_cases hz : l.2.val = 0
  · have he := dependent_linear_apply (dimension J) (i := .inl (J.source l.1))
      (j := left J.source l) (by simp only [left, dite_eq_left hz])
      (J.linearLeft l.1) (vectorShift J h)
    simp only [linkLeft, dite_eq_left hz, leftConstant, ite_eq_left hz,
      ProductImages.Instance.shiftLeft, ProductImages.Instance.leftForm]
    exact congrArg (fun z => z + J.constantLeft l.1) he
  · simp only [linkLeft, dite_eq_right hz, leftConstant, ite_eq_right hz, add_zero,
      ProductImages.Instance.shiftLeft]
    exact dependent_linear_apply (dimension J)
      (i := .inr (l.1, ⟨l.2.val-1, by omega⟩)) (j := left J.source l)
      (by simp only [left, dite_eq_right hz]) (LinearMap.proj (0 : Fin 1)) (vectorShift J h)

theorem linkRight_eval (h : J.Shifts n) (l : Link E n) :
    linkRight J l (vectorShift J h (right J.target l)) + rightConstant J l =
      J.shiftRight h l := by
  by_cases hz : l.2.val = n
  · have he := dependent_linear_apply (dimension J) (i := .inl (J.target l.1))
      (j := right J.target l) (by simp only [right, dite_eq_left hz])
      (J.linearRight l.1) (vectorShift J h)
    simp only [linkRight, dite_eq_left hz, rightConstant, ite_eq_left hz,
      ProductImages.Instance.shiftRight, ProductImages.Instance.rightForm]
    exact congrArg (fun z => z + J.constantRight l.1) he
  · simp only [linkRight, dite_eq_right hz, rightConstant, ite_eq_right hz, add_zero,
      ProductImages.Instance.shiftRight]
    exact dependent_linear_apply (dimension J)
      (i := .inr (l.1, ⟨l.2.val, by omega⟩)) (j := right J.target l)
      (by simp only [right, dite_eq_right hz]) (LinearMap.proj (0 : Fin 1)) (vectorShift J h)

theorem link_equation_iff (h : J.Shifts n) (l : Link E n) :
    linkLeft J l (vectorShift J h (left J.source l)) +
        linkRight J l (vectorShift J h (right J.target l)) = linkConstant J l ↔
      J.shiftLeft h l = J.shiftRight h l := by
  rw [← linkLeft_eval J h l, ← linkRight_eval J h l]
  unfold linkConstant
  constructor <;> intro he
  · have hh := congrArg (fun z => z + linkRight J l (vectorShift J h (right J.target l)) +
        leftConstant J l) he
    simpa [add_assoc, add_comm, add_left_comm] using hh
  · have hh := congrArg (fun z => z + leftConstant J l +
        linkRight J l (vectorShift J h (right J.target l))) he
    simpa [add_assoc, add_comm, add_left_comm] using hh

abbrev ReadoutValue : Readout r n P E → Type
  | .inl h => Value J h.type
  | .inr _ => Bit

abbrev Potentials := ∀ v : Corner r n P E, Value J v.2.1

def marker (marked i : Fin r) : Bit := if i = marked then 1 else 0

def potentialValues (marked : Fin r) (h : J.Shifts n) (M : Potentials (n := n) J) :
    ∀ a : Readout r n P E, ReadoutValue J a
  | .inl x => M (x.row, x.type, x.first) + M (finRotate r x.row, x.type, x.last) +
      marker marked x.row • vectorShift J h x.type
  | .inr y => linkLeft J y.link (M (y.row, left J.source y.link, y.label)) +
      linkRight J y.link (M (y.row, right J.target y.link, matchOutput J y.link y.row y.label))

theorem potential_square (marked : Fin r) (h : J.Shifts n) (M : Potentials (n := n) J)
    (s : Square r n E) (hs : J.shiftLeft h s.link = J.shiftRight h s.link) :
    linkLeft J s.link (potentialValues J marked h M (.inl (squareLeft J s))) +
      linkRight J s.link (potentialValues J marked h M (.inl (squareRight J s))) +
      potentialValues J marked h M (.inr (squareBottom s)) +
      potentialValues J marked h M (.inr (squareTop s)) =
        marker marked s.row * linkConstant J s.link := by
  have he := (link_equation_iff J h s.link).mpr hs
  dsimp only [potentialValues, squareLeft, squareRight, squareBottom, squareTop, end0, end1]
  simp only [map_add, map_smul, smul_eq_mul]
  have ht : (2 : Bit) = 0 := by decide
  linear_combination (marker marked s.row) * he +
    (linkLeft J s.link (M (s.row, left J.source s.link, s.first)) +
      linkLeft J s.link (M (finRotate r s.row, left J.source s.link, s.last)) +
      linkRight J s.link (M (s.row, right J.target s.link,
        matchOutput J s.link s.row s.first)) +
      linkRight J s.link (M (finRotate r s.row, right J.target s.link,
        matchOutput J s.link (finRotate r s.row) s.last))) * ht

def gaugePotentials (h g : J.Shifts n) (M : Potentials (n := n) J) (s : Corner r n P E → Bit) :
    Potentials (n := n) J := fun v => M v + s v • (vectorShift J g v.2.1 + vectorShift J h v.2.1)

theorem gauge_horizontal_readout (marked : Fin r) (h g : J.Shifts n)
    (M : Potentials (n := n) J) (s : Corner r n P E → Bit) (x : Horizontal r n P E)
    (hs : s (end0 J (.inl x)) + s (end1 J (.inl x)) = marker marked x.row) :
    potentialValues J marked g (gaugePotentials J h g M s) (.inl x) =
      potentialValues J marked h M (.inl x) := by
  exact Affine.gauge_horizontal _ _ _ _ _ _ _ hs

theorem gauge_vertical_readout (marked : Fin r) (h g : J.Shifts n)
    (M : Potentials (n := n) J) (s : Corner r n P E → Bit) (y : Vertical r n E)
    (hs : s (end0 J (.inr y)) = s (end1 J (.inr y)))
    (hh : J.shiftLeft h y.link = J.shiftRight h y.link)
    (hg : J.shiftLeft g y.link = J.shiftRight g y.link) :
    potentialValues J marked g (gaugePotentials J h g M s) (.inr y) =
      potentialValues J marked h M (.inr y) := by
  exact Affine.gauge_vertical _ _ _ _ _ _ _ _ _ _ hs
    (Affine.shift_difference _ _ _ _ _ _ _
      ((link_equation_iff J h y.link).mpr hh) ((link_equation_iff J g y.link).mpr hg))

end VariableWL.Blocks

namespace VariableWL.Markers
open scoped CharTwo
variable {V : Type uVariable4} {G : SimpleGraph V}

@[simp] theorem walkSum_copy (ω : V → V → Bit) {u v u' v' : V}
    (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    walkSum ω (p.copy hu hv) = walkSum ω p := by
  subst u'; subst v'; rfl

theorem exists_potential_all (ω : V → V → Bit)
    (hsym : ∀ u v, G.Adj u v → ω u v = ω v u)
    (hzero : ∀ u (p : G.Walk u u), walkSum ω p = 0) :
    ∃ s : V → Bit, ∀ u v, G.Adj u v → s u + s v = ω u v := by
  classical
  let root (v : V) : V := (G.connectedComponentMk v).out
  have hr (v : V) : G.Reachable (root v) v :=
    SimpleGraph.ConnectedComponent.exact (G.connectedComponentMk v).out_eq
  let p (v : V) : G.Walk (root v) v := (hr v).some
  refine ⟨fun v => walkSum ω (p v), ?_⟩
  intro u v huv
  have he : root v = root u := congrArg (fun c : G.ConnectedComponent => c.out)
    (SimpleGraph.ConnectedComponent.sound huv.reachable).symm
  have hc := hzero (root u)
    (((p u).append huv.toWalk).append ((p v).copy he rfl).reverse)
  simp only [walkSum_append, walkSum_reverse ω hsym, walkSum_copy,
    SimpleGraph.Adj.toWalk, walkSum_cons, walkSum_nil, add_zero] at hc
  calc
    walkSum ω (p u) + walkSum ω (p v) =
        (walkSum ω (p u) + ω u v + walkSum ω (p v)) + ω u v := by
      simp [add_comm, add_assoc]
    _ = ω u v := by rw [hc, zero_add]
end VariableWL.Markers

namespace VariableWL.Wrapping.RowDiagram
open scoped CharTwo
open VariableWL.Markers
variable {I : Type uVariable5} {V : Type uVariable6} [DecidableEq I] {G : SimpleGraph V}
    {next : Equiv.Perm I} (D : VariableWL.Wrapping.RowDiagram G next)

theorem nonwrapping_potential (marked : I) (hn : ¬ D.Wraps marked) :
    ∃ s : V → Bit, ∀ u v, G.Adj u v → s u + s v = D.rowWeight marked u v := by
  apply Markers.exists_potential_all
  · intro u v h
    simp only [rowWeight, D.symmetric u v h]
  · intro u p
    have hx : ∀ x : Bit, x = 0 ∨ x = 1 := by decide
    rcases hx (walkSum (D.rowWeight marked) p) with h | h
    · exact h
    · exact (hn ⟨u,p,h⟩).elim
end VariableWL.Wrapping.RowDiagram

namespace VariableWL.Blocks
open scoped CharTwo
open VariableWL.Affine Subdivision
variable {r n : ℕ} {P : Type uVariable7} {E : Type uVariable8} (J : ProductImages.Instance r P E)

theorem readout_adj (hr : 2 ≤ r) (hn : 0 < n) (U : Set (Block (n := n) J))
    {b : Block (n := n) J} (hb : b ∈ U) {a : Readout r n P E}
    (ha : HasReadout J b.val a) : (diagram J hr hn U).Adj (end0 J a) (end1 J a) :=
  ⟨b,hb,a,ha,Or.inl ⟨rfl,rfl⟩⟩

theorem diagram_mono (hr : 2 ≤ r) (hn : 0 < n) {U V : Set (Block (n := n) J)}
    (h : U ⊆ V) : diagram J hr hn U ≤ diagram J hr hn V := by
  rintro u v ⟨b,hb,a,ha,hh⟩
  exact ⟨b,h hb,a,ha,hh⟩

theorem gauge_nonwrapping (hr : 3 ≤ r) (hn : 0 < n)
    (U : Finset (Block (n := n) J)) (marked : Fin r)
    (h g : J.Shifts n) (M : Potentials (n := n) J)
    (hh : J.ShiftSystem (supportLinks J U) h)
    (hg : J.ShiftSystem (supportLinks J U) g)
    (hnw : ¬ (rowDiagram J hr hn U).Wraps marked) :
    ∃ M' : Potentials (n := n) J, ∀ b ∈ U, ∀ a, HasReadout J b.val a →
      potentialValues J marked g M' a = potentialValues J marked h M a := by
  classical
  obtain ⟨s,hs⟩ := (rowDiagram J hr hn U).nonwrapping_potential marked hnw
  refine ⟨gaugePotentials J h g M s, ?_⟩
  intro b hb a ha
  have hed := readout_adj J (by omega) hn U hb ha
  have he := hs (end0 J a) (end1 J a) hed
  dsimp only [rowDiagram] at he
  unfold Wrapping.RowDiagram.rowWeight at he
  dsimp only at he
  simp only [(horizontalTag_readout J hr a).1] at he
  cases a with
  | inl x =>
    apply gauge_horizontal_readout J marked h g M s x
    simpa [marker] using he
  | inr y =>
    apply gauge_vertical_readout J marked h g M s y
    · simp only [reduceCtorEq, ite_false] at he
      have he' := congrArg (fun z => z + s (end1 J (.inr y))) he
      simpa [add_assoc] using he'
    · exact hh y.link (Finset.mem_biUnion.mpr
        ⟨b,hb,hasReadout_vertical_link J ha⟩)
    · exact hg y.link (Finset.mem_biUnion.mpr
        ⟨b,hb,hasReadout_vertical_link J ha⟩)
end VariableWL.Blocks

namespace VariableWL.ProductImages.Instance
open VariableWL.Affine Subdivision
variable {r n : ℕ} {P : Type uVariable9} {E : Type uVariable10} (J : ProductImages.Instance r P E)

noncomputable def replaceInternal (hn : 0 < n) (S : Set (Link E n))
    (root : Vertex P E n) (a : Bit) (h : J.Shifts n) : J.Shifts n := by
  classical
  exact (h.1, fun q => if (supportGraph hn J.source J.target S).Reachable root (.inr q)
    then a else h.2 q)

theorem replaceInternal_agree_outside (hn : 0 < n) (S : Set (Link E n))
    (root : Vertex P E n) (a : Bit) (h : J.Shifts n) {v : Vertex P E n}
    (hv : ¬ (supportGraph hn J.source J.target S).Reachable root v) :
    J.AgreeAt (J.replaceInternal hn S root a h) h v := by
  classical
  cases v with
  | inl p => rfl
  | inr q => exact ite_eq_right hv

theorem replaceInternal_system (hn : 0 < n) (S : Set (Link E n))
    (root : Vertex P E n) (a : Bit) (h : J.Shifts n) (hh : J.ShiftSystem S h)
    (hnr : ∀ p, ¬ (supportGraph hn J.source J.target S).Reachable root (.inl p)) :
    J.ShiftSystem S (J.replaceInternal hn S root a h) := by
  classical
  intro l hl
  have hadj : (supportGraph hn J.source J.target S).Adj
      (left J.source l) (right J.target l) := ⟨l,hl,Or.inl ⟨rfl,rfl⟩⟩
  by_cases hr : (supportGraph hn J.source J.target S).Reachable root (left J.source l)
  · have hr' := hr.trans hadj.reachable
    obtain ⟨q,hq⟩ : ∃ q, left J.source l = .inr q := by
      cases he : left J.source l with
      | inl p => exact (hnr p (he ▸ hr)).elim
      | inr q => exact ⟨q,rfl⟩
    obtain ⟨q',hq'⟩ : ∃ q', right J.target l = .inr q' := by
      cases he : right J.target l with
      | inl p => exact (hnr p (he ▸ hr')).elim
      | inr q => exact ⟨q,rfl⟩
    rw [J.shiftLeft_eq_internal _ l hq, J.shiftRight_eq_internal _ l hq']
    simp only [replaceInternal, ite_eq_left (hq ▸ hr), ite_eq_left (hq' ▸ hr')]
  · have hr' : ¬ (supportGraph hn J.source J.target S).Reachable root (right J.target l) :=
      fun hw => hr (hw.trans hadj.symm.reachable)
    rw [J.shiftLeft_agree l (J.replaceInternal_agree_outside hn S root a h hr),
      J.shiftRight_agree l (J.replaceInternal_agree_outside hn S root a h hr')]
    exact hh l hl

theorem exists_scalar_shift (hn : 0 < n) (S : Set (Link E n))
    (root : Vertex P E n) (a : Bit) (h : J.Shifts n) (hh : J.ShiftSystem S h)
    (hnr : ∀ p, ¬ (supportGraph hn J.source J.target S).Reachable root (.inl p)) :
    ∃ g : J.Shifts n, J.ShiftSystem S g ∧ ∀ q,
      (supportGraph hn J.source J.target S).Reachable root (.inr q) → g.2 q = a := by
  classical
  refine ⟨J.replaceInternal hn S root a h,
    J.replaceInternal_system hn S root a h hh hnr, ?_⟩
  intro q hq
  exact ite_eq_left hq

theorem internal_adj_values (hn : 0 < n) (S : Set (Link E n))
    (h : J.Shifts n) (hh : J.ShiftSystem S h) {q q' : E × Fin n}
    (ha : (supportGraph hn J.source J.target S).Adj (.inr q) (.inr q')) :
    h.2 q = h.2 q' := by
  obtain ⟨l,hl,⟨he,he'⟩ | ⟨he,he'⟩⟩ := ha
  · exact (J.shiftLeft_eq_internal h l he.symm).symm.trans
      ((hh l hl).trans (J.shiftRight_eq_internal h l he'.symm))
  · exact (J.shiftRight_eq_internal h l he.symm).symm.trans
      ((hh l hl).symm.trans (J.shiftLeft_eq_internal h l he'.symm))

theorem scalar_constant (hn : 0 < n) (S : Set (Link E n))
    (h : J.Shifts n) (hh : J.ShiftSystem S h) (q : E × Fin n)
    (hnr : ∀ p, ¬ (supportGraph hn J.source J.target S).Reachable (.inr q) (.inl p))
    {q' : E × Fin n}
    (hr : (supportGraph hn J.source J.target S).Reachable (.inr q) (.inr q')) :
    h.2 q = h.2 q' := by
  have walk_prop {v w : Vertex P E n}
      (p : (supportGraph hn J.source J.target S).Walk v w)
      (hv : ∃ qv, v = .inr qv ∧ h.2 q = h.2 qv)
      (hreach : (supportGraph hn J.source J.target S).Reachable (.inr q) v) :
      ∃ qw, w = .inr qw ∧ h.2 q = h.2 qw := by
    induction p with
    | nil => exact hv
    | @cons v u w hadj p ih =>
      obtain ⟨qv,rfl,hv⟩ := hv
      have hu := hreach.trans hadj.reachable
      obtain ⟨qu,rfl⟩ : ∃ qu, u = .inr qu := by
        cases u with
        | inl real => exact (hnr real hu).elim
        | inr qu => exact ⟨qu,rfl⟩
      exact ih ⟨qu,rfl,hv.trans (J.internal_adj_values hn S h hh hadj)⟩ hu
  obtain ⟨qw,he,hh'⟩ := walk_prop hr.some ⟨q,rfl,rfl⟩ (.refl _)
  cases Sum.inr.inj he
  exact hh'
end VariableWL.ProductImages.Instance

namespace VariableWL.ProductImages.Instance
open Subdivision
variable {r n : ℕ} {P : Type uVariable11} {E : Type uVariable12} (J : ProductImages.Instance r P E)

theorem bool_perm_eq_of_apply {f g : Equiv.Perm Bool} {a : Bool}
    (h : f a = g a) : f = g := by
  ext b
  by_cases hb : b = a
  · simpa only [hb] using h
  · have hf : f b ≠ f a := f.injective.ne hb
    have hg : g b ≠ g a := g.injective.ne hb
    rw [h] at hf
    exact (show ∀ x y z : Bool, x ≠ z → y ≠ z → x = y by decide) _ _ _ hf hg

noncomputable def transport (l : Link E n) (i : Fin r) : Equiv.Perm Bool :=
  if l.2.val = n then J.ambient l.1 i else Equiv.refl _

theorem alignment_link (hn : 0 < n) (cut : E → Fin (n+1))
    (l : Link E n) (hc : l.2 ≠ cut l.1) (i : Fin r) :
    J.alignment cut (left J.source l) i =
      J.alignment cut (right J.target l) i * J.transport l i := by
  obtain ⟨a,ha⟩ := J.domain_nonempty l.1 i
  apply bool_perm_eq_of_apply (a := a)
  have he := J.alignment_match hn cut l hc i
    (a := a) (b := if l.2.val = n then J.map l.1 i a else a) ⟨ha,rfl⟩
  by_cases hl : l.2.val = n
  · simpa only [transport, ite_eq_left hl, Equiv.Perm.coe_mul, Function.comp_apply,
      J.ambient_on_domain _ _ _ ha] using he
  · simpa only [transport, ite_eq_right hl, Equiv.Perm.coe_mul, Function.comp_apply,
      Equiv.refl_apply] using he

noncomputable def relativeAlignment (cut cut' : E → Fin (n+1))
    (v : Vertex P E n) (i : Fin r) : Equiv.Perm Bool :=
  J.alignment cut v i * (J.alignment cut' v i)⁻¹

theorem relativeAlignment_link (hn : 0 < n) (cut cut' : E → Fin (n+1))
    (l : Link E n) (hc : l.2 ≠ cut l.1) (hc' : l.2 ≠ cut' l.1) (i : Fin r) :
    J.relativeAlignment cut cut' (left J.source l) i =
      J.relativeAlignment cut cut' (right J.target l) i := by
  unfold relativeAlignment
  rw [J.alignment_link hn cut l hc i, J.alignment_link hn cut' l hc' i]
  simp only [mul_inv_rev, mul_assoc, mul_inv_cancel_left]

theorem relativeAlignment_reachable (hn : 0 < n) (S : Set (Link E n))
    (cut cut' : E → Fin (n+1))
    (hc : ∀ l ∈ S, l.2 ≠ cut l.1) (hc' : ∀ l ∈ S, l.2 ≠ cut' l.1)
    {v w : Vertex P E n} (h : (supportGraph hn J.source J.target S).Reachable v w)
    (i : Fin r) : J.relativeAlignment cut cut' v i = J.relativeAlignment cut cut' w i := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons ha _ ih =>
    apply Eq.trans _ ih
    obtain ⟨l,hl,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := ha
    · exact J.relativeAlignment_link hn cut cut' l (hc l hl) (hc' l hl) i
    · exact (J.relativeAlignment_link hn cut cut' l (hc l hl) (hc' l hl) i).symm
end VariableWL.ProductImages.Instance

end OAI
