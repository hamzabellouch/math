import OAI.Computability.WeisfeilerLeman.Colors

namespace OAI

universe uV uE uF

namespace WLTime.Compression

abbrev F₂ := ZMod 2

variable {V : Type uV} {G : SimpleGraph V}

def walkWeight (mark : V → V → F₂) : {u v : V} → G.Walk u v → F₂
  | _, _, .nil => 0
  | _, _, @SimpleGraph.Walk.cons _ _ u v _ _ p => mark u v + walkWeight mark p

@[simp] theorem walkWeight_nil (mark : V → V → F₂) (v : V) :
    walkWeight mark (G := G) (.nil : G.Walk v v) = 0 := rfl

@[simp] theorem walkWeight_cons (mark : V → V → F₂) {u v w : V}
    (h : G.Adj u v) (p : G.Walk v w) :
    walkWeight mark (.cons h p) = mark u v + walkWeight mark p := rfl

@[simp] theorem walkWeight_append (mark : V → V → F₂) {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) :
    walkWeight mark (p.append q) = walkWeight mark p + walkWeight mark q := by
  induction p with
  | nil => simp [walkWeight]
  | @cons u v w h p ih => simp [walkWeight, ih, add_assoc]

@[simp] theorem walkWeight_reverse (mark : V → V → F₂)
    (hsymm : ∀ u v, G.Adj u v → mark u v = mark v u)
    {u v : V} (p : G.Walk u v) :
    walkWeight mark p.reverse = walkWeight mark p := by
  induction p with
  | nil => rfl
  | @cons u v w h p ih =>
    simp [SimpleGraph.Walk.reverse_cons, ih, hsymm u v h, add_comm]

theorem walkWeight_independent (mark : V → V → F₂)
    (hsymm : ∀ u v, G.Adj u v → mark u v = mark v u)
    (hclosed : ∀ v (p : G.Walk v v), walkWeight mark p = 0)
    {u v : V} (p q : G.Walk u v) : walkWeight mark p = walkWeight mark q := by
  have h := hclosed u (p.append q.reverse)
  simp only [walkWeight_append, walkWeight_reverse mark hsymm] at h
  have hz := CharTwo.add_self_eq_zero (walkWeight mark q)
  exact add_right_cancel (h.trans hz.symm)

theorem walkWeight_congr (mark mark' : V → V → F₂)
    (h : ∀ u v, G.Adj u v → mark u v = mark' u v)
    {u v : V} (p : G.Walk u v) : walkWeight mark p = walkWeight mark' p := by
  induction p with
  | nil => rfl
  | cons e p ih => simp only [walkWeight_cons, h _ _ e, ih]

@[simp] theorem walkWeight_zero {u v : V} (p : G.Walk u v) :
    walkWeight (fun _ _ => 0) p = 0 := by
  induction p with
  | nil => rfl
  | cons e p ih => simp only [walkWeight_cons, zero_add, ih]

@[simp] theorem walkWeight_add (a b : V → V → F₂) {u v : V} (p : G.Walk u v) :
    walkWeight (fun u v => a u v + b u v) p = walkWeight a p + walkWeight b p := by
  induction p with
  | nil => simp
  | cons e p ih => simp only [walkWeight_cons, ih]; abel

@[simp] theorem walkWeight_mul (a : V → V → F₂) (c : F₂)
    {u v : V} (p : G.Walk u v) :
    walkWeight (fun u v => c * a u v) p = c * walkWeight a p := by
  induction p with
  | nil => simp
  | cons e p ih => simp only [walkWeight_cons, ih, mul_add]

@[simp] theorem walkWeight_coboundary (s : V → F₂) {u v : V} (p : G.Walk u v) :
    walkWeight (fun u v => s u + s v) p = s u + s v := by
  induction p with
  | nil => simp [CharTwo.add_self_eq_zero]
  | @cons a b c e p ih =>
    simp only [walkWeight_cons, ih]
    calc
      _ = s a + (s b + s b) + s c := by abel
      _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]

noncomputable def potentialFrom (mark : V → V → F₂) (root v : V) : F₂ := by
  classical
  exact if h : G.Reachable root v then walkWeight mark h.some else 0

theorem potentialFrom_edge (mark : V → V → F₂)
    (hsymm : ∀ u v, G.Adj u v → mark u v = mark v u)
    (hclosed : ∀ v (p : G.Walk v v), walkWeight mark p = 0)
    {root u v : V} (hu : G.Reachable root u) (h : G.Adj u v) :
    potentialFrom (G := G) mark root u + potentialFrom (G := G) mark root v = mark u v := by
  classical
  have hv := hu.trans h.reachable
  simp only [potentialFrom, dite_eq_left hu, dite_eq_left hv]
  have hp := walkWeight_independent mark hsymm hclosed
    (hu.some.append (.cons h .nil)) hv.some
  simp only [walkWeight_append, walkWeight_cons, walkWeight_nil, add_zero] at hp
  rw [← hp, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

theorem exists_seam_potential (mark : V → V → F₂)
    (hsymm : ∀ u v, G.Adj u v → mark u v = mark v u)
    (hclosed : ∀ v (p : G.Walk v v), walkWeight mark p = 0) :
    ∃ s : V → F₂, ∀ u v, G.Adj u v → s u + s v = mark u v := by
  classical
  let root (v : V) : V := (G.connectedComponentMk v).out
  have hroot (v : V) : G.Reachable (root v) v :=
    SimpleGraph.ConnectedComponent.eq.mp (Quot.out_eq (G.connectedComponentMk v))
  refine ⟨fun v => potentialFrom (G := G) mark (root v) v, ?_⟩
  intro u v huv
  have heq : root u = root v :=
    congrArg Quot.out (SimpleGraph.ConnectedComponent.eq.mpr huv.reachable)
  change potentialFrom mark (root u) u + potentialFrom mark (root v) v = mark u v
  rw [← heq]
  exact potentialFrom_edge mark hsymm hclosed (hroot u) huv

section ReadoutAlgebra

variable {E : Type uE} {F : Type uF} [AddCommGroup E] [Module F₂ E]
  [AddCommGroup F] [Module F₂ F]

def horizontalReadout (left right shift : E) (seam : F₂) : E :=
  left + right + seam • shift

def verticalReadout (L : E →ₗ[F₂] F₂) (R : F →ₗ[F₂] F₂)
    (left : E) (right : F) : F₂ := L left + R right

theorem horizontal_adjustment (left right oldShift newShift : E)
    (s t seam : F₂) (hst : s + t = seam) :
    horizontalReadout (left + s • (oldShift - newShift))
      (right + t • (oldShift - newShift)) newShift seam =
        horizontalReadout left right oldShift seam := by
  unfold horizontalReadout
  calc
    _ = left + right + (s + t) • (oldShift - newShift) + seam • newShift := by
      module
    _ = _ := by rw [hst, smul_sub]; abel

theorem homogeneous_shift_difference (L : E →ₗ[F₂] F₂) (R : F →ₗ[F₂] F₂)
    (oldLeft newLeft : E) (oldRight newRight : F) (b : F₂)
    (ho : L oldLeft + R oldRight = b) (hn : L newLeft + R newRight = b) :
    L (oldLeft - newLeft) + R (oldRight - newRight) = 0 := by
  simp only [map_sub]
  linear_combination ho - hn

theorem vertical_adjustment (L : E →ₗ[F₂] F₂) (R : F →ₗ[F₂] F₂)
    (left gLeft : E) (right gRight : F) (s : F₂)
    (hg : L gLeft + R gRight = 0) :
    verticalReadout L R (left + s • gLeft) (right + s • gRight) =
      verticalReadout L R left right := by
  simp only [verticalReadout, map_add, map_smul, smul_eq_mul]
  linear_combination s * hg

theorem square_readouts_legal (L : E →ₗ[F₂] F₂) (R : F →ₗ[F₂] F₂)
    (left₀ left₁ shiftLeft : E) (right₀ right₁ shiftRight : F) (seam b : F₂)
    (hlink : L shiftLeft + R shiftRight = b) :
    L (horizontalReadout left₀ left₁ shiftLeft seam) +
      R (horizontalReadout right₀ right₁ shiftRight seam) +
      verticalReadout L R left₀ right₀ + verticalReadout L R left₁ right₁ =
        seam * b := by
  simp only [horizontalReadout, verticalReadout, map_add, map_smul, smul_eq_mul]
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) seam * hlink

end ReadoutAlgebra

end WLTime.Compression

end OAI
