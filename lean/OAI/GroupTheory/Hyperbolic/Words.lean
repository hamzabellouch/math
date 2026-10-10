import OAI.GroupTheory.Hyperbolic.TriangleFilling

namespace OAI

namespace Release075
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

inductive WordPath (flip : E → E) (color : E → V) : V → V → List E → Prop
  | nil (v : V) : WordPath flip color v v []
  | cons (e : E) {v : V} {w : List E} : WordPath flip color (color e) v w →
      WordPath flip color (color (flip e)) v (e::w)

def reverseWord (flip : E → E) (w : List E) : List E := w.reverse.map flip

@[simp] theorem reverseWord_nil : reverseWord flip [] = [] := rfl
@[simp] theorem reverseWord_cons (e : E) (w : List E) :
    reverseWord flip (e::w) = reverseWord flip w ++ [flip e] := by
  simp [reverseWord]
@[simp] theorem reverseWord_append (w z : List E) :
    reverseWord flip (w++z) = reverseWord flip z ++ reverseWord flip w := by
  simp [reverseWord]

theorem reverseWord_reverse (hi : Function.Involutive flip) (w : List E) :
    reverseWord flip (reverseWord flip w) = w := by
  simp only [reverseWord,List.map_reverse,List.reverse_reverse,List.map_map]
  rw [show flip ∘ flip = id from funext hi]
  exact List.map_id w

namespace WordPath
variable {a b c : V} {u v : List E}

theorem source {e : E} {w : List E} (h : WordPath flip color a b (e::w)) :
    color (flip e) = a := by cases h; rfl

theorem append (h : WordPath flip color a b u) (h' : WordPath flip color b c v) :
    WordPath flip color a c (u++v) := by
  induction h with
  | nil => exact h'
  | cons e _ ih => exact .cons e (ih h')

theorem singleton (e : E) : WordPath flip color (color (flip e)) (color e) [e] :=
  .cons e (.nil _)

theorem reverse (hi : Function.Involutive flip) (h : WordPath flip color a b u) :
    WordPath flip color b a (reverseWord flip u) := by
  induction h with
  | nil => exact .nil _
  | cons e _ ih =>
    rw [reverseWord_cons]
    apply ih.append
    have hh := singleton (color := color) (flip := flip) (flip e)
    rwa [hi] at hh

end WordPath

namespace Fillable
variable (hi : Function.Involutive flip)
variable (hn : ∀ e, color e ≠ color (flip e))

include hi hn in
/-- Erase a reversed path followed by the path, in any boundary context. -/
theorem erase_reverse (u v p : List E)
    (h : Fillable flip color face (u ++ reverseWord flip p ++ p ++ v)) :
    Fillable flip color face (u++v) := by
  induction p generalizing u with
  | nil => simpa only [reverseWord_nil,List.append_nil,List.nil_append] using h
  | cons e p ih =>
    simp only [reverseWord_cons,List.append_assoc,List.singleton_append] at h
    have h' : Fillable flip color face
        ((u++reverseWord flip p) ++ flip e :: flip (flip e) :: (p++v)) := by
      rw [hi e]
      simpa only [List.append_assoc,List.cons_append] using h
    exact ih u (by simpa only [List.append_assoc] using
      (h'.erase hi hn (u++reverseWord flip p) (p++v) (flip e)))

include hi in
/-- Attach a whole typed stem; each corner identification is type checked. -/
theorem stemPath {a b : V} {p w : List E} (hp : WordPath flip color a b p)
    (hw : WordPath flip color b b w) (h : Fillable flip color face w) :
    Fillable flip color face (p++w++reverseWord flip p) := by
  induction hp with
  | nil => simpa only [reverseWord_nil,List.nil_append,List.append_nil] using h
  | @cons e b p hp ih =>
    have hloop : WordPath flip color (color e) (color e)
        (p++w++reverseWord flip p) := (hp.append hw).append (hp.reverse hi)
    have hh := (ih hw).stem hi e (fun x xs hx => by
      rw [hx] at hloop
      exact hloop.source)
    simpa only [reverseWord_cons,List.cons_append,List.append_assoc] using hh

include hi in
theorem palindrome {a b : V} {p : List E} (hp : WordPath flip color a b p) :
    Fillable flip color face (p++reverseWord flip p) := by
  simpa only [List.append_nil] using (stemPath hi hp (.nil b)
    (empty (flip := flip) (color := color) (face := face)))

end Fillable

/-- Filling the two paths glued along their common endpoints. -/
def FilledBetween (flip : E → E) (color : E → V) (face : E → E → E → Prop)
    (p q : List E) : Prop := Fillable flip color face (p++reverseWord flip q)

namespace FilledBetween
variable (hi : Function.Involutive flip)
variable (hn : ∀ e, color e ≠ color (flip e))
variable (hf : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
variable {a b c d : V} {p q r u v : List E}

include hi in
theorem refl (hp : WordPath flip color a b p) : FilledBetween flip color face p p :=
  Fillable.palindrome hi hp

include hi hf in
theorem symm (h : FilledBetween flip color face p q) : FilledBetween flip color face q p := by
  have hm := Fillable.mirror h hi hf
  change Fillable flip color face (reverseWord flip (p++reverseWord flip q)) at hm
  simpa only [FilledBetween,reverseWord_append,reverseWord_reverse hi] using hm

include hi hn in
theorem trans (hp : WordPath flip color a b p) (hq : WordPath flip color a b q)
    (hr : WordPath flip color a b r)
    (h : FilledBetween flip color face p q) (h' : FilledBetween flip color face q r) :
    FilledBetween flip color face p r := by
  have hloop := hp.append (hq.reverse hi)
  have hloop' := hq.append (hr.reverse hi)
  have hh := Fillable.app h h' (by
    intro e es f fs he hf
    rw [he] at hloop
    rw [hf] at hloop'
    exact hloop.source.trans hloop'.source.symm)
  apply Fillable.erase_reverse hi hn p (reverseWord flip r) q
  simpa only [List.append_assoc] using hh

include hi in
theorem whiskerLeft (hu : WordPath flip color c a u)
    (hp : WordPath flip color a b p) (hq : WordPath flip color a b q)
    (h : FilledBetween flip color face p q) :
    FilledBetween flip color face (u++p) (u++q) := by
  have hh := Fillable.stemPath hi hu (hp.append (hq.reverse hi)) h
  simpa only [FilledBetween,reverseWord_append,List.append_assoc] using hh

include hi in
theorem whiskerRight (hp : WordPath flip color a b p) (hq : WordPath flip color a b q)
    (hv : WordPath flip color b c v) (h : FilledBetween flip color face p q) :
    FilledBetween flip color face (p++v) (q++v) := by
  have h' : FilledBetween flip color face (reverseWord flip q) (reverseWord flip p) := by
    simpa only [FilledBetween,reverseWord_reverse hi] using
      (Fillable.rotateAppend (u := p) (v := reverseWord flip q) h)
  have hh := whiskerLeft hi (hv.reverse hi) (hq.reverse hi) (hp.reverse hi) h'
  have hh' := Fillable.rotateAppend hh
  simpa only [FilledBetween,reverseWord_append,reverseWord_reverse hi,List.append_assoc] using hh'

end FilledBetween
end Release075

namespace Release075.BlockPresentation
open CategoryTheory
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

abbrev OrientedEdge := d.Edge × Bool

def flipEdge : d.OrientedEdge → d.OrientedEdge := fun ⟨e,s⟩ => (e,!s)

@[simp] theorem flipEdge_flipEdge (e : d.OrientedEdge) : d.flipEdge (d.flipEdge e) = e := by
  rcases e with ⟨e,s⟩
  cases s <;> rfl

def edgeTarget : d.OrientedEdge → d.Vertex
  | (.inl _, true) => .w
  | (.inl _, false) => .v
  | (.inr (.inl _), true) => .v
  | (.inr (.inl _), false) => .o
  | (.inr (.inr _), true) => .w
  | (.inr (.inr _), false) => .o

theorem edgeTarget_ne (e : d.OrientedEdge) : d.edgeTarget e ≠ d.edgeTarget (d.flipEdge e) := by
  rcases e with ⟨e,s⟩
  rcases e with x|l|rr <;> cases s <;> simp [edgeTarget,flipEdge]

def arrowLabel {a c : d.Vertex} : d.Arrow a c → d.Edge
  | .x e => .inl e
  | .l e => .inr (.inl e)
  | .rr e => .inr (.inr e)

def orientedLabel {a c : Quiver.Symmetrify d.Vertex} (f : a ⟶ c) : d.OrientedEdge :=
  match f with
  | .inl e => (d.arrowLabel e,true)
  | .inr e => (d.arrowLabel e,false)

@[simp] theorem orientedLabel_reverse {a c : Quiver.Symmetrify d.Vertex} (f : a ⟶ c) :
    d.orientedLabel (Quiver.reverse f) = d.flipEdge (d.orientedLabel f) := by
  change d.Arrow a c ⊕ d.Arrow c a at f
  cases f <;> rfl

@[simp] theorem orientedLabel_target {a c : Quiver.Symmetrify d.Vertex} (f : a ⟶ c) :
    d.edgeTarget (d.orientedLabel f) = c := by
  change d.Arrow a c ⊕ d.Arrow c a at f
  rcases f with f|f
  · change d.Arrow a c at f
    cases f <;> rfl
  · change d.Arrow c a at f
    cases f <;> rfl

@[simp] theorem orientedLabel_source {a c : Quiver.Symmetrify d.Vertex} (f : a ⟶ c) :
    d.edgeTarget (d.flipEdge (d.orientedLabel f)) = a := by
  rw [← d.orientedLabel_reverse]
  exact d.orientedLabel_target _

def rawWord {a : Quiver.Symmetrify d.Vertex} :
    ∀ {c : Quiver.Symmetrify d.Vertex},
      @Quiver.Path (Quiver.Symmetrify d.Vertex) (Quiver.symmetrifyQuiver d.Vertex) a c →
        List d.OrientedEdge
  | _, .nil => []
  | _, .cons p f => rawWord p ++ [d.orientedLabel f]

@[simp] theorem rawWord_nil (a : d.RawPaths) : d.rawWord (𝟙 a) = [] := rfl

@[simp] theorem rawWord_comp {a b c : d.RawPaths} (p : a ⟶ b) (q : b ⟶ c) :
    d.rawWord (p ≫ q) = d.rawWord p ++ d.rawWord q := by
  change @Quiver.Path (Quiver.Symmetrify d.Vertex) (Quiver.symmetrifyQuiver d.Vertex) b c at q
  induction q with
  | nil =>
    change d.rawWord p = d.rawWord p ++ []
    exact (List.append_nil _).symm
  | cons q f ih =>
    change d.rawWord (p ≫ q) ++ [d.orientedLabel f] =
      d.rawWord p ++ (d.rawWord q ++ [d.orientedLabel f])
    rw [ih,List.append_assoc]

theorem rawWord_path_comp {a b c : Quiver.Symmetrify d.Vertex}
    (p : Quiver.Path a b) (q : Quiver.Path b c) :
    d.rawWord (p.comp q) = d.rawWord p ++ d.rawWord q := by
  induction q with
  | nil => exact (List.append_nil _).symm
  | cons q f ih =>
    change d.rawWord (p.comp q) ++ [d.orientedLabel f] =
      d.rawWord p ++ (d.rawWord q ++ [d.orientedLabel f])
    rw [ih,List.append_assoc]

@[simp] theorem rawWord_toPath {a c : Quiver.Symmetrify d.Vertex} (f : a ⟶ c) :
    d.rawWord f.toPath = [d.orientedLabel f] := rfl

@[simp] theorem rawWord_reverse {a c : Quiver.Symmetrify d.Vertex}
    (p : Quiver.Path a c) :
    d.rawWord p.reverse = reverseWord d.flipEdge (d.rawWord p) := by
  change @Quiver.Path (Quiver.Symmetrify d.Vertex) (Quiver.symmetrifyQuiver d.Vertex) a c at p
  induction p with
  | nil => rfl
  | cons p f ih =>
    change d.rawWord (Quiver.Path.comp (Quiver.reverse f).toPath p.reverse) =
      reverseWord d.flipEdge (d.rawWord p ++ [d.orientedLabel f])
    rw [d.rawWord_path_comp,d.rawWord_toPath,d.orientedLabel_reverse,ih]
    simp only [reverseWord_append,reverseWord_cons,reverseWord_nil,List.nil_append]

theorem rawWord_typed {a c : Quiver.Symmetrify d.Vertex} (p : Quiver.Path a c) :
    WordPath d.flipEdge d.edgeTarget a c (d.rawWord p) := by
  change @Quiver.Path (Quiver.Symmetrify d.Vertex) (Quiver.symmetrifyQuiver d.Vertex) a c at p
  induction p with
  | nil => exact .nil _
  | cons p f ih =>
    apply ih.append
    have hs := d.orientedLabel_source f
    have ht := d.orientedLabel_target f
    have hh := WordPath.singleton (flip := d.flipEdge) (color := d.edgeTarget) (d.orientedLabel f)
    simpa only [hs,ht] using hh

def orientedL (b : B) (i : (d.block b).labels) (u v : Fin r) : d.OrientedEdge :=
  (.inr (.inl ⟨b,u,((d.block b).coordinates i).1 + (v.val : ZMod (d.block b).s)⟩),true)
def orientedX (i : I) (u v : Fin r) : d.OrientedEdge := (.inl (i,u,v),true)
def orientedR (b : B) (i : (d.block b).labels) (u v : Fin r) : d.OrientedEdge :=
  (.inr (.inr ⟨b,v,((d.block b).coordinates i).2 + (u.val : ZMod (d.block b).t)⟩),true)

inductive TriangleFace : d.OrientedEdge → d.OrientedEdge → d.OrientedEdge → Prop
  | pos₀ (b : B) (i : (d.block b).labels) (u v : Fin r) :
    TriangleFace (d.orientedL b i u v) (d.orientedX i u v) (d.flipEdge (d.orientedR b i u v))
  | pos₁ (b : B) (i : (d.block b).labels) (u v : Fin r) :
    TriangleFace (d.orientedX i u v) (d.flipEdge (d.orientedR b i u v)) (d.orientedL b i u v)
  | pos₂ (b : B) (i : (d.block b).labels) (u v : Fin r) :
    TriangleFace (d.flipEdge (d.orientedR b i u v)) (d.orientedL b i u v) (d.orientedX i u v)
  | neg₀ (b : B) (i : (d.block b).labels) (u v : Fin r) :
    TriangleFace (d.flipEdge (d.orientedL b i u v)) (d.orientedR b i u v) (d.flipEdge (d.orientedX i u v))
  | neg₁ (b : B) (i : (d.block b).labels) (u v : Fin r) :
    TriangleFace (d.orientedR b i u v) (d.flipEdge (d.orientedX i u v)) (d.flipEdge (d.orientedL b i u v))
  | neg₂ (b : B) (i : (d.block b).labels) (u v : Fin r) :
    TriangleFace (d.flipEdge (d.orientedX i u v)) (d.flipEdge (d.orientedL b i u v)) (d.orientedR b i u v)

theorem TriangleFace.rotate {a b c : d.OrientedEdge} (h : d.TriangleFace a b c) :
    d.TriangleFace b c a := by
  cases h with
  | pos₀ b i u v => exact .pos₁ b i u v
  | pos₁ b i u v => exact .pos₂ b i u v
  | pos₂ b i u v => exact .pos₀ b i u v
  | neg₀ b i u v => exact .neg₁ b i u v
  | neg₁ b i u v => exact .neg₂ b i u v
  | neg₂ b i u v => exact .neg₀ b i u v

theorem TriangleFace.mirror {a b c : d.OrientedEdge} (h : d.TriangleFace a b c) :
    d.TriangleFace (d.flipEdge a) (d.flipEdge c) (d.flipEdge b) := by
  cases h with
  | pos₀ b i u v => simpa only [flipEdge_flipEdge] using TriangleFace.neg₀ (d := d) b i u v
  | pos₁ b i u v => simpa only [flipEdge_flipEdge] using TriangleFace.neg₂ (d := d) b i u v
  | pos₂ b i u v => simpa only [flipEdge_flipEdge] using TriangleFace.neg₁ (d := d) b i u v
  | neg₀ b i u v => simpa only [flipEdge_flipEdge] using TriangleFace.pos₀ (d := d) b i u v
  | neg₁ b i u v => simpa only [flipEdge_flipEdge] using TriangleFace.pos₂ (d := d) b i u v
  | neg₂ b i u v => simpa only [flipEdge_flipEdge] using TriangleFace.pos₁ (d := d) b i u v

theorem rawMove_filled {a c : d.RawPaths} {p q : a ⟶ c} (h : d.RawMove p q) :
    FilledBetween d.flipEdge d.edgeTarget d.TriangleFace (d.rawWord p) (d.rawWord q) := by
  cases h with
  | backtrack h =>
    cases h with
    | step a c f =>
      change Fillable d.flipEdge d.edgeTarget d.TriangleFace
        (reverseWord d.flipEdge [d.orientedLabel f,d.orientedLabel (Quiver.reverse f)])
      rw [d.orientedLabel_reverse]
      simp only [reverseWord_cons,reverseWord_nil,List.nil_append,
        flipEdge_flipEdge,List.singleton_append]
      exact ⟨TriangleFilling.backtrack (d.flipEdge_flipEdge) (d.orientedLabel f)⟩
  | triangle b i u v =>
    change Nonempty (TriangleFilling d.flipEdge d.edgeTarget d.TriangleFace
      [d.orientedL b i u v, d.orientedX i u v, d.flipEdge (d.orientedR b i u v)])
    exact ⟨TriangleFilling.triangle d.flipEdge_flipEdge (fun _ _ _ => TriangleFace.rotate d)
      _ _ _ rfl rfl rfl (by simpa only [flipEdge_flipEdge] using TriangleFace.neg₀ (d := d) b i u v)⟩

theorem rawHomotopic_filled {a c : d.RawPaths} {p q : a ⟶ c} (h : d.RawHomotopic p q) :
    FilledBetween d.flipEdge d.edgeTarget d.TriangleFace (d.rawWord p) (d.rawWord q) := by
  induction h with
  | rel p q h =>
    cases h with
    | intro a c u p q v h =>
      rw [d.rawWord_comp,d.rawWord_comp,d.rawWord_comp,d.rawWord_comp]
      exact FilledBetween.whiskerLeft d.flipEdge_flipEdge (d.rawWord_typed u)
        ((d.rawWord_typed p).append (d.rawWord_typed v))
        ((d.rawWord_typed q).append (d.rawWord_typed v))
        (FilledBetween.whiskerRight d.flipEdge_flipEdge (d.rawWord_typed p)
          (d.rawWord_typed q) (d.rawWord_typed v) (d.rawMove_filled h))
  | refl p => exact FilledBetween.refl d.flipEdge_flipEdge (d.rawWord_typed p)
  | symm p q _ ih =>
    exact FilledBetween.symm d.flipEdge_flipEdge
      (fun _ _ _ => TriangleFace.mirror d) ih
  | trans p q s _ _ ih ih' =>
    exact FilledBetween.trans d.flipEdge_flipEdge d.edgeTarget_ne
      (d.rawWord_typed p) (d.rawWord_typed q) (d.rawWord_typed s) ih ih'

theorem nullhomotopic_fillable {a : d.RawPaths} {p : a ⟶ a} (h : d.RawHomotopic p (𝟙 a)) :
    Fillable d.flipEdge d.edgeTarget d.TriangleFace (d.rawWord p) := by
  simpa only [FilledBetween,rawWord_nil,reverseWord_nil,List.append_nil] using
    d.rawHomotopic_filled h

/-- The actual presented rectangular word, if trivial, has a finite labelled
planar triangular filling. This lemma has no geometric hypothesis. -/
theorem rectangle_fillable_of_eq_one (i : I) (u u' v v' : Fin r)
    (h : d.x i u v * (d.x i u' v)⁻¹ * d.x i u' v' * (d.x i u v')⁻¹ = 1) :
    Fillable d.flipEdge d.edgeTarget d.TriangleFace
      [d.orientedX i u v, d.flipEdge (d.orientedX i u' v),
       d.orientedX i u' v', d.flipEdge (d.orientedX i u v')] := by
  exact d.nullhomotopic_fillable (d.rawRectangle_nullhomotopic_of_eq_one i u u' v v' h)

end Release075.BlockPresentation

namespace Release075.BlockPresentation
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

def vertexColor : d.Vertex ≃ Fin 3 where
  toFun | .o => 0 | .v => 1 | .w => 2
  invFun j := if j = 0 then .o else if j = 1 then .v else .w
  left_inv a := by cases a <;> rfl
  right_inv j := by fin_cases j <;> rfl

theorem TriangleFace.colors {a b c : d.OrientedEdge} (h : d.TriangleFace a b c) :
    d.edgeTarget a ≠ d.edgeTarget b ∧ d.edgeTarget b ≠ d.edgeTarget c ∧
    d.edgeTarget c ≠ d.edgeTarget a := by
  cases h <;> simp [orientedL,orientedX,orientedR,flipEdge,edgeTarget]

theorem TriangleFace.typed {a b c : d.OrientedEdge} (h : d.TriangleFace a b c) :
    d.edgeTarget (d.flipEdge b) = d.edgeTarget a ∧
    d.edgeTarget (d.flipEdge c) = d.edgeTarget b ∧
    d.edgeTarget (d.flipEdge a) = d.edgeTarget c := by
  cases h <;> simp [orientedL,orientedX,orientedR,flipEdge,edgeTarget]

theorem TriangleFace.unique_aux {a b c a' b' c' : d.OrientedEdge}
    (h : d.TriangleFace a b c) (h' : d.TriangleFace a' b' c')
    (ha : a = a') (hb : b = b') : c = c' := by
  cases h <;> cases h' <;>
    simp only [orientedL,orientedX,orientedR,flipEdge,Prod.mk.injEq,
      Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,
      Bool.not_true,and_true,false_and] at ha hb ⊢
  all_goals
    first
    | have hbb := congrArg Sigma.fst ha; cases hbb
    | have hbb := congrArg Sigma.fst hb; cases hbb
  all_goals simp only [Sigma.mk.inj_iff,heq_eq_eq,Prod.mk.injEq,Subtype.val_inj,true_and] at ha hb ⊢
  case pos₀.pos₀ b i u v u' v' i' =>
    rcases hb with ⟨rfl,rfl,rfl⟩
    simp
  case pos₁.pos₁ b i u v u' v' i' =>
    rcases ha with ⟨rfl,rfl,rfl⟩
    simp
  case pos₂.pos₂ b i u v u' v' i' =>
    rcases ha with ⟨rfl,hβ⟩
    rcases hb with ⟨rfl,hα⟩
    have hi := (d.block b).coordinates.injective
      (Prod.ext (add_right_cancel hα) (add_right_cancel hβ))
    subst i'
    exact ⟨rfl,rfl,rfl⟩
  case neg₀.neg₀ b i u v u' v' i' =>
    rcases ha with ⟨rfl,hα⟩
    rcases hb with ⟨rfl,hβ⟩
    have hi := (d.block b).coordinates.injective
      (Prod.ext (add_right_cancel hα) (add_right_cancel hβ))
    subst i'
    exact ⟨rfl,rfl,rfl⟩
  case neg₁.neg₁ b i u v u' v' i' =>
    rcases hb with ⟨rfl,rfl,rfl⟩
    simp
  case neg₂.neg₂ b i u v u' v' i' =>
    rcases ha with ⟨rfl,rfl,rfl⟩
    simp

theorem TriangleFace.unique {a b c c' : d.OrientedEdge}
    (h : d.TriangleFace a b c) (h' : d.TriangleFace a b c') : c = c' :=
  TriangleFace.unique_aux d h h' rfl rfl

end Release075.BlockPresentation

end OAI
