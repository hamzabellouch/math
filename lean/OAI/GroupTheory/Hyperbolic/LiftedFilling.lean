import OAI.GroupTheory.Hyperbolic.Rectangles

namespace OAI

namespace Release075.BlockPresentation
open CategoryTheory
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

/-- The signed displacement of an oriented original edge, with the two tree
edges already killed in the actual presentation. -/
def edgeValue (e : d.OrientedEdge) : d.GroupType :=
  if e.2 then d.edge e.1 else (d.edge e.1)⁻¹

@[simp] theorem edgeValue_flip (e : d.OrientedEdge) :
    d.edgeValue (d.flipEdge e) = (d.edgeValue e)⁻¹ := by
  rcases e with ⟨e,s⟩
  cases s <;> simp [edgeValue,flipEdge]

def wordValue (w : List d.OrientedEdge) : d.GroupType := (w.map d.edgeValue).prod

@[simp] theorem wordValue_nil : d.wordValue [] = 1 := rfl
@[simp] theorem wordValue_cons (e : d.OrientedEdge) (w : List d.OrientedEdge) :
    d.wordValue (e::w) = d.edgeValue e * d.wordValue w := rfl
@[simp] theorem wordValue_append (u v : List d.OrientedEdge) :
    d.wordValue (u++v) = d.wordValue u * d.wordValue v := by
  simp only [wordValue,List.map_append,List.prod_append]

abbrev LiftedEdge := d.OrientedEdge × d.GroupType
abbrev LiftedVertex := d.Vertex × d.GroupType

def liftedFlip (e : d.LiftedEdge) : d.LiftedEdge :=
  (d.flipEdge e.1,e.2 * (d.edgeValue e.1)⁻¹)

def liftedTarget (e : d.LiftedEdge) : d.LiftedVertex := (d.edgeTarget e.1,e.2)

@[simp] theorem liftedFlip_flip (e : d.LiftedEdge) :
    d.liftedFlip (d.liftedFlip e) = e := by
  rcases e with ⟨e,g⟩
  simp [liftedFlip]

theorem liftedTarget_ne (e : d.LiftedEdge) :
    d.liftedTarget e ≠ d.liftedTarget (d.liftedFlip e) := by
  intro h
  exact d.edgeTarget_ne e.1 (congrArg Prod.fst h)

/-- A genuine lift of a triangular face: all three corners are glued at the
same group coordinates, not merely at the same original vertex colors. -/
def LiftedFace (a b c : d.LiftedEdge) : Prop :=
  d.TriangleFace a.1 b.1 c.1 ∧
  d.liftedTarget (d.liftedFlip b) = d.liftedTarget a ∧
  d.liftedTarget (d.liftedFlip c) = d.liftedTarget b ∧
  d.liftedTarget (d.liftedFlip a) = d.liftedTarget c

theorem LiftedFace.rotate {a b c : d.LiftedEdge} (h : d.LiftedFace a b c) :
    d.LiftedFace b c a := ⟨TriangleFace.rotate d h.1,h.2.2.1,h.2.2.2,h.2.1⟩

theorem LiftedFace.mirror {a b c : d.LiftedEdge} (h : d.LiftedFace a b c) :
    d.LiftedFace (d.liftedFlip a) (d.liftedFlip c) (d.liftedFlip b) := by
  refine ⟨TriangleFace.mirror d h.1,?_,?_,?_⟩
  · simpa only [liftedFlip_flip] using h.2.2.2.symm
  · simpa only [liftedFlip_flip] using h.2.2.1.symm
  · simpa only [liftedFlip_flip] using h.2.1.symm

theorem LiftedFace.colors {a b c : d.LiftedEdge} (h : d.LiftedFace a b c) :
    d.liftedTarget a ≠ d.liftedTarget b ∧ d.liftedTarget b ≠ d.liftedTarget c ∧
      d.liftedTarget c ≠ d.liftedTarget a := by
  obtain ⟨hab,hbc,hca⟩ := TriangleFace.colors d h.1
  exact ⟨fun he => hab (congrArg Prod.fst he),
    fun he => hbc (congrArg Prod.fst he),fun he => hca (congrArg Prod.fst he)⟩

theorem LiftedFace.unique {a b c c' : d.LiftedEdge}
    (h : d.LiftedFace a b c) (h' : d.LiftedFace a b c') : c = c' := by
  have hc : d.liftedTarget c = d.liftedTarget c' := h.2.2.2.symm.trans h'.2.2.2
  exact Prod.ext (TriangleFace.unique d h.1 h'.1)
    (congrArg (fun x : d.LiftedVertex => x.2) hc)

def liftWord (g : d.GroupType) : List d.OrientedEdge → List d.LiftedEdge
  | [] => []
  | e::w => (e,g*d.edgeValue e)::liftWord (g*d.edgeValue e) w

@[simp] theorem liftWord_nil (g : d.GroupType) : d.liftWord g [] = [] := rfl
@[simp] theorem liftWord_cons (g : d.GroupType) (e : d.OrientedEdge) (w) :
    d.liftWord g (e::w) = (e,g*d.edgeValue e)::d.liftWord (g*d.edgeValue e) w := rfl

@[simp] theorem liftWord_length (g : d.GroupType) (w) :
    (d.liftWord g w).length = w.length := by
  induction w generalizing g with
  | nil => rfl
  | cons e w ih => simp only [liftWord,List.length_cons,ih]

@[simp] theorem liftWord_forget (g : d.GroupType) (w) :
    (d.liftWord g w).map Prod.fst = w := by
  induction w generalizing g with
  | nil => rfl
  | cons e w ih => simp only [liftWord,List.map_cons,ih]

theorem liftWord_append (g : d.GroupType) (u v) :
    d.liftWord g (u++v) = d.liftWord g u ++ d.liftWord (g*d.wordValue u) v := by
  induction u generalizing g with
  | nil => simp only [List.nil_append,liftWord_nil,wordValue_nil,mul_one]
  | cons e u ih =>
    simp only [List.cons_append,liftWord_cons,ih,wordValue_cons,mul_assoc]

theorem liftWord_typed {a c : d.Vertex} {w : List d.OrientedEdge}
    (h : WordPath d.flipEdge d.edgeTarget a c w) (g : d.GroupType) :
    WordPath d.liftedFlip d.liftedTarget (a,g) (c,g*d.wordValue w) (d.liftWord g w) := by
  induction h generalizing g with
  | nil a => simpa only [wordValue_nil,mul_one,liftWord_nil] using
      (WordPath.nil (flip := d.liftedFlip) (color := d.liftedTarget) (a,g))
  | @cons e tgt w h ih =>
    simp only [liftWord_cons,wordValue_cons,← mul_assoc]
    have hh := WordPath.cons (e,g*d.edgeValue e) (ih _)
    simpa only [liftedTarget,liftedFlip,mul_inv_cancel_right] using hh

theorem TriangleFace.value {a b c : d.OrientedEdge} (h : d.TriangleFace a b c) :
    d.edgeValue a * d.edgeValue b * d.edgeValue c = 1 := by
  cases h <;>
    simp only [edgeValue,orientedL,orientedX,orientedR,flipEdge,Bool.not_true,
      Bool.false_eq_true,↓reduceIte]
  all_goals
    rw [show d.edge (.inl _) = _ from d.triangle_relation _ _ _ _]
  all_goals simp only [l,rr,edge] at *
  all_goals group

theorem TriangleFace.lift {a b c : d.OrientedEdge} (h : d.TriangleFace a b c)
    (g : d.GroupType) :
    d.LiftedFace (a,g*d.edgeValue a) (b,g*d.edgeValue a*d.edgeValue b) (c,g) := by
  obtain ⟨hab,hbc,hca⟩ := TriangleFace.typed d h
  have hv := TriangleFace.value d h
  refine ⟨h,Prod.ext hab ?_,Prod.ext hbc ?_,Prod.ext hca ?_⟩
  · change g*d.edgeValue a*d.edgeValue b*(d.edgeValue b)⁻¹ = g*d.edgeValue a
    group
  · change g*(d.edgeValue c)⁻¹ = g*d.edgeValue a*d.edgeValue b
    rw [mul_assoc]
    exact congrArg (g*·) (eq_inv_iff_mul_eq_one.mpr hv).symm
  · change g*d.edgeValue a*(d.edgeValue a)⁻¹ = g
    group

theorem rawMove_wordValue {a c : d.RawPaths} {p q : a ⟶ c} (h : d.RawMove p q) :
    d.wordValue (d.rawWord p) = d.wordValue (d.rawWord q) := by
  cases h with
  | backtrack h =>
    cases h with
    | step a c f =>
      change d.wordValue [] = d.wordValue [d.orientedLabel f,d.orientedLabel (Quiver.reverse f)]
      simp only [wordValue_nil,wordValue_cons,orientedLabel_reverse,edgeValue_flip,mul_one,mul_inv_cancel]
  | triangle b i u v =>
    change d.edgeValue (d.orientedL b i u v) * d.edgeValue (d.orientedX i u v) * 1 =
      d.edgeValue (d.orientedR b i u v) * 1
    simp only [edgeValue,orientedL,orientedX,orientedR,↓reduceIte,mul_one]
    exact (eq_inv_mul_iff_mul_eq).mp (d.triangle_relation b i u v)

theorem rawHomotopic_wordValue {a c : d.RawPaths} {p q : a ⟶ c}
    (h : d.RawHomotopic p q) : d.wordValue (d.rawWord p) = d.wordValue (d.rawWord q) := by
  induction h with
  | rel p q h =>
    cases h with
    | intro a c u p q v h =>
      simp only [rawWord_comp,wordValue_append,d.rawMove_wordValue h]
  | refl p => rfl
  | symm p q _ ih => exact ih.symm
  | trans p q s _ _ ih ih' => exact ih.trans ih'

theorem rawMove_lifted_filled {a c : d.RawPaths} {p q : a ⟶ c}
    (h : d.RawMove p q) (g : d.GroupType) :
    FilledBetween d.liftedFlip d.liftedTarget d.LiftedFace
      (d.liftWord g (d.rawWord p)) (d.liftWord g (d.rawWord q)) := by
  cases h with
  | backtrack h =>
    cases h with
    | step a c f =>
      change Fillable d.liftedFlip d.liftedTarget d.LiftedFace
        (reverseWord d.liftedFlip (d.liftWord g
          [d.orientedLabel f,d.orientedLabel (Quiver.reverse f)]))
      simp only [liftWord_cons,liftWord_nil,orientedLabel_reverse,edgeValue_flip,
        reverseWord_cons,reverseWord_nil,List.nil_append,List.singleton_append]
      have he : (d.flipEdge (d.orientedLabel f),g*d.edgeValue (d.orientedLabel f)*
          (d.edgeValue (d.orientedLabel f))⁻¹) =
          d.liftedFlip (d.orientedLabel f,g*d.edgeValue (d.orientedLabel f)) := rfl
      rw [he,d.liftedFlip_flip]
      exact Fillable.backtrack d.liftedFlip_flip _
  | triangle b i u v =>
    have hh := TriangleFace.lift d (TriangleFace.pos₀ (d := d) b i u v) g
    change Fillable d.liftedFlip d.liftedTarget d.LiftedFace
      (d.liftWord g [d.orientedL b i u v,d.orientedX i u v] ++
        reverseWord d.liftedFlip (d.liftWord g [d.orientedR b i u v]))
    simp only [liftWord_cons,liftWord_nil,reverseWord_cons,reverseWord_nil,List.nil_append,
      List.cons_append]
    have hr : d.liftedFlip (d.orientedR b i u v,g*d.edgeValue (d.orientedR b i u v)) =
        (d.flipEdge (d.orientedR b i u v),g) := by
      simp only [liftedFlip,mul_inv_cancel_right]
    rw [hr]
    exact ⟨TriangleFilling.triangle d.liftedFlip_flip
      (fun _ _ _ => LiftedFace.rotate d) _ _ _
      hh.2.1.symm hh.2.2.1.symm hh.2.2.2.symm (LiftedFace.mirror d hh)⟩

theorem rawHomotopic_lifted_filled {a c : d.RawPaths} {p q : a ⟶ c}
    (h : d.RawHomotopic p q) (g : d.GroupType) :
    FilledBetween d.liftedFlip d.liftedTarget d.LiftedFace
      (d.liftWord g (d.rawWord p)) (d.liftWord g (d.rawWord q)) := by
  induction h generalizing g with
  | rel p q h =>
    cases h with
    | intro a c u p q v h =>
      have he := d.rawMove_wordValue h
      have hu := d.liftWord_typed (d.rawWord_typed u) g
      have hp := d.liftWord_typed (d.rawWord_typed p) (g*d.wordValue (d.rawWord u))
      have hq := d.liftWord_typed (d.rawWord_typed q) (g*d.wordValue (d.rawWord u))
      rw [← he] at hq
      have hv := d.liftWord_typed (d.rawWord_typed v)
        (g*d.wordValue (d.rawWord u)*d.wordValue (d.rawWord p))
      have hf := FilledBetween.whiskerLeft d.liftedFlip_flip hu (hp.append hv) (hq.append hv)
        (FilledBetween.whiskerRight d.liftedFlip_flip hp hq hv
          (d.rawMove_lifted_filled h (g*d.wordValue (d.rawWord u))))
      simpa only [rawWord_comp,liftWord_append,wordValue_append,← he,mul_assoc,List.append_assoc]
        using hf
  | refl p => exact FilledBetween.refl d.liftedFlip_flip (d.liftWord_typed (d.rawWord_typed p) g)
  | symm p q _ ih =>
    exact FilledBetween.symm d.liftedFlip_flip (fun _ _ _ => LiftedFace.mirror d) (ih g)
  | trans p q s hpq hqs ih ih' =>
    have hq := d.liftWord_typed (d.rawWord_typed q) g
    have hs := d.liftWord_typed (d.rawWord_typed s) g
    rw [← d.rawHomotopic_wordValue hpq] at hq
    rw [← d.rawHomotopic_wordValue hqs,← d.rawHomotopic_wordValue hpq] at hs
    exact FilledBetween.trans d.liftedFlip_flip d.liftedTarget_ne
      (d.liftWord_typed (d.rawWord_typed p) g) hq hs (ih g) (ih' g)

theorem nullhomotopic_lifted_fillable {a : d.RawPaths} {p : a ⟶ a}
    (h : d.RawHomotopic p (𝟙 a)) (g : d.GroupType) :
    Fillable d.liftedFlip d.liftedTarget d.LiftedFace (d.liftWord g (d.rawWord p)) := by
  simpa only [FilledBetween,rawWord_nil,liftWord_nil,reverseWord_nil,List.append_nil] using
    d.rawHomotopic_lifted_filled h g

end Release075.BlockPresentation

namespace Release075.TriangleFilling
open Equiv PermCycles
variable {I B : Type} {r : ℕ} {d : BlockPresentation I B r}
variable {w : List d.LiftedEdge}

/-- Forgetting group coordinates keeps every dart, incidence, boundary and
planar component. The metric labels can therefore be tracked through reduction. -/
def forgetLift (D : TriangleFilling d.liftedFlip d.liftedTarget d.LiftedFace w) :
    TriangleFilling d.flipEdge d.edgeTarget d.TriangleFace (w.map Prod.fst) where
  Dart := D.Dart
  reverse := D.reverse
  next := D.next
  reverse_involutive := D.reverse_involutive
  reverse_ne := D.reverse_ne
  label a := (D.label a).1
  reverse_label a := congrArg Prod.fst (D.reverse_label a)
  color_next a := congrArg Prod.fst (D.color_next a)
  planar := D.planar
  boundary := D.boundary
  boundary_cycle := D.boundary_cycle
  boundary_word := by
    simpa only [List.map_map,Function.comp_def] using congrArg (List.map Prod.fst) D.boundary_word
  triangular a ha hb := let ht := D.triangular a ha hb; ⟨ht.1,ht.2.1,ht.2.2.1⟩

@[simp] theorem forgetLift_activeCount
    (D : TriangleFilling d.liftedFlip d.liftedTarget d.LiftedFace w) :
    D.forgetLift.activeCount = D.activeCount := rfl

/-- Matching opposite face labels at a shared lifted edge forces matching group
coordinates on the other two edges. Thus reduction cannot hide a downstairs dipole. -/
def Dipole.lift {D : TriangleFilling d.liftedFlip d.liftedTarget d.LiftedFace w}
    (P : D.forgetLift.Dipole) : D.Dipole := by
  have hn (j) : D.next (P.dart j) = P.dart (dipoleFace j) := P.next_dart j
  have hc (j) : d.liftedTarget (d.liftedFlip (D.label (P.dart (dipoleFace j)))) =
      d.liftedTarget (D.label (P.dart j)) := by
    have hh := D.color_next (P.dart j)
    change d.liftedTarget (D.label (D.reverse (D.next (P.dart j)))) =
      d.liftedTarget (D.label (P.dart j)) at hh
    exact (congrArg d.liftedTarget (D.reverse_label (P.dart (dipoleFace j)))).symm.trans
      (by simpa only [hn] using hh)
  have hrev : D.label (P.dart 3) = d.liftedFlip (D.label (P.dart 0)) := by
    rw [← P.reverse_zero]
    exact D.reverse_label _
  have h0 := hc 0
  have h5 := hc 5
  simp only [dipoleFace_zero] at h0
  simp only [dipoleFace_five,hrev,d.liftedFlip_flip] at h5
  have h51 : D.label (P.dart 5) = d.liftedFlip (D.label (P.dart 1)) :=
    Prod.ext P.label51 (congrArg (fun x : d.LiftedVertex => x.2) (h5.symm.trans h0.symm))
  have h1 := hc 1
  have h4 := hc 4
  simp only [dipoleFace_one] at h1
  simp only [dipoleFace_four,h51,d.liftedFlip_flip] at h4
  have h42 : D.label (P.dart 4) = d.liftedFlip (D.label (P.dart 2)) :=
    Prod.ext P.label42 (congrArg (fun x : d.LiftedVertex => x.2) (h4.symm.trans h1.symm))
  exact {
    dart := P.dart
    next_dart := P.next_dart
    reverse_zero := P.reverse_zero
    not_boundary := P.not_boundary
    active := P.active
    color10 := fun h => P.color10 (congrArg Prod.fst h)
    color21 := fun h => P.color21 (congrArg Prod.fst h)
    label51 := h51
    label42 := h42 }

theorem noDipole_forgetLift {D : TriangleFilling d.liftedFlip d.liftedTarget d.LiftedFace w}
    (h : IsEmpty D.Dipole) : IsEmpty D.forgetLift.Dipole := ⟨fun P => h.false P.lift⟩

end Release075.TriangleFilling

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)
variable {w : List (d.presentation hr).LiftedEdge}

theorem exists_lifted_linear_filling (hf : Fillable (d.presentation hr).liftedFlip
    (d.presentation hr).liftedTarget (d.presentation hr).LiftedFace w) :
    ∃ D : TriangleFilling (d.presentation hr).liftedFlip (d.presentation hr).liftedTarget
      (d.presentation hr).LiftedFace w, D.activeCount ≤ 19*w.length := by
  classical
  by_cases hw : w = []
  · subst w
    refine ⟨TriangleFilling.empty,?_⟩
    unfold TriangleFilling.activeCount
    apply (Finset.card_le_univ _).trans
    change 0 ≤ _
    exact Nat.zero_le _
  · obtain ⟨D,hD⟩ := TriangleFilling.exists_noDipole hf
    have hn : D.boundary ≠ [] := by
      intro he
      apply hw
      rw [← D.boundary_word,he,List.map_nil]
    obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil D.boundary hn
    have hbound := d.reduced_linear_active_bound hr D.forgetLift b hb
      (TriangleFilling.noDipole_forgetLift hD)
    rw [TriangleFilling.forgetLift_activeCount,List.length_map] at hbound
    exact ⟨D,by omega⟩

end Release075.MarkedLineData

end OAI
