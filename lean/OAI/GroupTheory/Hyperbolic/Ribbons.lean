import OAI.GroupTheory.Hyperbolic.Dipoles

namespace OAI

namespace Release075
open scoped BigOperators

/-- The numerical incidence identities of a nonempty planar triangle disk, with
boundary visits counted with multiplicity (including both sides of naked edges).
All fields are finite counts or angle data. No group conclusion is assumed. -/
structure AngleDiskCounts where
  Vertex : Type
  [vertexFintype : Fintype Vertex]
  edges : ℕ
  faces : ℕ
  visits : Vertex → ℕ
  angles : Vertex → ℝ
  angles_nonneg : ∀ v, 0 ≤ angles v
  euler : Fintype.card Vertex + faces = edges + 1
  exterior : (∑ v, visits v) + 3*faces = 2*edges
  angle_sum : (∑ v, angles v) = 5*faces

attribute [instance] AngleDiskCounts.vertexFintype
namespace AngleDiskCounts
variable (D : AngleDiskCounts)

def curvature (v : D.Vertex) : ℝ := 10 - 5*(D.visits v) - D.angles v

/-- Gauss--Bonnet includes repeated boundary visits and naked edges. -/
theorem gauss_bonnet : ∑ v, D.curvature v = 10 := by
  have he : (Fintype.card D.Vertex : ℝ) + D.faces = D.edges + 1 := by exact_mod_cast D.euler
  have hb : (∑ v, (D.visits v : ℝ)) + 3*D.faces = 2*D.edges := by exact_mod_cast D.exterior
  simp only [curvature,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,← Finset.mul_sum]
  linarith [D.angle_sum]

/-- Curvature obstruction for a boundary all of whose cyclic turns have link
length >=π: an interior reduced link contributes >=2π and a single exterior
visit contributes >=π. Multiple visits require no turn estimate. -/
theorem cannot_have_geodesic_boundary
    (hinterior : ∀ v, D.visits v = 0 → 10 ≤ D.angles v)
    (hboundary : ∀ v, D.visits v = 1 → 5 ≤ D.angles v) : False := by
  have hnonpos (v : D.Vertex) : D.curvature v ≤ 0 := by
    by_cases h0 : D.visits v = 0
    · have h := hinterior v h0
      simp only [curvature,h0,Nat.cast_zero,mul_zero,sub_zero]
      linarith
    by_cases h1 : D.visits v = 1
    · have h := hboundary v h1
      simp only [curvature,h1,Nat.cast_one,mul_one]
      linarith
    · have h2 : (2 : ℝ) ≤ D.visits v := by exact_mod_cast (show 2 ≤ D.visits v by omega)
      have ha := D.angles_nonneg v
      dsimp [curvature]
      linarith
  have hs : (∑ v, D.curvature v) ≤ 0 := Finset.sum_nonpos (fun v _ => hnonpos v)
  rw [D.gauss_bonnet] at hs
  norm_num at hs

noncomputable def interior : Finset D.Vertex := by
  classical
  exact Finset.univ.filter (fun v => D.visits v = 0)

noncomputable def boundary : Finset D.Vertex := by
  classical
  exact Finset.univ.filter (fun v => D.visits v ≠ 0)

def boundaryLength : ℕ := ∑ v, D.visits v

theorem vertices_partition : D.interior.card + D.boundary.card = Fintype.card D.Vertex := by
  classical
  simpa only [interior,boundary,Finset.card_univ] using
    Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun v => D.visits v = 0)

theorem boundary_card_le_length : D.boundary.card ≤ D.boundaryLength := by
  classical
  calc
    D.boundary.card = ∑ v ∈ D.boundary, 1 := by simp
    _ ≤ ∑ v ∈ D.boundary, D.visits v := by
      apply Finset.sum_le_sum
      intro v hv
      have h : D.visits v ≠ 0 := (Finset.mem_filter.mp hv).2
      omega
    _ ≤ D.boundaryLength := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- The Euler/incidence formula in terms of interior and boundary vertices. -/
theorem face_vertex_formula :
    D.faces + D.boundaryLength + 2 = 2*D.interior.card + 2*D.boundary.card := by
  have he := D.euler
  have hb := D.exterior
  have hp := D.vertices_partition
  change D.boundaryLength + 3*D.faces = 2*D.edges at hb
  omega

theorem linear_face_bound
    (hinterior : ∀ v, D.visits v = 0 → 12 ≤ D.angles v) :
    D.faces + 12 ≤ 6*D.boundaryLength := by
  classical
  have ha : (12 : ℝ)*D.interior.card ≤ 5*D.faces := by
    calc
      (12 : ℝ)*D.interior.card = ∑ _v ∈ D.interior, (12 : ℝ) := by simp [mul_comm]
      _ ≤ ∑ v ∈ D.interior, D.angles v := by
        apply Finset.sum_le_sum
        intro v hv
        exact hinterior v (Finset.mem_filter.mp hv).2
      _ ≤ ∑ v, D.angles v := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun v _ _ => D.angles_nonneg v)
      _ = 5*D.faces := D.angle_sum
  have ha' : 12*D.interior.card ≤ 5*D.faces := by exact_mod_cast ha
  have hp := D.face_vertex_formula
  have hb := D.boundary_card_le_length
  omega

/-- For a simple geodesic polygon only its designated corners can contribute
positive boundary curvature. Original interior vertices cost two angle units.
This is the exact quantitative count used for uniform inradius. -/
theorem polygon_original_vertex_bound (original corners : Finset D.Vertex)
    (hvisits : ∀ v, D.visits v ≤ 1)
    (hcorner : ∀ v ∈ corners, D.visits v = 1)
    (horiginal : ∀ v ∈ original, D.visits v = 0)
    (hstrict : ∀ v ∈ original, 12 ≤ D.angles v)
    (hinterior : ∀ v, D.visits v = 0 → 10 ≤ D.angles v)
    (hboundary : ∀ v, D.visits v = 1 → v ∉ corners → 5 ≤ D.angles v) :
    2*(original.card : ℝ) + 10 ≤ 5*corners.card := by
  classical
  have hpoint (v : D.Vertex) : D.curvature v ≤
      (if v ∈ corners then (5 : ℝ) else 0) - (if v ∈ original then 2 else 0) := by
    by_cases ho : v ∈ original
    · have hv := horiginal v ho
      have ha := hstrict v ho
      have hc : v ∉ corners := by intro hc; have := hcorner v hc; omega
      simp only [curvature,hv,Nat.cast_zero,mul_zero,sub_zero,ite_eq_right hc,ite_eq_left ho]
      linarith
    · by_cases hc : v ∈ corners
      · have hv := hcorner v hc
        have ha := D.angles_nonneg v
        simp only [curvature,hv,Nat.cast_one,mul_one,ite_eq_left hc,ite_eq_right ho,sub_zero]
        linarith
      · simp only [ite_eq_right hc,ite_eq_right ho,sub_zero]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hvisits v) with hv | hv
        · have ha := hinterior v hv
          simp only [curvature,hv,Nat.cast_zero,mul_zero,sub_zero]
          linarith
        · have ha := hboundary v hv hc
          simp only [curvature,hv,Nat.cast_one,mul_one]
          linarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hpoint v)
  rw [D.gauss_bonnet,Finset.sum_sub_distrib] at hs
  have hc : (∑ v : D.Vertex, if v ∈ corners then (5 : ℝ) else 0) = 5*corners.card := by
    rw [← Finset.sum_filter]
    have he : Finset.univ.filter (· ∈ corners) = corners := by ext; simp
    simp [he,mul_comm]
  have ho : (∑ v : D.Vertex, if v ∈ original then (2 : ℝ) else 0) = 2*original.card := by
    rw [← Finset.sum_filter]
    have he : Finset.univ.filter (· ∈ original) = original := by ext; simp
    simp [he,mul_comm]
  rw [hc,ho] at hs
  linarith

end AngleDiskCounts
end Release075

namespace Release075
open scoped BigOperators
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq

/-- An oriented combinatorial triangle filling. Darts are incoming at the
corner they carry; `reverse * face` rotates those corners about a vertex.
This records finite incidence data, NOT existence of a filling for a nullword.
Its single distinguished face is the prescribed exterior walk, including spurs. -/
structure TriangleRibbon where
  Dart : Type
  [dartFintype : Fintype Dart]
  reverse : Perm Dart
  face : Perm Dart
  reverse_involution : Function.Involutive reverse
  reverse_ne : ∀ d, reverse d ≠ d
  outer : Cycles face
  color : Cycles (reverse * face) → Fin 3
  face_colors : ∀ c : Cycles face, c ≠ outer →
    Function.Bijective (fun d : {d : Dart // cl face d = c} => color (cl (reverse * face) d))
  euler : Fintype.card (Cycles (reverse * face)) +
      Fintype.card {c : Cycles face // c ≠ outer} = Fintype.card (Cycles reverse) + 1
attribute [instance] TriangleRibbon.dartFintype

namespace TriangleRibbon
variable (R : TriangleRibbon)
abbrev vertexPerm := R.reverse * R.face
abbrev Vertex := Cycles R.vertexPerm
abbrev Edge := Cycles R.reverse
abbrev Face := {c : Cycles R.face // c ≠ R.outer}

noncomputable def weight (c : Fin 3) : ℝ := if c = 0 then 3 else 1

noncomputable def cornerAngle (d : R.Dart) : ℝ :=
  if cl R.face d = R.outer then 0 else weight (R.color (cl R.vertexPerm d))

noncomputable def visits (v : R.Vertex) : ℕ :=
  ∑ d : R.Dart, if cl R.vertexPerm d = v ∧ cl R.face d = R.outer then 1 else 0

noncomputable def angles (v : R.Vertex) : ℝ :=
  ∑ d : R.Dart, if cl R.vertexPerm d = v then R.cornerAngle d else 0

@[simp] theorem cornerAngle_nonneg (d : R.Dart) : 0 ≤ R.cornerAngle d := by
  dsimp [cornerAngle,weight]
  split_ifs <;> norm_num

theorem angles_nonneg (v : R.Vertex) : 0 ≤ R.angles v := by
  apply Finset.sum_nonneg
  intro d _
  split_ifs
  · exact R.cornerAngle_nonneg d
  · rfl

theorem card_face_fiber (c : Cycles R.face) (hc : c ≠ R.outer) :
    Fintype.card {d : R.Dart // cl R.face d = c} = 3 := by
  have h := Fintype.card_congr (Equiv.ofBijective _ (R.face_colors c hc))
  simpa only [Fintype.card_fin] using h

theorem face_angle_sum (c : Cycles R.face) (hc : c ≠ R.outer) :
    (∑ d : {d : R.Dart // cl R.face d = c}, R.cornerAngle d) = 5 := by
  have hh : (∑ d : {d : R.Dart // cl R.face d = c},
      weight (R.color (cl R.vertexPerm d))) = ∑ i : Fin 3, weight i :=
    (Equiv.ofBijective _ (R.face_colors c hc)).sum_comp weight
  have he (d : {d : R.Dart // cl R.face d = c}) : R.cornerAngle d =
      weight (R.color (cl R.vertexPerm d)) := by
    simp only [cornerAngle,d.property,ite_eq_right hc]
  simp only [he]
  rw [hh]
  norm_num [Fin.sum_univ_succ,weight]

theorem dart_card : Fintype.card R.Dart = 2 * Fintype.card R.Edge :=
  card_eq_mul_cycles R.reverse 2 (orbit_card_involution R.reverse R.reverse_involution R.reverse_ne)

theorem visits_sum : (∑ v : R.Vertex, R.visits v) =
    Fintype.card {d : R.Dart // cl R.face d = R.outer} := by
  simp only [visits]
  rw [Finset.sum_comm]
  have hs (d : R.Dart) :
      (∑ v : R.Vertex, if cl R.vertexPerm d = v ∧ cl R.face d = R.outer then 1 else 0) =
      if cl R.face d = R.outer then 1 else 0 := by
    by_cases h : cl R.face d = R.outer <;> simp [h]
  simp only [hs]
  rw [← Finset.card_filter]
  exact (Fintype.card_subtype _).symm

theorem exterior_count : (∑ v : R.Vertex, R.visits v) + 3 * Fintype.card R.Face =
    2 * Fintype.card R.Edge := by
  rw [R.visits_sum,← R.dart_card,← sum_card_fibers R.face,
    Fintype.sum_eq_add_sum_subtype_ne _ R.outer]
  congr 1
  have h3 (c : R.Face) : Fintype.card {d : R.Dart // cl R.face d = c.val} = 3 :=
    R.card_face_fiber c.val c.property
  simp only [h3,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_comm]

theorem all_angles_sum : (∑ v : R.Vertex, R.angles v) = 5 * Fintype.card R.Face := by
  simp only [angles]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  have hh : (∑ c : Cycles R.face, ∑ d : {d : R.Dart // cl R.face d = c},
      R.cornerAngle d) = ∑ d : R.Dart, R.cornerAngle d := by
    simpa only [Fintype.sum_sigma, Equiv.sigmaFiberEquiv_apply] using
      (Equiv.sigmaFiberEquiv (cl R.face)).sum_comp R.cornerAngle
  rw [← hh,Fintype.sum_eq_add_sum_subtype_ne _ R.outer]
  have h0 : (∑ d : {d : R.Dart // cl R.face d = R.outer}, R.cornerAngle d) = 0 := by
    apply Finset.sum_eq_zero
    intro d _
    simp [cornerAngle,d.property]
  rw [h0,zero_add]
  have h5 (c : R.Face) : (∑ d : {d : R.Dart // cl R.face d = c.val}, R.cornerAngle d) = 5 :=
    R.face_angle_sum c.val c.property
  simp only [h5,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm]

/-- All arithmetic hypotheses of the earlier curvature identity are now derived
from actual edge/face/vertex permutations and face-color bijections. -/
noncomputable def counts : AngleDiskCounts where
  Vertex := R.Vertex
  edges := Fintype.card R.Edge
  faces := Fintype.card R.Face
  visits := R.visits
  angles := R.angles
  angles_nonneg := R.angles_nonneg
  euler := R.euler
  exterior := R.exterior_count
  angle_sum := R.all_angles_sum

end TriangleRibbon
end Release075

namespace Release075.SumWalk
variable {U V : Type*} {G : SimpleGraph U} {H : SimpleGraph V}

/-- Forget the disjoint summand tag from a walk in the left component. -/
def left {a b : U} : (G.sum H).Walk (.inl a) (.inl b) → G.Walk a b
  | .nil => .nil
  | .cons (v := .inl _) h p => (left p).cons (SimpleGraph.sum_adj_inl.mp h)
  | .cons (v := .inr _) h _ => by simp at h

@[simp] theorem left_length {a b : U} (p : (G.sum H).Walk (.inl a) (.inl b)) :
    (left p).length = p.length := by
  fun_induction left p <;> simp_all only [SimpleGraph.Walk.length_cons,SimpleGraph.Walk.length_nil]

@[simp] theorem map_left {a b : U} (p : (G.sum H).Walk (.inl a) (.inl b)) :
    (left p).map SimpleGraph.Embedding.sumInl.toHom = p := by
  fun_induction left p <;> simp_all only [SimpleGraph.Walk.map_cons,SimpleGraph.Walk.map_nil] <;> rfl

 theorem left_reduced {a b : U} {p : (G.sum H).Walk (.inl a) (.inl b)}
    (hp : ReducedWalk p) : ReducedWalk (left p) := by
  intro i hi heq
  apply hp i (by simpa only [left_length] using hi)
  have hh := congrArg (fun x : U => (Sum.inl x : U ⊕ V)) heq
  have hm (j : ℕ) : Sum.inl ((left p).getVert j) = p.getVert j := by
    have h := SimpleGraph.Walk.getVert_map (SimpleGraph.Embedding.sumInl (G := G) (H := H)).toHom (left p) j
    rw [map_left p] at h
    exact h.symm
  simpa only [hm] using hh

/-- The right-component extraction is left extraction after the graph sum swap. -/
def right {a b : V} (p : (G.sum H).Walk (.inr a) (.inr b)) : H.Walk a b :=
  left (p.map SimpleGraph.Iso.sumComm.toHom)

@[simp] theorem right_length {a b : V} (p : (G.sum H).Walk (.inr a) (.inr b)) :
    (right p).length = p.length :=
  (left_length _).trans (SimpleGraph.Walk.length_map _ _)

 theorem right_reduced {a b : V} {p : (G.sum H).Walk (.inr a) (.inr b)}
    (hp : ReducedWalk p) : ReducedWalk (right p) := by
  apply left_reduced
  exact hp.map _ (fun _ _ _ _ _ h => SimpleGraph.Iso.sumComm.injective h)

end Release075.SumWalk

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

theorem IsBoundary.sameCycle {f : Perm A} {l : List A} (h : IsBoundary f l)
    {a b : A} (ha : a ∈ l) (hb : b ∈ l) : f.SameCycle a b := by
  by_cases hab : a = b
  · subst b; exact .refl _ _
  have hlen : 2 ≤ l.length := by
    cases l with
    | nil => simp at ha
    | cons x xs =>
      cases xs with
      | nil => simp_all
      | cons y ys => simp
  have hform : l.formPerm.SameCycle a b :=
    (List.isCycle_formPerm h.1 hlen).sameCycle
      ((List.formPerm_apply_mem_ne_self_iff l h.1 a ha).mpr hlen)
      ((List.formPerm_apply_mem_ne_self_iff l h.1 b hb).mpr hlen)
  apply sameCycle_le_of_step l.formPerm (Perm.SameCycle.setoid f) _ hform
  intro x
  by_cases hx : x ∈ l
  · rw [← h.2 x hx]
    exact (Perm.SameCycle.refl f x).apply_right
  · rw [List.formPerm_apply_of_notMem hx]

theorem IsBoundary.mem_iff_sameCycle {f : Perm A} {l : List A} (h : IsBoundary f l)
    {b : A} (hb : b ∈ l) (a : A) : a ∈ l ↔ f.SameCycle a b := by
  refine ⟨fun ha => h.sameCycle ha hb,fun hh => ?_⟩
  exact (invariant_pred_sameCycle f (· ∈ l) h.mem_iff hh).mpr hb

end Release075

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

theorem three_color_bijective (f : Perm A) (a : A) (q : A → Fin 3)
    (hp : (f^3) a = a) (hne : f a ≠ a)
    (hab : q a ≠ q (f a)) (hbc : q (f a) ≠ q ((f^2) a))
    (hca : q ((f^2) a) ≠ q a) :
    Function.Bijective (fun x : {x : A // cl f x = cl f a} => q x) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro x y hxy
    have hx : x.val ∈ orbit f a := (mem_orbit f a x).mpr ((cl_eq_iff f _ _).mp x.property).symm
    have hy : y.val ∈ orbit f a := (mem_orbit f a y).mpr ((cl_eq_iff f _ _).mp y.property).symm
    rw [orbit_eq_image f a (by omega : 0 < 3) hp] at hx hy
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hx
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hy
    apply Subtype.ext
    rw [← hi,← hj]
    change q x.val = q y.val at hxy
    rw [← hi,← hj] at hxy
    fin_cases i <;> fin_cases j <;>
      norm_num only [pow_zero,pow_one,Perm.one_apply] at hxy ⊢
    all_goals first | exact (hab hxy).elim | exact (hab hxy.symm).elim |
      exact (hbc hxy).elim | exact (hbc hxy.symm).elim |
      exact (hca hxy).elim | exact (hca hxy.symm).elim
  · rw [card_fiber,orbit_card_three f a hp hne,Fintype.card_fin]

end Release075.PermCycles

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}
variable {w : List E} (D : TriangleFilling flip color face w)

abbrev ActiveDart := {a : D.Dart // D.Active a}
noncomputable def activeReverse : Perm D.ActiveDart := D.reverse.subtypePerm D.active_reverse
noncomputable def activeNext : Perm D.ActiveDart := D.next.subtypePerm D.active_next

@[simp] theorem activeReverse_val (a : D.ActiveDart) : (D.activeReverse a).val = D.reverse a := rfl
@[simp] theorem activeNext_val (a : D.ActiveDart) : (D.activeNext a).val = D.next a := rfl

 theorem activeReverse_involutive : Function.Involutive D.activeReverse := by
  intro a
  apply Subtype.ext
  exact D.reverse_involutive a

 theorem activeReverse_ne (a : D.ActiveDart) : D.activeReverse a ≠ a := by
  intro h
  exact D.reverse_ne a (congrArg Subtype.val h)

 theorem active_planar : PlanarMap D.activeReverse D.activeNext :=
  D.planar.restrict D.Active D.active_reverse D.active_next

 theorem active_components (a b : D.ActiveDart) :
    components D.activeReverse D.activeNext a b := by
  rw [activeReverse,activeNext,components_subtype]
  obtain ⟨x,hx,hax⟩ := a.property
  obtain ⟨y,hy,hby⟩ := b.property
  have hxy : components D.reverse D.next x y :=
    (show Perm.SameCycle.setoid D.next ≤ components D.reverse D.next from le_sup_right)
      (D.boundary_cycle.sameCycle hx hy)
  exact (components D.reverse D.next).trans hax
    ((components D.reverse D.next).trans hxy ((components D.reverse D.next).symm hby))

 theorem active_componentCount {b : D.Dart} (hb : b ∈ D.boundary) :
    componentCount D.activeReverse D.activeNext = 1 := by
  apply Nat.card_eq_one_iff_unique.mpr
  constructor
  · refine ⟨?_⟩
    intro x y
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y =>
        exact Quotient.sound (D.active_components x y)
  · exact ⟨Quotient.mk _ ⟨b,D.active_of_mem hb⟩⟩

 theorem active_color_step (q : V → Fin 3) (a : D.ActiveDart) :
    q (color (D.label ((D.activeReverse*D.activeNext) a))) = q (color (D.label a)) :=
  congrArg q (D.color_next a)

noncomputable def activeColor (q : V → Fin 3) : Cycles (D.activeReverse*D.activeNext) → Fin 3 :=
  descend _ (fun a => q (color (D.label a))) (D.active_color_step q)

 theorem active_boundary_iff {b : D.Dart} (hb : b ∈ D.boundary) (a : D.ActiveDart) :
    cl D.activeNext a = cl D.activeNext ⟨b,D.active_of_mem hb⟩ ↔ a.val ∈ D.boundary := by
  rw [cl_eq_iff,activeNext,Perm.sameCycle_subtypePerm]
  exact (D.boundary_cycle.mem_iff_sameCycle hb a.val).symm

/-- A nonempty labeled filling has its connected boundary component as an actual
Euler-characteristic-one triangle ribbon. No geometric embedding is postulated. -/
noncomputable def ribbon (q : V ≃ Fin 3)
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a)
    (b : D.Dart) (hb : b ∈ D.boundary) : TriangleRibbon where
  Dart := D.ActiveDart
  reverse := D.activeReverse
  face := D.activeNext
  reverse_involution := D.activeReverse_involutive
  reverse_ne := D.activeReverse_ne
  outer := cl D.activeNext ⟨b,D.active_of_mem hb⟩
  color := D.activeColor q
  face_colors := by
    intro c hc
    obtain ⟨a,rfl⟩ := cl_surjective D.activeNext c
    have ha : a.val ∉ D.boundary := fun h => hc ((D.active_boundary_iff hb a).mpr h)
    obtain ⟨hp,hn,hface⟩ := D.triangular a a.property ha
    obtain ⟨h01,h12,h20⟩ := hf _ _ _ hface
    have hp' : (D.activeNext^3) a = a := by
      apply Subtype.ext
      exact hp
    have hn' : D.activeNext a ≠ a := fun h => hn (congrArg Subtype.val h)
    exact three_color_bijective D.activeNext a (fun x => q (color (D.label x))) hp' hn'
      (fun h => h01 (q.injective h)) (fun h => h12 (q.injective h))
      (fun h => h20 (q.injective h))
  euler := by
    have hp := D.active_planar
    have hr := card_eq_mul_cycles D.activeReverse 2
      (orbit_card_involution D.activeReverse D.activeReverse_involutive D.activeReverse_ne)
    have hc := D.active_componentCount hb
    have hf' := card_subtype_ne_add_one (cl D.activeNext ⟨b,D.active_of_mem hb⟩)
    simp only [PlanarMap,cycleCount,Nat.card_eq_fintype_card] at hp hc hf'
    omega

end Release075.TriangleFilling

namespace Release075.SequenceWalk
variable {E : Type*} (L : SimpleGraph E)

def walk (a : ℕ → E) : (n : ℕ) → (∀ i, i < n → L.Adj (a i) (a (i+1))) → L.Walk (a 0) (a n)
  | 0, _ => .nil
  | n+1, h => (walk (fun i => a (i+1)) n (fun i hi => h (i+1) (by omega))).cons (h 0 (by omega))

@[simp] theorem length_walk (a : ℕ → E) (n : ℕ) (h) : (walk L a n h).length = n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp only [walk,SimpleGraph.Walk.length_cons,ih]

theorem getVert_walk (a : ℕ → E) (n : ℕ) (h) (i : ℕ) (hi : i ≤ n) :
    (walk L a n h).getVert i = a i := by
  induction n generalizing a i with
  | zero => have : i = 0 := by omega
            subst i
            rfl
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih (fun j => a (j+1)) _ i (by omega)

theorem reduced_walk (a : ℕ → E) (n : ℕ) (h)
    (hr : ∀ i, i+2 ≤ n → a i ≠ a (i+2)) : ReducedWalk (walk L a n h) := by
  intro i hi
  simp only [length_walk] at hi
  rw [getVert_walk L a n h i (by omega),getVert_walk L a n h (i+2) hi]
  exact hr i hi

end Release075.SequenceWalk

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

theorem class_filter (f : Perm A) (a : A) :
    Finset.univ.filter (fun d => cl f d = cl f a) = orbit f a := by
  ext d
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,cl_eq_iff,mem_orbit,Perm.sameCycle_comm]

theorem pow_card_orbit (f : Perm A) (a : A) : (f^(orbit f a).card) a = a := by
  rw [orbit_card_eq_minimalPeriod]
  exact Function.iterate_minimalPeriod

theorem pow_ne_of_lt_card_orbit (f : Perm A) (a : A) (n : ℕ)
    (hn : 0 < n) (hlt : n < (orbit f a).card) : (f^n) a ≠ a := by
  intro h
  rw [orbit_card_eq_minimalPeriod] at hlt
  have hz : 0 < Function.minimalPeriod (f : A → A) a := minimalPeriod_pos f a
  have hh : n = 0 := Function.iterate_injOn_Iio_minimalPeriod (f := (f : A → A))
    (x := a) hlt hz h
  omega

end Release075.PermCycles

namespace Release075.TriangleRibbon
open Equiv PermCycles
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable (R : TriangleRibbon)

def IsOuter (a : R.Dart) : Prop := cl R.face a = R.outer

noncomputable def outerCorners (a : R.Dart) : Finset R.Dart :=
  (orbit R.vertexPerm a).filter R.IsOuter
noncomputable def innerCorners (a : R.Dart) : Finset R.Dart :=
  (orbit R.vertexPerm a).filter (fun b => ¬ R.IsOuter b)

theorem visits_cl (a : R.Dart) : R.visits (cl R.vertexPerm a) = (R.outerCorners a).card := by
  unfold visits outerCorners IsOuter
  rw [← class_filter,Finset.filter_filter,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs <;> rfl

theorem angles_cl (a : R.Dart) :
    R.angles (cl R.vertexPerm a) = weight (R.color (cl R.vertexPerm a)) * (R.innerCorners a).card := by
  have hs : R.angles (cl R.vertexPerm a) =
      ∑ d ∈ R.innerCorners a, weight (R.color (cl R.vertexPerm a)) := by
    rw [angles,innerCorners,← class_filter,Finset.filter_filter,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    simp only [cornerAngle,IsOuter]
    by_cases h : cl R.vertexPerm d = cl R.vertexPerm a <;>
      by_cases ho : cl R.face d = R.outer <;> simp [h,ho]
  rw [hs]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_comm]

theorem corner_count (a : R.Dart) :
    (R.innerCorners a).card + (R.outerCorners a).card = (orbit R.vertexPerm a).card := by
  have h := Finset.card_filter_add_card_filter_not (s := orbit R.vertexPerm a) R.IsOuter
  change (R.outerCorners a).card + (R.innerCorners a).card = _ at h
  omega

theorem no_outer_of_visits_zero (a : R.Dart) (h : R.visits (cl R.vertexPerm a) = 0)
    {b : R.Dart} (hb : R.vertexPerm.SameCycle a b) : ¬ R.IsOuter b := by
  intro ho
  rw [R.visits_cl,Finset.card_eq_zero] at h
  have hm : b ∈ R.outerCorners a := Finset.mem_filter.mpr ⟨(mem_orbit _ _ _).mpr hb,ho⟩
  rw [h] at hm
  exact Finset.notMem_empty _ hm

theorem unique_outer_of_visits_one (a : R.Dart) (ha : R.IsOuter a)
    (h : R.visits (cl R.vertexPerm a) = 1) {b : R.Dart}
    (hb : R.vertexPerm.SameCycle a b) (ho : R.IsOuter b) : b = a := by
  rw [R.visits_cl,Finset.card_eq_one] at h
  obtain ⟨c,hc⟩ := h
  have hma : a ∈ R.outerCorners a := Finset.mem_filter.mpr ⟨(mem_orbit _ _ _).mpr (.refl _ _),ha⟩
  have hmb : b ∈ R.outerCorners a := Finset.mem_filter.mpr ⟨(mem_orbit _ _ _).mpr hb,ho⟩
  rw [hc,Finset.mem_singleton] at hma hmb
  exact hmb.trans hma.symm

variable {E : Type*} (L : SimpleGraph E) (label : R.Dart → E)
variable (hadj : ∀ a, ¬ R.IsOuter a → L.Adj (label a) (label (R.vertexPerm a)))
variable (hred : ∀ a, ¬ R.IsOuter a → ¬ R.IsOuter (R.vertexPerm a) →
  label a ≠ label (R.vertexPerm (R.vertexPerm a)))

include hadj hred

/-- The full corner orbit at a vertex disjoint from the exterior is a genuinely
reduced nonempty closed link walk. -/
theorem interior_angle_lower (M : ℝ)
    (hclosed : ∀ a (p : L.Walk (label a) (label a)), 0 < p.length → ReducedWalk p →
      M ≤ weight (R.color (cl R.vertexPerm a)) * p.length)
    (v : R.Vertex) (hv : R.visits v = 0) : M ≤ R.angles v := by
  obtain ⟨a,rfl⟩ := cl_surjective R.vertexPerm v
  let n := (orbit R.vertexPerm a).card
  let seq := fun i : ℕ => label ((R.vertexPerm^i) a)
  have hn : 0 < n := by
    change 0 < (orbit R.vertexPerm a).card
    rw [orbit_card_eq_minimalPeriod]
    exact minimalPeriod_pos _ _
  have hout (i : ℕ) : ¬ R.IsOuter ((R.vertexPerm^i) a) :=
    R.no_outer_of_visits_zero a hv ((Perm.SameCycle.refl _ _).pow_right)
  have hadj' (i : ℕ) (_hi : i < n) : L.Adj (seq i) (seq (i+1)) := by
    simpa only [seq,pow_succ',Perm.mul_apply] using hadj _ (hout i)
  have hred' (i : ℕ) (_hi : i+2 ≤ n) : seq i ≠ seq (i+2) := by
    have hh := hred ((R.vertexPerm^i) a) (hout i)
      (by simpa only [pow_succ',Perm.mul_apply] using hout (i+1))
    simpa only [seq,show i+2 = (i+1)+1 by omega,pow_succ',Perm.mul_apply] using hh
  have hend : seq n = label a := congrArg label (pow_card_orbit R.vertexPerm a)
  have hstart : seq 0 = label a := rfl
  let p := (SequenceWalk.walk L seq n hadj').copy hstart hend
  have hlen : p.length = n := (SimpleGraph.Walk.length_copy _ _ _).trans
    (SequenceWalk.length_walk L seq n hadj')
  have hr : ReducedWalk p := by
    intro i hi
    simpa only [p,SimpleGraph.Walk.getVert_copy] using
      SequenceWalk.reduced_walk L seq n hadj' hred' i
        (by simpa only [p,SimpleGraph.Walk.length_copy] using hi)
  have hh := hclosed a p (by rw [hlen]; exact hn) hr
  have hc : (R.innerCorners a).card = n := by
    have hc := R.corner_count a
    rw [← R.visits_cl,hv] at hc
    omega
  rw [R.angles_cl,hc]
  simpa only [hlen] using hh

/-- A vertex with exactly one exterior corner has a reduced interior-sector
path from the outgoing boundary direction back to the incoming one. -/
theorem boundary_angle_lower
    (hboundary : ∀ a, R.IsOuter a →
      ∀ p : L.Walk (label (R.vertexPerm a)) (label a), ReducedWalk p →
        5 ≤ weight (R.color (cl R.vertexPerm a)) * p.length)
    (v : R.Vertex) (hv : R.visits v = 1) : 5 ≤ R.angles v := by
  obtain ⟨a,ha⟩ : ∃ a, cl R.vertexPerm a = v ∧ R.IsOuter a := by
    obtain ⟨b,rfl⟩ := cl_surjective R.vertexPerm v
    rw [R.visits_cl,Finset.card_eq_one] at hv
    obtain ⟨a,ha⟩ := hv
    have hm : a ∈ R.outerCorners b := by rw [ha]; simp
    obtain ⟨hc,ho⟩ := Finset.mem_filter.mp hm
    exact ⟨a,(cl_eq_iff _ _ _).mpr ((mem_orbit _ _ _).mp hc).symm,ho⟩
  obtain ⟨rfl,ha⟩ := ha
  let n := (orbit R.vertexPerm a).card
  let seq := fun i : ℕ => label ((R.vertexPerm^(i+1)) a)
  have hn : 0 < n := by
    change 0 < (orbit R.vertexPerm a).card
    rw [orbit_card_eq_minimalPeriod]
    exact minimalPeriod_pos _ _
  have hout (i : ℕ) (hi : 0 < i) (hin : i < n) : ¬ R.IsOuter ((R.vertexPerm^i) a) := by
    intro ho
    have hh := R.unique_outer_of_visits_one a ha hv
      ((Perm.SameCycle.refl _ _).pow_right) ho
    exact pow_ne_of_lt_card_orbit R.vertexPerm a i hi hin hh
  have hadj' (i : ℕ) (hi : i < n-1) : L.Adj (seq i) (seq (i+1)) := by
    simpa only [seq,pow_succ',Perm.mul_apply] using
      hadj ((R.vertexPerm^(i+1)) a) (hout (i+1) (by omega) (by omega))
  have hred' (i : ℕ) (hi : i+2 ≤ n-1) : seq i ≠ seq (i+2) := by
    have hh := hred ((R.vertexPerm^(i+1)) a) (hout (i+1) (by omega) (by omega))
      (by simpa only [pow_succ',Perm.mul_apply] using hout (i+2) (by omega) (by omega))
    simpa only [seq,show i+2+1 = (i+1)+1+1 by omega,pow_succ',Perm.mul_apply] using hh
  have hstart : seq 0 = label (R.vertexPerm a) := rfl
  have hend : seq (n-1) = label a := by
    dsimp [seq]
    rw [Nat.sub_add_cancel hn,pow_card_orbit]
  let p := (SequenceWalk.walk L seq (n-1) hadj').copy hstart hend
  have hr : ReducedWalk p := by
    intro i hi
    simpa only [p,SimpleGraph.Walk.getVert_copy] using
      SequenceWalk.reduced_walk L seq (n-1) hadj' hred' i
        (by simpa only [p,SimpleGraph.Walk.length_copy] using hi)
  have hh := hboundary a ha p hr
  have hc : (R.innerCorners a).card = n-1 := by
    have hc := R.corner_count a
    rw [← R.visits_cl,hv] at hc
    omega
  rw [R.angles_cl,hc]
  simpa only [p,SimpleGraph.Walk.length_copy,SequenceWalk.length_walk] using hh

/-- Gauss--Bonnet on the actual permutation ribbon now rules out a filling whose
boundary turns are all separated by angle at least π in their target links. -/
theorem not_all_turns_geodesic
    (hclosed : ∀ a (p : L.Walk (label a) (label a)), 0 < p.length → ReducedWalk p →
      10 ≤ weight (R.color (cl R.vertexPerm a)) * p.length)
    (hboundary : ∀ a, R.IsOuter a →
      ∀ p : L.Walk (label (R.vertexPerm a)) (label a), ReducedWalk p →
        5 ≤ weight (R.color (cl R.vertexPerm a)) * p.length) : False :=
  R.counts.cannot_have_geodesic_boundary
    (R.interior_angle_lower L label hadj hred 10 hclosed)
    (R.boundary_angle_lower L label hadj hred hboundary)

end Release075.TriangleRibbon

end OAI
