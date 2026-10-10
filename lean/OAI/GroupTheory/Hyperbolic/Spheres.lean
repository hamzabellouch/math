import OAI.GroupTheory.Hyperbolic.LiftedFilling

namespace OAI

namespace Release075
open Equiv PermCycles

/-- A finite labelled spherical map, possibly with several connected components.
All faces are triangles; there is no distinguished outer face. -/
structure TriangleSphere {E V : Type} (flip : E → E) (color : E → V)
    (face : E → E → E → Prop) where
  Dart : Type
  [dartFintype : Fintype Dart]
  reverse : Perm Dart
  next : Perm Dart
  reverse_involutive : Function.Involutive reverse
  reverse_ne : ∀ a, reverse a ≠ a
  label : Dart → E
  reverse_label : ∀ a, label (reverse a) = flip (label a)
  color_next : ∀ a, color (label ((reverse*next) a)) = color (label a)
  planar : PlanarMap reverse next
  triangular : ∀ a, (next^3) a = a ∧ next a ≠ a ∧
    face (label a) (label (next a)) (label ((next^2) a))

attribute [instance] TriangleSphere.dartFintype

namespace TriangleSphere
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}
variable (D : TriangleSphere flip color face)

structure Dipole where
  dart : Fin 6 ↪ D.Dart
  next_dart : ∀ j, D.next (dart j) = dart (dipoleFace j)
  reverse_zero : D.reverse (dart 0) = dart 3
  color10 : color (D.label (dart 1)) ≠ color (D.label (dart 0))
  color21 : color (D.label (dart 2)) ≠ color (D.label (dart 1))
  label51 : D.label (dart 5) = flip (D.label (dart 1))
  label42 : D.label (dart 4) = flip (D.label (dart 2))

theorem reverse_not_sameCycle (a : D.Dart)
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a) :
    ¬ D.next.SameCycle a (D.reverse a) := by
  obtain ⟨hp,hn,hface⟩ := D.triangular a
  obtain ⟨h01,h12,h20⟩ := hf _ _ _ hface
  intro h
  have hm : D.reverse a ∈ orbit D.next a := (mem_orbit _ _ _).mpr h
  rw [orbit_eq_image D.next a (by omega : 0 < 3) hp] at hm
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hm
  fin_cases i
  · exact D.reverse_ne a hi.symm
  · have h := D.color_next ((D.next^2) a)
    have h3 : D.next ((D.next^2) a) = a := by simpa only [pow_succ',Perm.mul_apply] using hp
    simp only [Perm.mul_apply,h3,← hi] at h
    exact h12 h
  · have h := D.color_next (D.next a)
    have hr : D.reverse ((D.next^2) a) = a := by rw [hi,D.reverse_involutive]
    change color (D.label (D.reverse ((D.next^2) a))) = color (D.label (D.next a)) at h
    rw [hr] at h
    exact h01 h

/-- Internal reversal of a link walk creates a cancellable pair, when the face
labels are determined by two consecutive sides. -/
theorem dipole_of_link_backtrack
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a)
    (hflip : ∀ e, flip (flip e) = e)
    (hmirror : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
    (hunique : ∀ a b c c', face a b c → face a b c' → c = c')
    (x : D.Dart)
    (hback : D.label x = D.label ((D.reverse*D.next) ((D.reverse*D.next) x))) :
    Nonempty D.Dipole := by
  let a := D.next x
  let b := D.reverse a
  obtain ⟨hp,hne,hfa⟩ := D.triangular a
  obtain ⟨hp',hne',hfb⟩ := D.triangular b
  have hx3 := (D.triangular x).1
  have hax : (D.next^2) a = x := by
    change (D.next^2) (D.next x) = x
    simpa only [pow_succ,Perm.mul_apply] using hx3
  have h42 : D.label (D.next b) = flip (D.label ((D.next^2) a)) := by
    have he : D.label x = flip (D.label (D.next b)) := hback.trans (D.reverse_label (D.next b))
    rw [hax,he,hflip]
  have h51 : D.label ((D.next^2) b) = flip (D.label (D.next a)) := by
    apply hunique (D.label b) (D.label (D.next b)) _ _ hfb
    rw [h42]
    change face (D.label (D.reverse a)) (flip (D.label ((D.next^2) a))) (flip (D.label (D.next a)))
    rw [D.reverse_label]
    exact hmirror _ _ _ hfa
  have hab : ¬ D.next.SameCycle a b := D.reverse_not_sameCycle a hf
  let e := trianglePairEmbedding D.next a b hp hne hp' hne' hab
  obtain ⟨he0,he1,he2,he3,he4,he5⟩ := trianglePairEmbedding_values D.next a b hp hne hp' hne' hab
  have hnext : ∀ j, D.next (e j) = e (dipoleFace j) := by
    have h3 : D.next ((D.next^2) a) = a := by simpa only [pow_succ',Perm.mul_apply] using hp
    have h3' : D.next ((D.next^2) b) = b := by simpa only [pow_succ',Perm.mul_apply] using hp'
    intro j
    fin_cases j <;> first | rfl | exact h3 | exact h3'
  obtain ⟨h01,h12,_⟩ := hf _ _ _ hfa
  refine ⟨{
    dart := e
    next_dart := hnext
    reverse_zero := by rw [he0,he3]
    color10 := by rw [he1,he0]; exact h01.symm
    color21 := by rw [he2,he1]; exact h12.symm
    label51 := by rw [he5,he1]; exact h51
    label42 := by rw [he4,he2]; exact h42 }⟩

theorem noDipole_link_reduced
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a)
    (hflip : ∀ e, flip (flip e) = e)
    (hmirror : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
    (hunique : ∀ a b c c', face a b c → face a b c' → c = c')
    (hD : IsEmpty D.Dipole)
    (x : D.Dart) :
    D.label x ≠ D.label ((D.reverse*D.next) ((D.reverse*D.next) x)) := by
  intro h
  obtain ⟨P⟩ := D.dipole_of_link_backtrack hf hflip hmirror hunique x h
  exact hD.false P

abbrev vertexPerm : Perm D.Dart := D.reverse*D.next

noncomputable def paint (q : V → Fin 3) : Cycles D.vertexPerm → Fin 3 :=
  descend D.vertexPerm (fun a => q (color (D.label a)))
    (fun a => congrArg q (D.color_next a))

@[simp] theorem paint_cl (q : V → Fin 3) (a : D.Dart) :
    D.paint q (cl D.vertexPerm a) = q (color (D.label a)) := descend_cl _ _ _ _

noncomputable def vertexAngle (q : V → Fin 3) (v : Cycles D.vertexPerm) : ℝ :=
  TriangleRibbon.weight (D.paint q v) * Fintype.card {a : D.Dart // cl D.vertexPerm a = v}

theorem sum_angles (q : V ≃ Fin 3)
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a) :
    ∑ v, D.vertexAngle q v = 5 * Fintype.card (Cycles D.next) := by
  have hfiber (c : Cycles D.next) :
      (∑ a : {a : D.Dart // cl D.next a = c},
        TriangleRibbon.weight (q (color (D.label a)))) = 5 := by
    obtain ⟨a,rfl⟩ := cl_surjective D.next c
    obtain ⟨hp,hn,hface⟩ := D.triangular a
    obtain ⟨hab,hbc,hca⟩ := hf _ _ _ hface
    have hb := three_color_bijective D.next a (fun a => q (color (D.label a))) hp hn
      (fun h => hab (q.injective h)) (fun h => hbc (q.injective h))
      (fun h => hca (q.injective h))
    have he := (Equiv.ofBijective _ hb).sum_comp TriangleRibbon.weight
    have he' : (∑ x : {x : D.Dart // cl D.next x = cl D.next a},
        TriangleRibbon.weight (q (color (D.label x)))) = ∑ i, TriangleRibbon.weight i := he
    rw [he']
    norm_num [Fin.sum_univ_succ,TriangleRibbon.weight]
  have hv : ∑ v, D.vertexAngle q v =
      ∑ a : D.Dart, TriangleRibbon.weight (q (color (D.label a))) := by
    have he := (Equiv.sigmaFiberEquiv (cl D.vertexPerm)).sum_comp
      (fun a => TriangleRibbon.weight (q (color (D.label a))))
    simp only [Fintype.sum_sigma,Equiv.sigmaFiberEquiv_apply] at he
    rw [← he]
    apply Finset.sum_congr rfl
    intro v _
    have hie (a : {a : D.Dart // cl D.vertexPerm a = v}) :
        q (color (D.label a)) = D.paint q v := by
      rw [← D.paint_cl q a,a.property]
    simp only [hie,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,vertexAngle,mul_comm]
  rw [hv]
  have he := (Equiv.sigmaFiberEquiv (cl D.next)).sum_comp
    (fun a => TriangleRibbon.weight (q (color (D.label a))))
  simp only [Fintype.sum_sigma,Equiv.sigmaFiberEquiv_apply] at he
  rw [← he]
  simp only [hfiber,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm]

theorem local_angle_lower (q : V → Fin 3) (L : SimpleGraph E)
    (hadj : ∀ a b c, face a b c → L.Adj a (flip b))
    (hred : ∀ a, D.label a ≠ D.label (D.vertexPerm (D.vertexPerm a)))
    (hclosed : ∀ a (p : L.Walk a a), 0 < p.length → ReducedWalk p →
      10 ≤ TriangleRibbon.weight (q (color a)) * p.length)
    (v : Cycles D.vertexPerm) : 10 ≤ D.vertexAngle q v := by
  obtain ⟨a,rfl⟩ := cl_surjective D.vertexPerm v
  let n := (orbit D.vertexPerm a).card
  let seq := fun i : ℕ => D.label ((D.vertexPerm^i) a)
  have hn : 0 < n := by
    change 0 < (orbit D.vertexPerm a).card
    rw [orbit_card_eq_minimalPeriod]
    exact minimalPeriod_pos _ _
  have hstep (b : D.Dart) : L.Adj (D.label b) (D.label (D.vertexPerm b)) := by
    change L.Adj (D.label b) (D.label (D.reverse (D.next b)))
    rw [D.reverse_label]
    exact hadj _ _ _ (D.triangular b).2.2
  have hs (i : ℕ) (_hi : i < n) : L.Adj (seq i) (seq (i+1)) := by
    simpa only [seq,pow_succ',Perm.mul_apply] using hstep ((D.vertexPerm^i) a)
  have hres (i : ℕ) (_hi : i+2 ≤ n) : seq i ≠ seq (i+2) := by
    simpa only [seq,show i+2 = (i+1)+1 by omega,pow_succ',Perm.mul_apply] using
      hred ((D.vertexPerm^i) a)
  have hend : seq n = D.label a := congrArg D.label (pow_card_orbit D.vertexPerm a)
  let p := (SequenceWalk.walk L seq n hs).copy (show seq 0 = D.label a from rfl) hend
  have hlen : p.length = n := (SimpleGraph.Walk.length_copy _ _ _).trans
    (SequenceWalk.length_walk L seq n hs)
  have hp : ReducedWalk p := by
    intro i hi
    simpa only [p,SimpleGraph.Walk.getVert_copy] using
      SequenceWalk.reduced_walk L seq n hs hres i
        (by simpa only [p,SimpleGraph.Walk.length_copy] using hi)
  have h := hclosed (D.label a) p (by rw [hlen]; exact hn) hp
  simpa only [vertexAngle,paint_cl,card_fiber,hlen,n] using h

/-- Angular Gauss--Bonnet on a closed genus-zero map forbids a nonempty reduced
sphere. This is a statement about actual finite permutation maps, not an
asphericity or torsion-freeness assumption. -/
theorem empty_of_angles (q : V ≃ Fin 3)
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a)
    (hmin : ∀ v, 10 ≤ D.vertexAngle q v) : IsEmpty D.Dart := by
  have hs := D.sum_angles q hf
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hmin v)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  rw [hs] at hsum
  have hr := card_eq_mul_cycles D.reverse 2
    (orbit_card_involution D.reverse D.reverse_involutive D.reverse_ne)
  have hfcard := card_eq_mul_cycles D.next 3
    (fun a => orbit_card_three D.next a (D.triangular a).1 (D.triangular a).2.1)
  have he := D.planar
  simp only [PlanarMap,cycleCount,Nat.card_eq_fintype_card] at he
  have hzero : Fintype.card (Quotient (components D.reverse D.next)) = 0 := by
    have hs' : 2 * Fintype.card (Cycles D.vertexPerm) ≤ Fintype.card (Cycles D.next) := by
      have : (2 : ℝ) * Fintype.card (Cycles D.vertexPerm) ≤ Fintype.card (Cycles D.next) := by
        linarith
      exact_mod_cast this
    change 2 * Fintype.card (Cycles (D.reverse * D.next)) ≤ Fintype.card (Cycles D.next) at hs'
    unfold componentCount at he
    rw [Nat.card_eq_fintype_card] at he
    omega
  exact ⟨fun a => (Fintype.card_pos_iff.mpr ⟨Quotient.mk _ a⟩).ne' hzero⟩

end TriangleSphere
end Release075

namespace Release075.MarkedLineData
open Equiv PermCycles
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

/-- Every nonempty spherical map over the actual presentation has a dipole. -/
theorem sphere_empty_of_noDipole
    (D : TriangleSphere (d.presentation hr).flipEdge (d.presentation hr).edgeTarget
      (d.presentation hr).TriangleFace) (hD : IsEmpty D.Dipole) : IsEmpty D.Dart := by
  let L := (d.allLink hr).comap (d.linkDirection hr)
  apply D.empty_of_angles (d.presentation hr).vertexColor
    (fun _ _ _ => BlockPresentation.TriangleFace.colors _)
  apply D.local_angle_lower (d.presentation hr).vertexColor L
    (fun _ _ _ h => d.face_corner_adj hr h)
    (D.noDipole_link_reduced
      (fun _ _ _ => BlockPresentation.TriangleFace.colors _)
      (d.presentation hr).flipEdge_flipEdge
      (fun _ _ _ => BlockPresentation.TriangleFace.mirror _)
      (fun _ _ _ _ => BlockPresentation.TriangleFace.unique _) hD)
  intro a p hn hp
  let f : L →g d.allLink hr := SimpleGraph.Hom.comap (d.linkDirection hr) (d.allLink hr)
  have h := d.allLink_closed hr _ (p.map f)
    (by simpa only [SimpleGraph.Walk.length_map] using hn)
    (hp.map f (fun _ _ _ _ _ h => d.linkDirection_injective hr h))
  simp only [SimpleGraph.Walk.length_map] at h
  change 12 ≤ TriangleRibbon.weight (d.linkColor hr (d.linkDirection hr a)) * p.length at h
  rw [d.linkDirection_color hr] at h
  linarith

end Release075.MarkedLineData

namespace Release075.TriangleSphere
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

/-- Evaluate once at every oriented corner. For cyclic face values this is three
 times the ordinary integral face chain; no unproved chain-complex property is used. -/
def cornerSum (D : TriangleSphere flip color face) (F : E → E → E → M) : M :=
  ∑ a, F (D.label a) (D.label (D.next a)) (D.label ((D.next^2) a))

/-- Remove an actual dipole, preserving every additive cyclic antisymmetric
face evaluation. -/
theorem Dipole.delete {D : TriangleSphere flip color face} (P : D.Dipole)
    (F : E → E → E → M)
    (hrot : ∀ a b c, face a b c → F b c a = F a b c)
    (hmir : ∀ a b c, face a b c → F (flip a) (flip c) (flip b) = -F a b c) :
    ∃ D' : TriangleSphere flip color face,
      Fintype.card D'.Dart < Fintype.card D.Dart ∧ D'.cornerSum F = D.cornerSum F := by
  let e := P.dart
  have h14 : color (D.label (e 1)) = color (D.label (e 4)) := by
    have h := D.color_next (P.dart 1)
    simp only [Perm.mul_apply,P.next_dart,dipoleFace_one,D.reverse_label] at h
    exact h.symm.trans (congrArg color P.label42.symm)
  obtain ⟨r',hi',hn',hp',hc',he',heq,_⟩ :=
    isolate_dipole D.reverse D.next D.reverse_involutive D.reverse_ne
      (color ∘ D.label) D.color_next e P.next_dart P.reverse_zero
      P.color10 P.color21 h14 D.planar
  have hl₁ : ∀ z, D.label (rePair D.reverse (e 1) (e 5) z) = flip (D.label z) :=
    rePair_labels D.reverse D.label flip D.reverse_label
      ((D.reverse_label (e 1)).trans P.label51.symm)
  have hl' : ∀ z, D.label (r' z) = flip (D.label z) := by
    rw [heq]
    exact rePair_labels _ D.label flip hl₁ ((hl₁ (e 2)).trans P.label42.symm)
  let hr : ∀ a, (r' a ∉ Set.range e) ↔ (a ∉ Set.range e) :=
    fun a => not_congr (range_invariant r' dipoleReverse e he' a)
  let hf : ∀ a, (D.next a ∉ Set.range e) ↔ (a ∉ Set.range e) :=
    fun a => not_congr (range_invariant D.next dipoleFace e P.next_dart a)
  let D' : TriangleSphere flip color face := {
    Dart := {a : D.Dart // a ∉ Set.range e}
    reverse := r'.subtypePerm hr
    next := D.next.subtypePerm hf
    reverse_involutive := fun a => Subtype.ext (hi' a.val)
    reverse_ne := fun a h => hn' a.val (congrArg Subtype.val h)
    label := D.label ∘ Subtype.val
    reverse_label := fun a => hl' a.val
    color_next := fun a => hc' a.val
    planar := by
      simpa only [PlanarMap,← Nat.card_eq_fintype_card] using
        hp'.restrict (fun a => a ∉ Set.range e) hr hf
    triangular := fun a => ⟨Subtype.ext (D.triangular a.val).1,
      fun h => (D.triangular a.val).2.1 (congrArg Subtype.val h),(D.triangular a.val).2.2⟩ }
  refine ⟨D',?_,?_⟩
  · exact Fintype.card_subtype_lt (x := e 0) (not_not.mpr ⟨0,rfl⟩)
  let f : D.Dart → M := fun a => F (D.label a) (D.label (D.next a)) (D.label ((D.next^2) a))
  have hcycle (a : D.Dart) : f (D.next a) = f a := by
    have h3' : (D.next^2) (D.next a) = a := by
      simpa only [pow_succ,Perm.mul_apply] using (D.triangular a).1
    change F (D.label (D.next a)) (D.label ((D.next^2) a))
      (D.label ((D.next^2) (D.next a))) = _
    rw [h3']
    exact hrot _ _ _ (D.triangular a).2.2
  have hecycle (j : Fin 6) : f (e (dipoleFace j)) = f (e j) := by
    rw [← P.next_dart]
    exact hcycle _
  have heNext (j : Fin 6) : D.next (e j) = e (dipoleFace j) := P.next_dart j
  have he42 : D.label (e 4) = flip (D.label (e 2)) := P.label42
  have he51 : D.label (e 5) = flip (D.label (e 1)) := P.label51
  have h03 : f (e 3) = - f (e 0) := by
    have hz : D.label (e 3) = flip (D.label (e 0)) := by
      rw [← P.reverse_zero,D.reverse_label]
    have hs (j : Fin 6) : (D.next^2) (e j) = e (dipoleFace (dipoleFace j)) := by
      simp only [pow_two,Perm.mul_apply,heNext]
    simp only [f,heNext,hs,dipoleFace_zero,dipoleFace_one,
      dipoleFace_three,dipoleFace_four]
    rw [hz,he42,he51]
    exact hmir _ _ _ (by simpa only [heNext,hs,dipoleFace_zero,dipoleFace_one] using
      (D.triangular (e 0)).2.2)
  have hsix : ∑ j : Fin 6, f (e j) = 0 := by
    have h1 := hecycle 0
    have h2 := hecycle 1
    have h4 := hecycle 3
    have h5 := hecycle 4
    simp only [dipoleFace_zero,dipoleFace_one,dipoleFace_three,dipoleFace_four] at h1 h2 h4 h5
    simp only [Fin.sum_univ_succ,Fin.succ_zero_eq_one]
    change f (e 0)+(f (e 1)+(f (e 2)+(f (e 3)+(f (e 4)+(f (e 5)+0))))) = 0
    rw [h2,h1,h5,h4,h03]
    abel
  have hrange : ∑ a : {a : D.Dart // a ∈ Set.range e}, f a = 0 := by
    have h := (Equiv.ofInjective e e.injective).sum_comp (fun a => f a.val)
    exact h.symm.trans hsix
  have hpart : (∑ a : {a : D.Dart // a ∈ Set.range e}, f a.val) +
      (∑ a : {a : D.Dart // a ∉ Set.range e}, f a.val) = ∑ a, f a := by
    simpa only [Fintype.sum_sum_type,Equiv.sumCompl_apply_inl,Equiv.sumCompl_apply_inr] using
      (Equiv.sumCompl (fun a => a ∈ Set.range e)).sum_comp f
  rw [hrange,zero_add] at hpart
  exact hpart

/-- Diagrammatic reducibility annihilates integral spherical face chains. -/
theorem cornerSum_eq_zero
    (hempty : ∀ D : TriangleSphere flip color face, IsEmpty D.Dipole → IsEmpty D.Dart)
    (F : E → E → E → M)
    (hrot : ∀ a b c, face a b c → F b c a = F a b c)
    (hmir : ∀ a b c, face a b c → F (flip a) (flip c) (flip b) = -F a b c)
    (D : TriangleSphere flip color face) : D.cornerSum F = 0 := by
  generalize hn : Fintype.card D.Dart = n
  induction n using Nat.strong_induction_on generalizing D with
  | h n ih =>
    by_cases hd : Nonempty D.Dipole
    · obtain ⟨P⟩ := hd
      obtain ⟨D',hlt,he⟩ := P.delete F hrot hmir
      rw [← he]
      exact ih (Fintype.card D'.Dart) (hn ▸ hlt) D' rfl
    · have : IsEmpty D.Dart := hempty D (not_nonempty_iff.mp hd)
      exact Finset.sum_eq_zero (fun b _ => isEmptyElim b)

end Release075.TriangleSphere

namespace Release075.TriangleSphere
open Equiv PermCycles
variable {I B : Type} {r : ℕ} {d : BlockPresentation I B r}

def forgetLift (D : TriangleSphere d.liftedFlip d.liftedTarget d.LiftedFace) :
    TriangleSphere d.flipEdge d.edgeTarget d.TriangleFace where
  Dart := D.Dart
  reverse := D.reverse
  next := D.next
  reverse_involutive := D.reverse_involutive
  reverse_ne := D.reverse_ne
  label a := (D.label a).1
  reverse_label a := congrArg Prod.fst (D.reverse_label a)
  color_next a := congrArg Prod.fst (D.color_next a)
  planar := D.planar
  triangular a := let ht := D.triangular a; ⟨ht.1,ht.2.1,ht.2.2.1⟩

/-- Matching opposite face labels at a shared lifted edge forces matching group
coordinates on the other two edges. Thus reduction cannot hide a downstairs dipole. -/
def Dipole.lift {D : TriangleSphere d.liftedFlip d.liftedTarget d.LiftedFace}
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
    color10 := fun h => P.color10 (congrArg Prod.fst h)
    color21 := fun h => P.color21 (congrArg Prod.fst h)
    label51 := h51
    label42 := h42 }

theorem noDipole_forgetLift {D : TriangleSphere d.liftedFlip d.liftedTarget d.LiftedFace}
    (h : IsEmpty D.Dipole) : IsEmpty D.forgetLift.Dipole := ⟨fun P => h.false P.lift⟩

end Release075.TriangleSphere

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

theorem lifted_sphere_empty_of_noDipole
    (D : TriangleSphere (d.presentation hr).liftedFlip (d.presentation hr).liftedTarget
      (d.presentation hr).LiftedFace) (hD : IsEmpty D.Dipole) : IsEmpty D.Dart :=
  d.sphere_empty_of_noDipole hr D.forgetLift (TriangleSphere.noDipole_forgetLift hD)

end Release075.MarkedLineData

end OAI
