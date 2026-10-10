import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.SurfaceSurgery
import Mathlib.GroupTheory.Perm.List

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.BoundaryBand
open scoped Classical
variable {α : Type*} [DecidableEq α]

/-- Joining incoming germs is postcomposition of the old successor with the transposition of its two
new targets. This does not identify facet labels. -/
def incomingSwitch (σ : Equiv.Perm α) (x y : α) : Equiv.Perm α :=
  Equiv.swap x y * σ

@[simp] theorem incomingSwitch_invol (σ : Equiv.Perm α) (x y : α) :
    incomingSwitch (incomingSwitch σ x y) x y=σ := by
  simp [incomingSwitch,←mul_assoc]

theorem formPerm_append (x y : α) (L M : List α)
    (h : ((x::L)++(y::M)).Nodup) :
    ((x::L)++(y::M)).formPerm=
      Equiv.swap x y*((x::L).formPerm*(y::M).formPerm) := by
  induction L generalizing x with
  | nil => simp [List.formPerm_cons_cons]
  | cons a L ih =>
    have ht : ((a::L)++(y::M)).Nodup := h.tail
    have hxy : x≠y := (List.nodup_append.mp h).2.2 x (by simp) y (by simp)
    have hay : a≠y := (List.nodup_append.mp ht).2.2 a (by simp) y (by simp)
    simp only [List.cons_append,List.formPerm_cons_cons]
    have hi := ih a ht
    simp only [List.cons_append] at hi
    rw [hi]
    rw [←mul_assoc,Equiv.mul_swap_eq_swap_mul]
    simp only [Equiv.swap_apply_right,Equiv.swap_apply_of_ne_of_ne hxy.symm hay.symm]
    simp only [mul_assoc]

theorem formPerm_append_rotate (L M : List α) (hn : (L++M).Nodup) :
    (M++L).formPerm=(L++M).formPerm := by
  have hr : (L++M).rotate L.length=M++L := by
    rw [List.rotate_eq_drop_append_take (by simp)]
    simp
  rw [←hr,List.formPerm_rotate _ hn]

/-- Exact new permutation, with an arbitrary untouched successor factor. -/
theorem join_cycles (x y : α) (L M : List α) (ρ : Equiv.Perm α)
    (h : ((x::L)++(y::M)).Nodup) :
    incomingSwitch ((x::L).formPerm*(y::M).formPerm*ρ) x y=
      (((x::L)++(y::M)).formPerm)*ρ := by
  rw [formPerm_append x y L M h]
  simp [incomingSwitch,mul_assoc]

/-- The inverse operation splits one old boundary circle into precisely the specified two circles;
this is not merely a change in the numerical count. -/
theorem split_cycle (x y : α) (L M : List α) (ρ : Equiv.Perm α)
    (h : ((x::L)++(y::M)).Nodup) :
    incomingSwitch ((((x::L)++(y::M)).formPerm)*ρ) x y=
      (x::L).formPerm*(y::M).formPerm*ρ := by
  rw [←join_cycles x y L M ρ h,incomingSwitch_invol]

/-- The band changes exactly the two indicated incoming germs and nothing else. Repeated incidences
of a facet remain separate α values. -/
theorem incomingSwitch_exact (σ : Equiv.Perm α) (x y z : α) :
    incomingSwitch σ x y z=
      if σ z=x then y else if σ z=y then x else σ z := by
  simp only [incomingSwitch,Equiv.Perm.mul_apply,Equiv.swap_apply_def]

section Holonomy
variable {G : Type*} [Group G]

/-- Same right-to-left convention as Diagram.boundaryWord. -/
def word (h : α → G) (L : List α) : G := (L.map h).reverse.prod

omit [DecidableEq α] in
@[simp] theorem word_nil (h : α → G) : word h []=1 := rfl
omit [DecidableEq α] in
@[simp] theorem word_cons (h : α → G) (x : α) (L : List α) :
    word h (x::L)=word h L*h x := by simp [word]
omit [DecidableEq α] in
@[simp] theorem word_append (h : α → G) (L M : List α) :
    word h (L++M)=word h M*word h L := by simp [word]

/-- The same band transports change only its two first departing edges; all old side occurrences
elsewhere retain their precise old matrix. -/
def joinEdges (h : α → G) (x y : α) (t : G) (z : α) : G :=
  if z=x then h z*t else if z=y then h z*t⁻¹ else h z

omit [DecidableEq α] in
theorem word_eq_of_agree {h k : α → G} {L : List α}
    (hh : ∀ z∈L,h z=k z) : word h L=word k L := by
  unfold word
  congr 2
  exact List.map_congr_left hh

theorem joinEdges_left (h : α → G) (x y : α) (t : G) (L M : List α)
    (hn : ((x::L)++(y::M)).Nodup) :
    word (joinEdges h x y t) (x::L)=word h (x::L)*t := by
  have hx : x∉L := (List.nodup_cons.mp (List.nodup_append.mp hn).1).1
  have hy : y∉L := by
    intro hh
    exact (List.nodup_append.mp hn).2.2 y (by simp [hh]) y (by simp) rfl
  rw [word_cons,word_cons]
  have hw : word (joinEdges h x y t) L=word h L :=
    word_eq_of_agree (fun z hz => by
      have hxz : z≠x := by rintro rfl; exact hx hz
      have hyz : z≠y := by rintro rfl; exact hy hz
      simp [joinEdges,hxz,hyz])
  rw [hw]
  simp [joinEdges,mul_assoc]

theorem joinEdges_right (h : α → G) (x y : α) (t : G) (L M : List α)
    (hn : ((x::L)++(y::M)).Nodup) :
    word (joinEdges h x y t) (y::M)=word h (y::M)*t⁻¹ := by
  have hy : y∉M := (List.nodup_cons.mp (List.nodup_append.mp hn).2.1).1
  have hx : x∉M := by
    intro hh
    exact (List.nodup_append.mp hn).2.2 x (by simp) x (by simp [hh]) rfl
  have hxy : y≠x := ((List.nodup_append.mp hn).2.2 x (by simp) y (by simp)).symm
  rw [word_cons,word_cons]
  have hw : word (joinEdges h x y t) M=word h M :=
    word_eq_of_agree (fun z hz => by
      have hxz : z≠x := by rintro rfl; exact hx hz
      have hyz : z≠y := by rintro rfl; exact hy hz
      simp [joinEdges,hxz,hyz])
  rw [hw]
  simp [joinEdges,hxy,mul_assoc]

/-- In the joined positive cyclic word, the two edge changes give exactLY the band word used by
SurfaceSurgery, not an unproved holonomy input. -/
theorem joined_word (h : α → G) (x y : α) (t : G) (L M : List α)
    (hn : ((x::L)++(y::M)).Nodup) :
    word (joinEdges h x y t) ((y::M)++(x::L))=
      word h (x::L)*t*word h (y::M)*t⁻¹ := by
  rw [word_append,joinEdges_left h x y t L M hn,joinEdges_right h x y t L M hn]
  simp [mul_assoc]
end Holonomy
end IntegralCharacterVarieties.BoundaryBand

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical
open OccurrenceIncidence BoundaryBand
variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity)

abbrev BoundaryCircle := (f : F) × Fin (D.boundaryCount f)

def boundarySides (B : D.BoundaryCircle) : List (Side S arity) :=
  List.ofFn (fun i => D.boundarySide ⟨B.1,B.2,i⟩)

lemma boundarySides_nodup (B : D.BoundaryCircle) : (D.boundarySides B).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j h
  have hh := D.boundarySide.injective h
  simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using hh

lemma boundarySides_ne_nil (B : D.BoundaryCircle) : D.boundarySides B≠[] := by
  intro h
  have hl := congrArg List.length h
  simp only [boundarySides,List.length_ofFn,List.length_nil] at hl
  exact (Nat.ne_of_gt (D.boundaryPositive B.1 B.2)) hl

lemma boundarySides_disjoint (B C : D.BoundaryCircle) (h : B≠C) :
    ∀ x∈D.boundarySides B, ∀ y∈D.boundarySides C,x≠y := by
  intro x hx y hy hxy
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hy
  have hh := D.boundarySide.injective hxy
  apply h
  exact congrArg (fun z : (f : F) × (b : Fin (D.boundaryCount f)) ×
    Fin (D.boundaryLength f b) => (⟨z.1,z.2.1⟩ : D.BoundaryCircle)) hh

lemma boundarySides_append_nodup (B C : D.BoundaryCircle) (h : B≠C) :
    (D.boundarySides B++D.boundarySides C).Nodup :=
  List.nodup_append.mpr ⟨D.boundarySides_nodup B,D.boundarySides_nodup C,
    D.boundarySides_disjoint B C h⟩

lemma boundarySides_successor (B : D.BoundaryCircle)
    (i : Fin (D.boundaryLength B.1 B.2)) :
    (D.boundarySides B).formPerm (D.boundarySide ⟨B.1,B.2,i⟩)=
      D.ports.vertexAssembly.corners.boundaryNext (D.boundarySide ⟨B.1,B.2,i⟩) := by
  rw [D.boundaryNext]
  have hh := List.formPerm_apply_getElem (D.boundarySides B)
    (D.boundarySides_nodup B) i.val (by simp [boundarySides])
  simpa [boundarySides] using hh

lemma boundarySides_agree (B : D.BoundaryCircle) (x : Side S arity)
    (hx : x∈D.boundarySides B) :
    (D.boundarySides B).formPerm x=D.ports.vertexAssembly.corners.boundaryNext x := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  exact D.boundarySides_successor B i

/-- Remove the two old circle factors. Unlike an arbitrary factor, this one will be proved to fix
every occurrence on either selected circle. -/
def remainingSuccessor (B C : D.BoundaryCircle) : Equiv.Perm (Side S arity) :=
  ((D.boundarySides B).formPerm*(D.boundarySides C).formPerm)⁻¹*
    D.ports.vertexAssembly.corners.boundaryNext

theorem boundary_factorization (B C : D.BoundaryCircle) :
    D.ports.vertexAssembly.corners.boundaryNext=
      (D.boundarySides B).formPerm*(D.boundarySides C).formPerm*D.remainingSuccessor B C := by
  simp [remainingSuccessor,mul_assoc]

theorem remainingSuccessor_fixes (B C : D.BoundaryCircle) (hBC : B≠C)
    (x : Side S arity) (hx : x∈D.boundarySides B ∨ x∈D.boundarySides C) :
    D.remainingSuccessor B C x=x := by
  have hh : ((D.boundarySides B).formPerm*(D.boundarySides C).formPerm) x=
      D.ports.vertexAssembly.corners.boundaryNext x := by
    rcases hx with hx|hx
    · have hxc : x∉D.boundarySides C := fun hxc => D.boundarySides_disjoint B C hBC x hx x hxc rfl
      simp only [Equiv.Perm.mul_apply,List.formPerm_apply_of_notMem hxc]
      exact D.boundarySides_agree B x hx
    · have hy : (D.boundarySides C).formPerm x∈D.boundarySides C :=
        List.formPerm_apply_mem_of_mem hx
      have hyb : (D.boundarySides C).formPerm x∉D.boundarySides B :=
        fun hyb => D.boundarySides_disjoint B C hBC _ hyb _ hy rfl
      simp only [Equiv.Perm.mul_apply,List.formPerm_apply_of_notMem hyb]
      exact D.boundarySides_agree C x hx
  simp only [remainingSuccessor,Equiv.Perm.mul_apply,←hh]
  exact Equiv.symm_apply_apply _ _

/-- Old Diagram boundary successor after attaching a strip between these two circles. The resulting
joined circle retains all old occurrence labels exactly once. -/
theorem old_boundary_join (B C : D.BoundaryCircle) (hBC : B≠C)
    (x y : Side S arity) (L M : List (Side S arity))
    (hB : D.boundarySides B=x::L) (hC : D.boundarySides C=y::M) :
    incomingSwitch D.ports.vertexAssembly.corners.boundaryNext x y=
      (((x::L)++(y::M)).formPerm)*D.remainingSuccessor B C := by
  have hn := D.boundarySides_append_nodup B C hBC
  rw [hB,hC] at hn
  rw [D.boundary_factorization B C,hB,hC]
  exact join_cycles x y L M (D.remainingSuccessor B C) hn
section ActualHolonomy
open MatrixExpression SurfaceSurgery
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
variable (P : D.Punctures R) (g : D.Solution P A)

/-- Exact old edge matrix viewed in the chosen facet fiber. Outside that facet it is irrelevant and
set to 1; no old edge in that facet is replaced. -/
def boundaryValue (f : F) (a : Side S arity) :
    (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ :=
  if hf : D.ports.facet a=f then
    rebaseUnit (congrArg D.rank hf) (g.val.val (.side a)) else 1

lemma eval_rebase {m n : ℕ} (h : m=n) (w : D.Word R m) :
    rebaseUnit h (w.eval (algebraMap R A) g.val.val)=
      (h ▸ w).eval (algebraMap R A) g.val.val := by
  subst n
  rfl

lemma boundaryValue_at (f : F) (b : Fin (D.boundaryCount f))
    (i : Fin (D.boundaryLength f b)) :
    D.boundaryValue P g f (D.boundarySide ⟨f,b,i⟩)=D.evaluatedBoundaryEdge P g f b i := by
  rw [boundaryValue,dite_eq_left (D.boundaryFacet f b i)]
  exact D.eval_rebase P g (congrArg D.rank (D.boundaryFacet f b i)) (D.sideWord _)

lemma actual_boundary_word (f : F) (b : Fin (D.boundaryCount f)) :
    word (D.boundaryValue P g f) (D.boundarySides ⟨f,b⟩)=
      ((List.ofFn (D.evaluatedBoundaryEdge P g f b)).reverse).prod := by
  simp only [word,boundarySides,List.map_ofFn,Function.comp_def,D.boundaryValue_at P g]

/-- Join the two selected old circles whenever their based surface-word order is explicitly
recorded. The new word is DERIVED from changed old side matrices, and the new handle is
constructed from the same band transport t. -/
theorem old_same_facet_band (f : F) (b c : Fin (D.boundaryCount f)) (hbc : b≠c)
    (x y : Side S arity) (L M : List (Side S arity))
    (hb : D.boundarySides ⟨f,b⟩=x::L) (hc : D.boundarySides ⟨f,c⟩=y::M)
    (T : List (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ)
    (horder : D.evaluatedBoundaries P g f=
      word (D.boundaryValue P g f) (x::L)::word (D.boundaryValue P g f) (y::M)::T)
    (t : (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ) :
    incomingSwitch D.ports.vertexAssembly.corners.boundaryNext x y=
      (((y::M)++(x::L)).formPerm)*D.remainingSuccessor ⟨f,b⟩ ⟨f,c⟩ ∧
    surfaceProduct (conjugateHandles t (D.evaluatedHandles P g f)++
      [(t,word (D.boundaryValue P g f) (x::L))])
      (word (joinEdges (D.boundaryValue P g f) x y t) ((y::M)++(x::L))::
        conjugateBoundaries t T)=scalarUnit (D.rank f) (D.diskScalar P f) ∧
    (conjugateHandles t (D.evaluatedHandles P g f)++
      [(t,word (D.boundaryValue P g f) (x::L))]).length=D.genus f+1 := by
  have hBC : (⟨f,b⟩ : D.BoundaryCircle)≠⟨f,c⟩ := by
    simpa only [ne_eq,Sigma.mk.inj_iff,heq_eq_eq,true_and] using hbc
  have hn := D.boundarySides_append_nodup ⟨f,b⟩ ⟨f,c⟩ hBC
  rw [hb,hc] at hn
  refine ⟨?_,?_,?_⟩
  · rw [formPerm_append_rotate _ _ hn]
    exact D.old_boundary_join ⟨f,b⟩ ⟨f,c⟩ hBC x y L M hb hc
  · rw [joined_word _ x y t L M hn]
    exact D.actual_join_same P g f T _ _ t horder
  · simp [conjugateHandles,evaluatedHandles]
private theorem ofFn_two {β : Type*} {n : ℕ} (hn : 2≤n) (v : Fin n → β) :
    List.ofFn v=v ⟨0,by omega⟩::v ⟨1,by omega⟩::(List.ofFn v).drop 2 := by
  rcases n with _|n
  · omega
  rcases n with _|n
  · omega
  simp only [List.ofFn_succ,List.drop_succ_cons,List.drop_zero]
  rfl

/-- The cyclic bags below are the original first two boundary occurrence circles. -/
theorem old_first_two_band (f : F) (hn : 2≤D.boundaryCount f)
    (t : (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ) :
    ∃ (x y : Side S arity) (L M : List (Side S arity)),
      D.boundarySides ⟨f,⟨0,by omega⟩⟩=x::L ∧
      D.boundarySides ⟨f,⟨1,by omega⟩⟩=y::M ∧
      incomingSwitch D.ports.vertexAssembly.corners.boundaryNext x y=
        (((y::M)++(x::L)).formPerm)*D.remainingSuccessor ⟨f,⟨0,by omega⟩⟩ ⟨f,⟨1,by omega⟩⟩ ∧
      surfaceProduct (conjugateHandles t (D.evaluatedHandles P g f)++
        [(t,word (D.boundaryValue P g f) (x::L))])
        (word (joinEdges (D.boundaryValue P g f) x y t) ((y::M)++(x::L))::
          conjugateBoundaries t ((D.evaluatedBoundaries P g f).drop 2))=
        scalarUnit (D.rank f) (D.diskScalar P f) ∧
      (conjugateHandles t (D.evaluatedHandles P g f)++
        [(t,word (D.boundaryValue P g f) (x::L))]).length=D.genus f+1 := by
  let b : Fin (D.boundaryCount f) := ⟨0,by omega⟩
  let c : Fin (D.boundaryCount f) := ⟨1,by omega⟩
  have hbc : b≠c := by intro h; have hh := congrArg Fin.val h; simp [b,c] at hh
  cases hb : D.boundarySides ⟨f,b⟩ with
  | nil => exact (D.boundarySides_ne_nil ⟨f,b⟩ hb).elim
  | cons x L =>
    cases hc : D.boundarySides ⟨f,c⟩ with
    | nil => exact (D.boundarySides_ne_nil ⟨f,c⟩ hc).elim
    | cons y M =>
      refine ⟨x,y,L,M,rfl,rfl,?_⟩
      apply D.old_same_facet_band P g f b c hbc x y L M hb hc _ ?_ t
      rw [←hb,←hc,D.actual_boundary_word P g f b,D.actual_boundary_word P g f c]
      exact ofFn_two hn _

end ActualHolonomy

end IntegralCharacterVarieties.SurfacePresentation.Diagram

end

end OAI
