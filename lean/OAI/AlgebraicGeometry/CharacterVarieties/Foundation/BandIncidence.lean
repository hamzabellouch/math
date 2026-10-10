import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.SurfacePresentation

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.OccurrenceIncidence.PortAssembly
open scoped Classical
open VertexTable

/-- Three old subintervals and one transverse identity connection. This is the intermediate inverse handle cut, before the two-flag gallery replaces the identity connection by proper lower strips. No fresh facet is introduced. -/
abbrev BandCutSeam (S : Type) := (S × Fin 3) ⊕ Unit
abbrev BandCutVertex (V S : Type) (q : S) := V ⊕ (({s : S // s ≠ q} × Bool) ⊕ Bool)
abbrev bandCutArity {S : Type} (arity : S → ℕ) : BandCutSeam S → ℕ
  | .inl (s,_) => arity s
  | .inr _ => 1

variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)

abbrev bandCutKind : BandCutVertex V S q → Kind
  | .inl v => A.kind v
  | .inr (.inl (s,_)) => .passage (arity s) .continuation
  | .inr (.inr b) => .splitting 0 (arity q) 0 b

def bandCutSplitPort : Bool → SplitPort → LocalPort (BandCutVertex V S q) (A.bandCutKind q)
  | false,p => ⟨.inr (.inr false),p⟩
  | true,p => ⟨.inr (.inr true),p⟩

def bandCutInteriorPort (s : S) (b p : Bool) : LocalPort (BandCutVertex V S q) (A.bandCutKind q) :=
  if h : s=q then A.bandCutSplitPort q b (if p=b then .branch else .after)
  else ⟨.inr (.inl (⟨s,h⟩,b)),p⟩

def bandCutAttachTo : LocalPort (BandCutVertex V S q) (A.bandCutKind q) → BandCutSeam S × Bool
  | ⟨.inl v,p⟩ => (.inl ((A.attach ⟨v,p⟩).1,if (A.attach ⟨v,p⟩).2 then 2 else 0),(A.attach ⟨v,p⟩).2)
  | ⟨.inr (.inl (s,false)),false⟩ => (.inl (s,0),true)
  | ⟨.inr (.inl (s,false)),true⟩ => (.inl (s,1),false)
  | ⟨.inr (.inl (s,true)),false⟩ => (.inl (s,1),true)
  | ⟨.inr (.inl (s,true)),true⟩ => (.inl (s,2),false)
  | ⟨.inr (.inr false),.before⟩ => (.inr (),true)
  | ⟨.inr (.inr false),.after⟩ => (.inl (q,1),false)
  | ⟨.inr (.inr false),.branch⟩ => (.inl (q,0),true)
  | ⟨.inr (.inr true),.before⟩ => (.inr (),false)
  | ⟨.inr (.inr true),.after⟩ => (.inl (q,1),true)
  | ⟨.inr (.inr true),.branch⟩ => (.inl (q,2),false)

def bandCutAttachFrom : BandCutSeam S × Bool → LocalPort (BandCutVertex V S q) (A.bandCutKind q)
  | (.inr (),e) => A.bandCutSplitPort q (!e) .before
  | (.inl (s,k),e) =>
    if k=0 then
      if e then A.bandCutInteriorPort q s false false
      else ⟨.inl (A.attach.symm (s,false)).1,(A.attach.symm (s,false)).2⟩
    else if k=1 then
      if e then A.bandCutInteriorPort q s true false
      else A.bandCutInteriorPort q s false true
    else
      if e then ⟨.inl (A.attach.symm (s,true)).1,(A.attach.symm (s,true)).2⟩
      else A.bandCutInteriorPort q s true true

/-- The two sides of the inverse band belong to the SAME original parent surface. All child occurrences, including repeated old facets, remain literal. -/
def bandCutFacet : Side (BandCutSeam S) (bandCutArity arity) → F
  | ⟨.inl (s,_),c⟩ => A.facet ⟨s,c⟩
  | ⟨.inr (),_⟩ => A.facet ⟨q,none⟩
end IntegralCharacterVarieties.OccurrenceIncidence.PortAssembly

namespace IntegralCharacterVarieties.OccurrenceIncidence.PortAssembly
open scoped Classical
open VertexTable
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)

lemma bandCutAttach_interior (s : S) (b p : Bool) :
    A.bandCutAttachTo q (A.bandCutInteriorPort q s b p)=
      (.inl (s,if b then (if p then 2 else 1) else (if p then 1 else 0)),!p) := by
  by_cases h : s=q
  · subst s
    rw [bandCutInteriorPort,dite_eq_left rfl]
    cases b <;> cases p <;> simp! [bandCutAttachTo,bandCutSplitPort]
  · rw [bandCutInteriorPort,dite_eq_right h]
    cases b <;> cases p <;> simp! [bandCutAttachTo,bandCutSplitPort]

lemma bandCutAttach_outer (v : V) (p : (A.kind v).table.Port) :
    A.bandCutAttachTo q ⟨.inl v,p⟩=(.inl ((A.attach ⟨v,p⟩).1,
      if (A.attach ⟨v,p⟩).2 then 2 else 0),(A.attach ⟨v,p⟩).2) := rfl

lemma bandCutAttach_left : Function.LeftInverse (A.bandCutAttachFrom q) (A.bandCutAttachTo q) := by
  rintro ⟨v,p⟩
  rcases v with v|⟨⟨s,b⟩|b⟩
  · change A.bandCutAttachFrom q (.inl ((A.attach ⟨v,p⟩).1,
      if (A.attach ⟨v,p⟩).2 then 2 else 0),(A.attach ⟨v,p⟩).2)=_
    let f : LocalPort V A.kind → LocalPort (BandCutVertex V S q) (A.bandCutKind q) :=
      fun u => ⟨.inl u.1,u.2⟩
    have h := congrArg f (A.attach.symm_apply_apply ⟨v,p⟩)
    cases he : (A.attach ⟨v,p⟩).2
    · change f (A.attach.symm ((A.attach ⟨v,p⟩).1,false))=f ⟨v,p⟩
      rw [show ((A.attach ⟨v,p⟩).1,false)=A.attach ⟨v,p⟩ from Prod.ext rfl he.symm]
      exact h
    · change f (A.attach.symm ((A.attach ⟨v,p⟩).1,true))=f ⟨v,p⟩
      rw [show ((A.attach ⟨v,p⟩).1,true)=A.attach ⟨v,p⟩ from Prod.ext rfl he.symm]
      exact h

  · obtain ⟨s,hs⟩ := s
    cases b <;> cases p <;>
      simp! [bandCutAttachTo,bandCutAttachFrom,bandCutInteriorPort,hs]
  · cases b <;> cases p <;>
      simp [bandCutAttachTo,bandCutAttachFrom,bandCutInteriorPort,bandCutSplitPort]

lemma bandCutAttach_right : Function.RightInverse (A.bandCutAttachFrom q) (A.bandCutAttachTo q) := by
  rintro ⟨s,e⟩
  rcases s with ⟨s,k⟩|u
  · rcases (show k=0 ∨ k=1 ∨ k=2 by fin_cases k <;> decide) with rfl|rfl|rfl <;>
      cases e <;> simp [bandCutAttachFrom,bandCutAttach_interior,bandCutAttach_outer]

  · cases u
    cases e <;> rfl

def bandCutAttach : LocalPort (BandCutVertex V S q) (A.bandCutKind q) ≃ BandCutSeam S × Bool where
  toFun := A.bandCutAttachTo q
  invFun := A.bandCutAttachFrom q
  left_inv := A.bandCutAttach_left q
  right_inv := A.bandCutAttach_right q

end IntegralCharacterVarieties.OccurrenceIncidence.PortAssembly

namespace IntegralCharacterVarieties.OccurrenceIncidence.PortAssembly
open scoped Classical
open VertexTable
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)

lemma bandCutEndpoint (p : LocalPort (BandCutVertex V S q) (A.bandCutKind q)) :
    (A.bandCutAttach q p).2=(A.bandCutKind q p.1).table.endpoint p.2 := by
  obtain ⟨v,p⟩ := p
  rcases v with v|⟨⟨s,b⟩|b⟩
  · exact A.endpoint ⟨v,p⟩
  · cases b <;> cases p <;> rfl
  · cases b <;> cases p <;> rfl

lemma bandCutCount (p : LocalPort (BandCutVertex V S q) (A.bandCutKind q)) :
    bandCutArity arity (A.bandCutAttach q p).1=(A.bandCutKind q p.1).arity p.2 := by
  obtain ⟨v,p⟩ := p
  rcases v with v|⟨⟨s,b⟩|b⟩
  · exact A.count ⟨v,p⟩
  · cases b <;> cases p <;> rfl
  · cases b <;> cases p <;>
      simp [bandCutAttach,bandCutAttachTo,bandCutArity,bandCutKind,Kind.arity]

@[simp] lemma bandCut_fin_transport {n m : ℕ} (h : n=m) (i : Fin n) :
    ((h ▸ i : Fin m)).val=i.val := by subst m; rfl

abbrev bandCutPorts : PortAssembly F (BandCutSeam S) (BandCutVertex V S q) (bandCutArity arity) where
  kind := A.bandCutKind q
  attach := A.bandCutAttach q
  endpoint := A.bandCutEndpoint q
  count := A.bandCutCount q
  facet := A.bandCutFacet q
  facetContinuation := by
    rintro ⟨v,p,c⟩
    rcases v with v|⟨⟨s,b⟩|b⟩
    · exact A.facetContinuation ⟨v,p,c⟩
    · cases b <;> cases p <;> cases c <;> rfl
    · cases b <;> cases p with
      | before =>
        cases c with
        | none => rfl
        | some c =>
          rcases c with a|j|a
          · exact a.elim0
          · rfl
          · exact a.elim0
      | after =>
        cases c with
        | none => rfl
        | some c =>
          rcases c with a|j|a
          · exact a.elim0
          · apply congrArg (fun j : Fin (arity q) => A.facet ⟨q,some j⟩)
            apply Fin.ext
            simp only [bandCut_fin_transport]
            change j.val = 0+j.val
            omega
          · exact a.elim0
      | branch =>
        cases c with
        | none => rfl
        | some j =>
          apply congrArg (fun j : Fin (arity q) => A.facet ⟨q,some j⟩)
          apply Fin.ext
          simp only [bandCut_fin_transport]
          change 0+j.val = j.val
          omega


/-- Required inverse arc incidence, with no scattering of an old port and no lost old endpoint or repeated child occurrence. -/
theorem inverse_band_port_assembly : ∃ B : PortAssembly F (BandCutSeam S) (BandCutVertex V S q) (bandCutArity arity),
    B.kind=A.bandCutKind q ∧ B.facet=A.bandCutFacet q ∧
      (∀ (v : V) (p : (A.kind v).table.Port),
        ∃ u : LocalPort (BandCutVertex V S q) B.kind,
          u.1=.inl v ∧ B.attach u=A.bandCutAttachTo q ⟨.inl v,p⟩) := by
  refine ⟨A.bandCutPorts q,rfl,rfl,?_⟩
  intro v p
  exact ⟨⟨.inl v,p⟩,rfl,rfl⟩
end IntegralCharacterVarieties.OccurrenceIncidence.PortAssembly

namespace IntegralCharacterVarieties.OccurrenceIncidence.PortAssembly
open scoped Classical
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)

/-- The oriented old boundary traverses three pieces. Only the middle parent piece at q is replaced by the child side of the inverse band. -/
def bandCutLong : Side S arity × Fin 3 → Side (BandCutSeam S) (bandCutArity arity)
  | (⟨s,none⟩,k) => if s=q ∧ k=1 then ⟨.inr (),some (0 : Fin 1)⟩ else ⟨.inl (s,k),none⟩
  | (⟨s,some c⟩,k) => ⟨.inl (s,k.rev),some c⟩

def bandCutShort (k : Fin 2) : Side (BandCutSeam S) (bandCutArity arity) :=
  if k=0 then ⟨.inl (q,1),none⟩ else ⟨.inr (),none⟩

def bandCutSideFrom : Side (BandCutSeam S) (bandCutArity arity) → (Side S arity × Fin 3) ⊕ Fin 2
  | ⟨.inl (s,k),none⟩ => if s=q ∧ k=1 then .inr 0 else .inl (⟨s,none⟩,k)
  | ⟨.inl (s,k),some c⟩ => .inl (⟨s,some c⟩,k.rev)
  | ⟨.inr (),none⟩ => .inr 1
  | ⟨.inr (),some _⟩ => .inl (⟨q,none⟩,1)

/-- Exhaustive side occurrence bijection. The new short boundary is additional, rather than a chosen list that might omit fresh-parent germs. -/
def bandCutSideEquiv : ((Side S arity × Fin 3) ⊕ Fin 2) ≃ Side (BandCutSeam S) (bandCutArity arity) where
  toFun := Sum.elim (bandCutLong q) (bandCutShort q)
  invFun := bandCutSideFrom q
  left_inv := by
    intro x
    rcases x with ⟨⟨s,c⟩,k⟩|k
    · cases c with
      | none =>
        by_cases h : s=q ∧ k=1
        · rcases h with ⟨rfl,rfl⟩
          simp [bandCutLong,bandCutSideFrom]
        · simp [bandCutLong,bandCutSideFrom,h]
      | some c => simp [bandCutLong,bandCutSideFrom]
    · rcases (show k=0 ∨ k=1 by fin_cases k <;> decide) with rfl|rfl <;>
        simp [bandCutShort,bandCutSideFrom]
  right_inv := by
    rintro ⟨s,c⟩
    rcases s with ⟨s,k⟩|u
    · cases c with
      | none =>
        by_cases h : s=q ∧ k=1
        · rcases h with ⟨rfl,rfl⟩
          simp [bandCutSideFrom,bandCutShort]
        · simp [bandCutSideFrom,bandCutLong,h]
      | some c => simp [bandCutSideFrom,bandCutLong]
    · cases u
      cases c with
      | none => simp [bandCutSideFrom,bandCutShort]
      | some c =>
        have h : c=(0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
        subst c
        simp [bandCutSideFrom,bandCutLong]

lemma bandCutLong_facet (a : Side S arity) (k : Fin 3) :
    A.bandCutFacet q (bandCutLong q (a,k))=A.facet a := by
  rcases a with ⟨s,c⟩
  cases c with
  | none =>
    by_cases h : s=q ∧ k=1
    · rcases h with ⟨rfl,rfl⟩
      simp [bandCutLong,bandCutFacet]
    · simp [bandCutLong,h,bandCutFacet]
  | some c => rfl

lemma bandCutShort_facet (k : Fin 2) :
    A.bandCutFacet q (bandCutShort q k)=A.facet ⟨q,none⟩ := by
  unfold bandCutShort
  split <;> rfl
end IntegralCharacterVarieties.OccurrenceIncidence.PortAssembly

namespace IntegralCharacterVarieties.OccurrenceIncidence.PortAssembly
open scoped Classical
open VertexTable
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)

def bandCutBeforeEnd : Bool → Option Unit → LocalEnd (BandCutVertex V S q) (A.bandCutKind q)
  | false,c => ⟨.inr (.inr false),.before,c.map (fun _ => .inr (.inl ()))⟩
  | true,c => ⟨.inr (.inr true),.before,c.map (fun _ => .inr (.inl ()))⟩
def bandCutAfterEnd : Bool → Option (Fin (arity q)) → LocalEnd (BandCutVertex V S q) (A.bandCutKind q)
  | false,c => ⟨.inr (.inr false),.after,c.map (fun j => .inr (.inl j))⟩
  | true,c => ⟨.inr (.inr true),.after,c.map (fun j => .inr (.inl j))⟩
def bandCutBranchEnd : Bool → Option (Fin (arity q)) → LocalEnd (BandCutVertex V S q) (A.bandCutKind q)
  | false,c => ⟨.inr (.inr false),.branch,c⟩
  | true,c => ⟨.inr (.inr true),.branch,c⟩

lemma bandCut_realize_old (x : LocalEnd V A.kind) :
    (A.bandCutPorts q).realize ⟨.inl x.1,x.2⟩=
      (⟨.inl ((A.realize x).1.1,if (A.realize x).2 then 2 else 0),(A.realize x).1.2⟩,(A.realize x).2) := rfl

lemma bandCut_realize_continuation (s : {s : S // s ≠ q}) (b p : Bool) (c : Option (Fin (arity s))) :
    (A.bandCutPorts q).realize ⟨.inr (.inl (s,b)),p,c⟩=
      (⟨.inl (s,if b then (if p then 2 else 1) else (if p then 1 else 0)),c⟩,!p) := by
  cases b <;> cases p <;> cases c <;> rfl

lemma bandCut_realize_before (b : Bool) (c : Option Unit) :
    (A.bandCutPorts q).realize (A.bandCutBeforeEnd q b c)=
      (⟨.inr (),c.map (fun _ => (0 : Fin 1))⟩,!b) := by
  cases b <;> cases c with
  | none => rfl
  | some c =>
    rw [realize_apply]
    dsimp only [bandCutBeforeEnd,bandCutAfterEnd,Option.map_some]
    apply Prod.ext
    rotate_left
    · rfl
    · refine Sigma.ext (by rfl) ?_
      apply heq_of_eq
      apply congrArg some
      exact Subsingleton.elim (α:=Fin 1) _ _

lemma bandCut_realize_after (b : Bool) (c : Option (Fin (arity q))) :
    (A.bandCutPorts q).realize (A.bandCutAfterEnd q b c)=
      (⟨.inl (q,1),c⟩,b) := by
  cases b <;> cases c with
  | none => rfl
  | some c =>
    rw [realize_apply]
    dsimp only [bandCutBeforeEnd,bandCutAfterEnd,Option.map_some]
    apply Prod.ext
    rotate_left
    · rfl
    · refine Sigma.ext (by rfl) ?_
      apply heq_of_eq
      apply congrArg some
      apply Fin.ext
      simp only [childEquiv]
      change 0+c.val=c.val
      omega

lemma bandCut_realize_branch (b : Bool) (c : Option (Fin (arity q))) :
    (A.bandCutPorts q).realize (A.bandCutBranchEnd q b c)=
      (⟨.inl (q,if b then 2 else 0),c⟩,!b) := by
  cases b <;> cases c <;> rfl

lemma bandCut_mate_realize (x : LocalEnd (BandCutVertex V S q) (A.bandCutKind q)) :
    (A.bandCutPorts q).vertexAssembly.corners.mate ((A.bandCutPorts q).realize x)=
      (A.bandCutPorts q).realize (localMate x) := by
  change (A.bandCutPorts q).realize
    (localMate ((A.bandCutPorts q).realize.symm ((A.bandCutPorts q).realize x)))=_
  rw [Equiv.symm_apply_apply]

lemma bandCut_mate_middle (b : Bool) (c : Option (Fin (arity q))) :
    (A.bandCutPorts q).vertexAssembly.corners.mate (⟨.inl (q,1),c⟩,b)=
      match c with
      | none => (⟨.inr (),none⟩,!b)
      | some j => (⟨.inl (q,if b then 2 else 0),some j⟩,!b) := by
  rw [← A.bandCut_realize_after q b c,A.bandCut_mate_realize]
  cases c with
  | none =>
    have h : localMate (A.bandCutAfterEnd q b none)=A.bandCutBeforeEnd q b none := by cases b <;> rfl
    rw [h,A.bandCut_realize_before]
    rfl
  | some j =>
    have h : localMate (A.bandCutAfterEnd q b (some j))=A.bandCutBranchEnd q b (some j) := by cases b <;> rfl
    rw [h,A.bandCut_realize_branch]

lemma bandCut_mate_outer_piece (b : Bool) (c : Option (Fin (arity q))) :
    (A.bandCutPorts q).vertexAssembly.corners.mate (⟨.inl (q,if b then 2 else 0),c⟩,!b)=
      match c with
      | none => (⟨.inr (),some (0 : Fin 1)⟩,!b)
      | some j => (⟨.inl (q,1),some j⟩,b) := by
  rw [← A.bandCut_realize_branch q b c,A.bandCut_mate_realize]
  cases c with
  | none =>
    have h : localMate (A.bandCutBranchEnd q b none)=A.bandCutBeforeEnd q b (some ()) := by cases b <;> rfl
    rw [h,A.bandCut_realize_before]
    rfl
  | some j =>
    have h : localMate (A.bandCutBranchEnd q b (some j))=A.bandCutAfterEnd q b (some j) := by cases b <;> rfl
    rw [h,A.bandCut_realize_after]

lemma bandCut_mate_band (b : Bool) (c : Option (Fin 1)) :
    (A.bandCutPorts q).vertexAssembly.corners.mate (⟨.inr (),c⟩,!b)=
      match c with
      | none => (⟨.inl (q,1),none⟩,b)
      | some _ => (⟨.inl (q,if b then 2 else 0),none⟩,!b) := by
  cases c with
  | none =>
    have he := A.bandCut_realize_before q b none
    simp only [Option.map_none] at he
    rw [← he,A.bandCut_mate_realize]
    have h : localMate (A.bandCutBeforeEnd q b none)=A.bandCutAfterEnd q b none := by cases b <;> rfl
    rw [h,A.bandCut_realize_after]
  | some j =>
    have hj : j=(0:Fin 1) := Subsingleton.elim (α:=Fin 1) _ _
    subst j
    have he := A.bandCut_realize_before q b (some ())
    simp only [Option.map_some] at he
    rw [← he,A.bandCut_mate_realize]
    have h : localMate (A.bandCutBeforeEnd q b (some ()))=A.bandCutBranchEnd q b none := by cases b <;> rfl
    rw [h,A.bandCut_realize_branch]
end IntegralCharacterVarieties.OccurrenceIncidence.PortAssembly

namespace IntegralCharacterVarieties.OccurrenceIncidence.PortAssembly
open scoped Classical
open VertexTable
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)

def bandCutOuter (g : Germ S arity) : Germ (BandCutSeam S) (bandCutArity arity) :=
  (⟨.inl (g.1.1,if g.2 then 2 else 0),g.1.2⟩,g.2)

lemma bandCut_mate_outer (g : Germ S arity) :
    (A.bandCutPorts q).vertexAssembly.corners.mate (bandCutOuter g)=
      bandCutOuter (A.vertexAssembly.corners.mate g) := by
  have hh := A.bandCut_mate_realize q ⟨.inl (A.realize.symm g).1,(A.realize.symm g).2⟩
  change (A.bandCutPorts q).vertexAssembly.corners.mate
    (bandCutOuter (A.realize (A.realize.symm g)))=
      bandCutOuter (A.realize (localMate (A.realize.symm g))) at hh
  rw [A.realize.apply_symm_apply] at hh
  exact hh

lemma bandCut_mate_continuation (s : {s : S // s ≠ q}) (b : Bool) (c : Option (Fin (arity s))) :
    (A.bandCutPorts q).vertexAssembly.corners.mate
      (⟨.inl (s,if b then 1 else 0),c⟩,true)=
        (⟨.inl (s,if b then 2 else 1),c⟩,false) := by
  have hh := A.bandCut_mate_realize q ⟨.inr (.inl (s,b)),false,c⟩
  have hm : localMate (⟨.inr (.inl (s,b)),false,c⟩ : LocalEnd _ (A.bandCutKind q))=
      ⟨.inr (.inl (s,b)),true,c⟩ := by cases b <;> cases c <;> rfl
  rw [hm,A.bandCut_realize_continuation,A.bandCut_realize_continuation] at hh
  simpa using hh

lemma bandCut_mate_continuation_back (s : {s : S // s ≠ q}) (b : Bool) (c : Option (Fin (arity s))) :
    (A.bandCutPorts q).vertexAssembly.corners.mate
      (⟨.inl (s,if b then 2 else 1),c⟩,false)=
        (⟨.inl (s,if b then 1 else 0),c⟩,true) := by
  have hh := congrArg (A.bandCutPorts q).vertexAssembly.corners.mate
    (A.bandCut_mate_continuation q s b c)
  rw [(A.bandCutPorts q).vertexAssembly.corners.involutive] at hh
  exact hh.symm

lemma bandCutLong_start (a : Side S arity) :
    start (bandCutLong q (a,0))=bandCutOuter (start a) := by
  rcases a with ⟨s,c⟩
  cases c <;> simp [bandCutLong,start,positive,bandCutOuter]
  rw [ite_eq_right (by intro h; exact (by decide : (0:Fin 3) ≠ 1) h.2)]

lemma bandCutLong_finish (a : Side S arity) :
    finish (bandCutLong q (a,2))=bandCutOuter (finish a) := by
  rcases a with ⟨s,c⟩
  cases c <;> simp [bandCutLong,finish,positive,bandCutOuter]
  rw [ite_eq_right (by intro h; exact (by decide : (2:Fin 3) ≠ 1) h.2)]

lemma bandCut_next_last (a : Side S arity) :
    (A.bandCutPorts q).vertexAssembly.corners.boundaryNext (bandCutLong q (a,2))=
      bandCutLong q (A.vertexAssembly.corners.boundaryNext a,0) := by
  change ((A.bandCutPorts q).vertexAssembly.corners.mate (finish _)).1=_
  rw [bandCutLong_finish,bandCut_mate_outer,A.vertexAssembly.corners.mate_finish,
    ← bandCutLong_start]
  rfl

lemma bandCut_next_first (a : Side S arity) :
    (A.bandCutPorts q).vertexAssembly.corners.boundaryNext (bandCutLong q (a,0))=
      bandCutLong q (a,1) := by
  rcases a with ⟨s,c⟩
  by_cases hs : s=q
  · subst s
    cases c with
    | none =>
      simpa [Corners.boundaryNext,bandCutLong,finish,positive] using
        congrArg Prod.fst (A.bandCut_mate_outer_piece q false none)
    | some j =>
      simpa [Corners.boundaryNext,bandCutLong,finish,positive] using
        congrArg Prod.fst (A.bandCut_mate_outer_piece q true (some j))
  · cases c with
    | none =>
      simpa [Corners.boundaryNext,bandCutLong,finish,positive,hs] using
        congrArg Prod.fst (A.bandCut_mate_continuation q ⟨s,hs⟩ false none)
    | some j =>
      simpa [Corners.boundaryNext,bandCutLong,finish,positive,hs] using
        congrArg Prod.fst (A.bandCut_mate_continuation_back q ⟨s,hs⟩ true (some j))

lemma bandCut_next_second (a : Side S arity) :
    (A.bandCutPorts q).vertexAssembly.corners.boundaryNext (bandCutLong q (a,1))=
      bandCutLong q (a,2) := by
  rcases a with ⟨s,c⟩
  by_cases hs : s=q
  · subst s
    cases c with
    | none =>
      simpa [Corners.boundaryNext,bandCutLong,finish,positive] using
        congrArg Prod.fst (A.bandCut_mate_band q true (some 0))
    | some j =>
      simpa [Corners.boundaryNext,bandCutLong,finish,positive] using
        congrArg Prod.fst (A.bandCut_mate_middle q false (some j))
  · cases c with
    | none =>
      simpa [Corners.boundaryNext,bandCutLong,finish,positive,hs] using
        congrArg Prod.fst (A.bandCut_mate_continuation q ⟨s,hs⟩ true none)
    | some j =>
      simpa [Corners.boundaryNext,bandCutLong,finish,positive,hs] using
        congrArg Prod.fst (A.bandCut_mate_continuation_back q ⟨s,hs⟩ false (some j))

lemma bandCut_next_short (k : Fin 2) :
    (A.bandCutPorts q).vertexAssembly.corners.boundaryNext (bandCutShort q k)=
      bandCutShort q ⟨(k.val+1)%2, Nat.mod_lt _ (by decide)⟩ := by
  rcases (show k=0 ∨ k=1 by fin_cases k <;> decide) with rfl|rfl
  · simpa [Corners.boundaryNext,bandCutShort,finish,positive] using
      congrArg Prod.fst (A.bandCut_mate_middle q true none)
  · simpa [Corners.boundaryNext,bandCutShort,finish,positive] using
      congrArg Prod.fst (A.bandCut_mate_band q false none)
end IntegralCharacterVarieties.OccurrenceIncidence.PortAssembly

end

end OAI
