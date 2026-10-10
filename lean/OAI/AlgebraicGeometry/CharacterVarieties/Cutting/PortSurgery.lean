import OAI.AlgebraicGeometry.CharacterVarieties.Cutting.DoubledStrips

namespace OAI

/-!
# Whole-port rewiring and its induced boundary permutation.

This formalizes the band reconstruction for filtered surface local systems in
*Integral points on character varieties of curves*.
-/

namespace IntegralCharacterVarieties.OccurrenceIncidence.PortAssembly
open scoped Classical
open VertexTable
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity)

/-- The old assembly's actual whole-port wiring, not an abstract end matching. -/
def toWiring : PortWiring A.kind where
  wire := (A.portAt true).symm.trans (A.portAt false)
  arity p := by
    obtain ⟨s,rfl⟩ := (A.portAt true).surjective p
    change (A.kind ((A.portAt false) ((A.portAt true).symm (A.portAt true s))).val.1).arity
      ((A.portAt false) ((A.portAt true).symm (A.portAt true s))).val.2=_
    simp only [Equiv.symm_apply_apply,A.portAt_arity]

lemma toWiring_endOf (p : LocalPort V A.kind) :
    (A.toWiring.endOf p).1=A.portAt true (A.attach p).1 := by
  cases he : (A.kind p.1).table.endpoint p.2 with
  | false =>
    have h := A.toWiring.endOf_negative ⟨p,he⟩
    rw [h]
    change (A.portAt true) ((A.portAt false).symm ⟨p,he⟩)=_
    rfl
  | true =>
    have h := A.toWiring.endOf_positive ⟨p,he⟩
    rw [h]
    exact (A.portAt true).apply_symm_apply ⟨p,he⟩ |>.symm

noncomputable def wiringSides : Side S arity ≃ Side A.toWiring.Seam A.toWiring.seamArity :=
  Equiv.sigmaCongr (A.portAt true) (fun s => Equiv.optionCongr (finCongr (A.portAt_arity s true).symm))

lemma wiringSides_number (a : Side S arity) :
    sideNumber (A.wiringSides a)=(A.portAt true a.1,a.2.map Fin.val) := by
  rcases a with ⟨s,c⟩
  cases c <;> rfl

lemma realize_number (x : LocalEnd V A.kind) :
    sideNumber (A.realize x).1=((A.attach ⟨x.1,x.2.1⟩).1,
      x.2.2.map (fun j => ((A.kind x.1).childEnumeration x.2.1 j).val)) := by
  rw [A.realize_apply]
  unfold sideNumber childEquiv
  cases x.2.2 <;> rfl

lemma toWiring_sideOf (x : LocalEnd V A.kind) :
    A.toWiring.sideOf x=A.wiringSides (A.realize x).1 := by
  apply sideNumber_injective
  refine (A.toWiring.sideOf_number x).trans ?_
  rw [A.toWiring_endOf,A.wiringSides_number]
  exact congrArg (fun z : S × Option ℕ => (A.portAt true z.1,z.2)) (A.realize_number x).symm

lemma boundaryNext_local (x : LocalEnd V A.kind)
    (hx : (A.kind x.1).table.endpoint x.2.1=x.2.2.isNone) :
    A.vertexAssembly.corners.boundaryNext (A.realize x).1=(A.realize (localMate x)).1 := by
  have he : A.realize x=finish (A.realize x).1 := by
    apply Prod.ext
    · rfl
    exact (A.realize_endpoint x).trans (hx.trans (A.realize_parent x).symm)
  change (A.realize (localMate (A.realize.symm (finish (A.realize x).1)))).1=_
  rw [←he,Equiv.symm_apply_apply]

lemma toWiring_boundary (a : Side S arity) :
    (A.toWiring.assemble (fun _ => ()) (fun _=>rfl)).vertexAssembly.corners.boundaryNext
      (A.wiringSides a)=A.wiringSides (A.vertexAssembly.corners.boundaryNext a) := by
  obtain ⟨x,hx,hxs⟩ := A.toWiring.oriented_side_exists (A.wiringSides a)
  have ha : (A.realize x).1=a := A.wiringSides.injective ((A.toWiring_sideOf x).symm.trans hxs)
  rw [←ha,←A.toWiring_sideOf x,A.toWiring.boundaryNext_local _ _ x hx,
    A.boundaryNext_local x hx,A.toWiring_sideOf]

end IntegralCharacterVarieties.OccurrenceIncidence.PortAssembly
namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable
namespace PortWiring
variable {V U : Type} {k : V → Kind} {l : U → Kind}
    (W : PortWiring k) (Z : PortWiring l)

/-- Disjoint whole-port union, before the three-port inverse-band surgery. -/
def sum : PortWiring (sumKind k l) where
  wire := (sumPortAt k l true).symm |>.trans (Equiv.sumCongr W.wire Z.wire) |>.trans (sumPortAt k l false)
  arity p := by
    obtain ⟨p,rfl⟩ := (sumPortAt k l true).surjective p
    have he : (((sumPortAt k l true).symm.trans (Equiv.sumCongr W.wire Z.wire)).trans
        (sumPortAt k l false)) (sumPortAt k l true p)=
        sumPortAt k l false ((Equiv.sumCongr W.wire Z.wire) p) := by simp
    refine (congrArg (fun p : PortAt (sumKind k l) false =>
      (sumKind k l p.val.1).arity p.val.2) he).trans ?_
    rcases p with p|p
    · exact W.arity p
    · exact Z.arity p

@[simp] lemma sum_wire_left (p : PortAt k true) :
    (W.sum Z).wire (sumPortAt k l true (.inl p))=sumPortAt k l false (.inl (W.wire p)) := by
  change (sumPortAt k l false) ((Equiv.sumCongr W.wire Z.wire) ((sumPortAt k l true).symm ((sumPortAt k l true) (.inl p))))=_
  rw [Equiv.symm_apply_apply]
  rfl
@[simp] lemma sum_wire_right (p : PortAt l true) :
    (W.sum Z).wire (sumPortAt k l true (.inr p))=sumPortAt k l false (.inr (Z.wire p)) := by
  change (sumPortAt k l false) ((Equiv.sumCongr W.wire Z.wire) ((sumPortAt k l true).symm ((sumPortAt k l true) (.inr p))))=_
  rw [Equiv.symm_apply_apply]
  rfl

/-- This equivalence retains each individual ordered child occurrence. -/
def sumSides : Side W.Seam W.seamArity ⊕ Side Z.Seam Z.seamArity ≃
    Side (W.sum Z).Seam (W.sum Z).seamArity where
  toFun s := match s with
    | .inl ⟨⟨⟨v,p⟩,hp⟩,c⟩ => ⟨⟨⟨.inl v,p⟩,hp⟩,c⟩
    | .inr ⟨⟨⟨u,p⟩,hp⟩,c⟩ => ⟨⟨⟨.inr u,p⟩,hp⟩,c⟩
  invFun s := match s with
    | ⟨⟨⟨.inl v,p⟩,hp⟩,c⟩ => .inl ⟨⟨⟨v,p⟩,hp⟩,c⟩
    | ⟨⟨⟨.inr u,p⟩,hp⟩,c⟩ => .inr ⟨⟨⟨u,p⟩,hp⟩,c⟩
  left_inv s := by rcases s with ⟨⟨⟨v,p⟩,hp⟩,c⟩|⟨⟨⟨u,p⟩,hp⟩,c⟩ <;> rfl
  right_inv s := by rcases s with ⟨⟨⟨v|u,p⟩,hp⟩,c⟩ <;> rfl

def leftEnd (x : LocalEnd V k) : LocalEnd (V ⊕ U) (sumKind k l) := ⟨.inl x.1,x.2⟩
def rightEnd (x : LocalEnd U l) : LocalEnd (V ⊕ U) (sumKind k l) := ⟨.inr x.1,x.2⟩

lemma sum_endOf_left (p : LocalPort V k) :
    ((W.sum Z).endOf ⟨.inl p.1,p.2⟩).1=sumPortAt k l true (.inl (W.endOf p).1) := by
  by_cases hp : (k p.1).table.endpoint p.2=true
  · have ha := (W.sum Z).endOf_positive (sumPortAt k l true (.inl ⟨p,hp⟩))
    have hb := W.endOf_positive ⟨p,hp⟩
    change (W.sum Z).endOf ⟨.inl p.1,p.2⟩=_ at ha
    rw [ha,hb]
  · have hn := Bool.eq_false_iff.mpr hp
    have ha := (W.sum Z).endOf_negative (sumPortAt k l false (.inl ⟨p,hn⟩))
    have hb := W.endOf_negative ⟨p,hn⟩
    change (W.sum Z).endOf ⟨.inl p.1,p.2⟩=_ at ha
    rw [ha,hb]
    apply (W.sum Z).wire.injective
    rw [Equiv.apply_symm_apply,W.sum_wire_left,Equiv.apply_symm_apply]

lemma sum_endOf_right (p : LocalPort U l) :
    ((W.sum Z).endOf ⟨.inr p.1,p.2⟩).1=sumPortAt k l true (.inr (Z.endOf p).1) := by
  by_cases hp : (l p.1).table.endpoint p.2=true
  · have ha := (W.sum Z).endOf_positive (sumPortAt k l true (.inr ⟨p,hp⟩))
    have hb := Z.endOf_positive ⟨p,hp⟩
    change (W.sum Z).endOf ⟨.inr p.1,p.2⟩=_ at ha
    rw [ha,hb]
  · have hn := Bool.eq_false_iff.mpr hp
    have ha := (W.sum Z).endOf_negative (sumPortAt k l false (.inr ⟨p,hn⟩))
    have hb := Z.endOf_negative ⟨p,hn⟩
    change (W.sum Z).endOf ⟨.inr p.1,p.2⟩=_ at ha
    rw [ha,hb]
    apply (W.sum Z).wire.injective
    rw [Equiv.apply_symm_apply,W.sum_wire_right,Equiv.apply_symm_apply]

lemma sumSides_number_left (s : Side W.Seam W.seamArity) :
    sideNumber (W.sumSides Z (.inl s))=(sumPortAt k l true (.inl s.1),s.2.map Fin.val) := by
  rcases s with ⟨⟨⟨v,p⟩,hp⟩,c⟩
  cases c <;> rfl
lemma sumSides_number_right (s : Side Z.Seam Z.seamArity) :
    sideNumber (W.sumSides Z (.inr s))=(sumPortAt k l true (.inr s.1),s.2.map Fin.val) := by
  rcases s with ⟨⟨⟨v,p⟩,hp⟩,c⟩
  cases c <;> rfl

lemma sum_sideOf_left (x : LocalEnd V k) :
    (W.sum Z).sideOf (leftEnd (l:=l) x)=W.sumSides Z (.inl (W.sideOf x)) := by
  apply sideNumber_injective
  refine ((W.sum Z).sideOf_number _).trans ?_
  change (((W.sum Z).endOf ⟨.inl x.1,x.2.1⟩).1,
    x.2.2.map (fun j => ((k x.1).childEnumeration x.2.1 j).val))=_
  rw [W.sum_endOf_left Z ⟨x.1,x.2.1⟩,W.sumSides_number_left]
  exact congrArg (fun z : W.Seam × Option ℕ => (sumPortAt k l true (.inl z.1),z.2)) (W.sideOf_number x).symm

lemma sum_sideOf_right (x : LocalEnd U l) :
    (W.sum Z).sideOf (rightEnd (k:=k) x)=W.sumSides Z (.inr (Z.sideOf x)) := by
  apply sideNumber_injective
  refine ((W.sum Z).sideOf_number _).trans ?_
  change (((W.sum Z).endOf ⟨.inr x.1,x.2.1⟩).1,
    x.2.2.map (fun j => ((l x.1).childEnumeration x.2.1 j).val))=_
  rw [W.sum_endOf_right Z ⟨x.1,x.2.1⟩,W.sumSides_number_right]
  exact congrArg (fun z : Z.Seam × Option ℕ => (sumPortAt k l true (.inr z.1),z.2)) (Z.sideOf_number x).symm

lemma sum_boundary_left (a : Side W.Seam W.seamArity) :
    ((W.sum Z).assemble (fun _ => ()) (fun _=>rfl)).vertexAssembly.corners.boundaryNext
      (W.sumSides Z (.inl a)) =
    W.sumSides Z (.inl ((W.assemble (fun _ => ()) (fun _=>rfl)).vertexAssembly.corners.boundaryNext a)) := by
  obtain ⟨x,hx,rfl⟩ := W.oriented_side_exists a
  rw [←W.sum_sideOf_left Z x,(W.sum Z).boundaryNext_local _ _ (leftEnd (l:=l) x) hx,
    W.boundaryNext_local _ _ x hx]
  exact W.sum_sideOf_left Z (localMate x)

lemma sum_boundary_right (a : Side Z.Seam Z.seamArity) :
    ((W.sum Z).assemble (fun _ => ()) (fun _=>rfl)).vertexAssembly.corners.boundaryNext
      (W.sumSides Z (.inr a)) =
    W.sumSides Z (.inr ((Z.assemble (fun _ => ()) (fun _=>rfl)).vertexAssembly.corners.boundaryNext a)) := by
  obtain ⟨x,hx,rfl⟩ := Z.oriented_side_exists a
  rw [←W.sum_sideOf_right Z x,(W.sum Z).boundaryNext_local _ _ (rightEnd (k:=k) x) hx,
    Z.boundaryNext_local _ _ x hx]
  exact W.sum_sideOf_right Z (localMate x)

end PortWiring
end IntegralCharacterVarieties.OccurrenceIncidence
namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable
namespace PortWiring
variable {V : Type} {kind : V → Kind} (W : PortWiring kind)

/-- Rewire WHOLE ports of the same ordered arity, never individual children. -/
def rewire (C : Equiv.Perm W.Seam) (hC : ∀ s,W.seamArity (C s)=W.seamArity s) : PortWiring kind where
  wire := C.trans W.wire
  arity s := (W.arity (C s)).trans (hC s)

lemma inverse_arity (C : Equiv.Perm W.Seam) (hC : ∀ s,W.seamArity (C s)=W.seamArity s) :
    ∀ s,W.seamArity (C.symm s)=W.seamArity s := by
  intro s
  have h := hC (C.symm s)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

def mapSides (C : Equiv.Perm W.Seam) (hC : ∀ s,W.seamArity (C s)=W.seamArity s) :
    Equiv.Perm (Side W.Seam W.seamArity) :=
  Equiv.sigmaCongr C (fun s => Equiv.optionCongr (finCongr (hC s).symm))

lemma mapSides_number (C : Equiv.Perm W.Seam) (hC) (a : Side W.Seam W.seamArity) :
    sideNumber (W.mapSides C hC a)=(C a.1,a.2.map Fin.val) := by
  rcases a with ⟨s,c⟩
  cases c <;> rfl
lemma mapSides_isNone (C : Equiv.Perm W.Seam) (hC) (a : Side W.Seam W.seamArity) :
    (W.mapSides C hC a).2.isNone=a.2.isNone := by
  rcases a with ⟨s,c⟩
  cases c <;> rfl

/-- Negative endpoints are the only local ends whose side number changes
under the whole-port rewiring. The ordered child NUMBER remains identical. -/
lemma rewire_sideOf (C : Equiv.Perm W.Seam) (hC) (x : LocalEnd V kind) :
    (W.rewire C hC).sideOf x =
      if (kind x.1).table.endpoint x.2.1 then W.sideOf x
      else W.mapSides C.symm (W.inverse_arity C hC) (W.sideOf x) := by
  apply @sideNumber_injective W.Seam W.seamArity
  refine ((W.rewire C hC).sideOf_number x).trans ?_
  cases he : (kind x.1).table.endpoint x.2.1 with
  | false =>
    rw [ite_eq_right (by simp),W.mapSides_number]
    have hf := congrArg Prod.fst (W.sideOf_number x)
    have hc := congrArg Prod.snd (W.sideOf_number x)
    change (W.sideOf x).1=(W.endOf ⟨x.1,x.2.1⟩).1 at hf
    change (W.sideOf x).2.map Fin.val=x.2.2.map (fun j => ((kind x.1).childEnumeration x.2.1 j).val) at hc
    rw [hc,hf]
    apply Prod.ext
    · dsimp only [rewire,PortWiring.endOf]
      rw [dite_eq_right (by simp only [he,Bool.false_eq_true,not_false_eq_true]),
        dite_eq_right (by simp only [he,Bool.false_eq_true,not_false_eq_true])]
      rfl
    · rfl
  | true =>
    rw [ite_eq_left (by simp),W.sideOf_number]
    apply Prod.ext
    · dsimp only [rewire,PortWiring.endOf]
      rw [dite_eq_left he,dite_eq_left he]
    · rfl

/-- Separate parents from their individual ordered child occurrences. -/
def sideEntries : Side W.Seam W.seamArity ≃ W.Seam ⊕ ((s : W.Seam) × Fin (W.seamArity s)) where
  toFun a := match a with
    | ⟨s,none⟩ => .inl s
    | ⟨s,some i⟩ => .inr ⟨s,i⟩
  invFun a := match a with
    | .inl s => ⟨s,none⟩
    | .inr ⟨s,i⟩ => ⟨s,some i⟩
  left_inv a := by rcases a with ⟨s,c⟩; cases c <;> rfl
  right_inv a := by rcases a with s|⟨s,i⟩ <;> rfl

def entryAction (C D : Equiv.Perm W.Seam) (hD : ∀ s,W.seamArity (D s)=W.seamArity s) :
    Equiv.Perm (Side W.Seam W.seamArity) :=
  W.sideEntries.trans ((Equiv.sumCongr C (Equiv.sigmaCongr D
    (fun s => finCongr (hD s).symm))).trans W.sideEntries.symm)

lemma entryAction_none (C D : Equiv.Perm W.Seam) (hD) (s : W.Seam) :
    W.entryAction C D hD ⟨s,none⟩=⟨C s,none⟩ := rfl
lemma entryAction_some (C D : Equiv.Perm W.Seam) (hD) (s : W.Seam) (i : Fin (W.seamArity s)) :
    W.entryAction C D hD ⟨s,some i⟩=W.mapSides D hD ⟨s,some i⟩ := rfl

def positiveRelabel (C : Equiv.Perm W.Seam) (hC : ∀ s,W.seamArity (C s)=W.seamArity s) :=
  W.entryAction (Equiv.refl _) C.symm (W.inverse_arity C hC)
def cutAction (C : Equiv.Perm W.Seam) (hC : ∀ s,W.seamArity (C s)=W.seamArity s) :=
  W.entryAction C.symm C hC

lemma positiveRelabel_sideOf (C : Equiv.Perm W.Seam) (hC) (x : LocalEnd V kind)
    (hx : (kind x.1).table.endpoint x.2.1=x.2.2.isNone) :
    (W.rewire C hC).sideOf x=W.positiveRelabel C hC (W.sideOf x) := by
  rw [W.rewire_sideOf,hx,←W.sideOf_isNone x]
  generalize W.sideOf x=a
  rcases a with ⟨s,c⟩
  cases c <;> rfl

lemma negativeRelabel_sideOf (C : Equiv.Perm W.Seam) (hC) (x : LocalEnd V kind)
    (hx : (kind x.1).table.endpoint x.2.1≠x.2.2.isNone) :
    (W.rewire C hC).sideOf x=
      W.positiveRelabel C hC (W.cutAction C hC (W.sideOf x)) := by
  have he : (kind x.1).table.endpoint x.2.1= !x.2.2.isNone := Bool.eq_not_iff.mpr hx
  rw [W.rewire_sideOf,he,←W.sideOf_isNone x]
  generalize W.sideOf x=a
  rcases a with ⟨s,c⟩
  cases c with
  | none => rfl
  | some i =>
    apply sideNumber_injective
    change (s,some i.val)=(C.symm (C s),some _)
    rw [Equiv.symm_apply_apply]
    rfl

/-- The literal boundary permutation after rewiring: inverse action on parent
occurrences, forward action on EACH ordered child occurrence. This identity is
independent of colors, ranks, or any supposed ribbon template. -/
theorem rewire_boundary (C : Equiv.Perm W.Seam) (hC) (a : Side W.Seam W.seamArity) :
    ((W.rewire C hC).assemble (fun _ => ()) (fun _ => rfl)).vertexAssembly.corners.boundaryNext
      (W.positiveRelabel C hC a) =
    W.positiveRelabel C hC (W.cutAction C hC
      ((W.assemble (fun _ => ()) (fun _ => rfl)).vertexAssembly.corners.boundaryNext a)) := by
  obtain ⟨x,hx,rfl⟩ := W.oriented_side_exists a
  rw [←W.positiveRelabel_sideOf C hC x hx,
    (W.rewire C hC).boundaryNext_local _ _ x hx,W.boundaryNext_local _ _ x hx]
  apply W.negativeRelabel_sideOf
  intro hm
  exact (kind x.1).table.orientation x.2 |>.mp hm <| hx
end PortWiring
end IntegralCharacterVarieties.OccurrenceIncidence

namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable
lemma PortWiring.ext_wire {V : Type} {k : V → Kind} (W Z : PortWiring k)
    (h : W.wire=Z.wire) : W=Z := by
  cases W
  cases Z
  cases h
  rfl
variable {F S V U I : Type} {arity : S → ℕ}
    (A : PortAssembly F S V arity) {kind : U → Kind}
    (P : PortPatch kind I Bool Bool) (d : (u : U) → Decoration (kind u) F)
    (q : S) (hi : P.SignatureMatch d)
    (hp : ∀ b,portSignature d (P.plus (.inr b)).val=A.seamSignature q)
    (hm : ∀ b,portSignature d (P.minus (.inr b)).val=A.seamSignature q)

include hp hm in
lemma graft_close_arity (b : Bool) :
    (kind (P.minus (.inr b)).val.1).arity (P.minus (.inr b)).val.2=
      (kind (P.plus (.inr b)).val.1).arity (P.plus (.inr b)).val.2 :=
  Decoration.arity_of_signature _ _ ((hm b).trans (hp b).symm)

noncomputable def graftBase : PortWiring (sumKind A.kind kind) :=
  A.toWiring.sum (P.complete (Equiv.refl Bool) (graft_close_arity A P d q hp hm))

lemma graftBase_wire (z : S ⊕ (I ⊕ Bool)) :
    (graftBase A P d q hp hm).wire (graftPlus A P z)=graftMinus A P z := by
  rcases z with s|(i|b)
  · change (A.toWiring.sum _).wire (sumPortAt A.kind kind true (.inl (A.portAt true s)))=_
    rw [PortWiring.sum_wire_left]
    change sumPortAt A.kind kind false (.inl (A.portAt false ((A.portAt true).symm (A.portAt true s))))=_
    rw [Equiv.symm_apply_apply]
    rfl
  · change (A.toWiring.sum _).wire (sumPortAt A.kind kind true (.inr (P.plus (.inl i))))=_
    erw [PortWiring.sum_wire_right,P.complete_internal]
    rfl
  · change (A.toWiring.sum _).wire (sumPortAt A.kind kind true (.inr (P.plus (.inr b))))=_
    erw [PortWiring.sum_wire_right,P.complete_external]
    rfl

noncomputable def graftPerm : Equiv.Perm (PortAt (sumKind A.kind kind) true) :=
  (graftPlus A P).symm.trans ((graftCycle q).trans (graftPlus A P))

@[simp] lemma graftPerm_apply (z : S ⊕ (I ⊕ Bool)) :
    graftPerm A P q (graftPlus A P z)=graftPlus A P (graftCycle q z) := by
  simp [graftPerm]

lemma graftPerm_wire (p : PortAt (sumKind A.kind kind) true) :
    (graftBase A P d q hp hm).wire (graftPerm A P q p)=
      (graftWiring A P d q hi hp hm).wire p := by
  obtain ⟨z,rfl⟩ := (graftPlus A P).surjective p
  rw [graftPerm_apply,graftBase_wire]
  change _=graftMinus A P (graftCycle q ((graftPlus A P).symm (graftPlus A P z)))
  rw [Equiv.symm_apply_apply]

include hi in
lemma graftPerm_arity (p : PortAt (sumKind A.kind kind) true) :
    (graftBase A P d q hp hm).seamArity (graftPerm A P q p)=
      (graftBase A P d q hp hm).seamArity p := by
  have h := (graftBase A P d q hp hm).arity (graftPerm A P q p)
  rw [graftPerm_wire A P d q hi hp hm] at h
  exact h.symm.trans ((graftWiring A P d q hi hp hm).arity p)

/-- The actual inverse-band assembly, not a guessed cyclic template, is the
three-port surgery of the disjoint old assembly and its closed doubled band. -/
theorem graftWiring_eq_rewire :
    graftWiring A P d q hi hp hm=
      (graftBase A P d q hp hm).rewire (graftPerm A P q)
        (graftPerm_arity A P d q hi hp hm) := by
  have hw : (graftWiring A P d q hi hp hm).wire=
      ((graftBase A P d q hp hm).rewire (graftPerm A P q)
        (graftPerm_arity A P d q hi hp hm)).wire := by
    apply Equiv.ext
    intro p
    exact (graftPerm_wire A P d q hi hp hm p).symm
  exact PortWiring.ext_wire _ _ hw

end IntegralCharacterVarieties.OccurrenceIncidence
namespace IntegralCharacterVarieties.BoundarySurgery
open scoped Classical
open Equiv Equiv.Perm
variable {α : Type} (N : Equiv.Perm α) (s t : Finset α) (x y : α)
    (hs : N.IsCycleOn (s : Set α)) (ht : N.IsCycleOn (t : Set α))
    (hx : x∈s) (hy : y∈t) (hdis : Disjoint s t)

include hs hx hy hdis in
lemma splice_pow_lt (n : ℕ) (hn : n<s.card) :
    ((Equiv.swap x y*N)^n) x=(N^n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',pow_succ',mul_apply,mul_apply,ih (by omega)]
    have hn0 : 0<n+1 := by omega
    have hne : (N^(n+1)) x≠x := by
      intro he
      have hd := (hs.pow_apply_eq hx).mp he
      have hp := Finset.card_pos.mpr ⟨x,hx⟩
      exact (Nat.le_of_dvd hn0 hd).not_gt hn
    have hm : (N^(n+1)) x∈s := hs.1.mapsTo.iterate (n+1) hx
    have hny : (N^(n+1)) x≠y := by
      intro he
      exact Finset.disjoint_left.mp hdis (he ▸ hm) hy
    simpa only [pow_succ',mul_apply] using Equiv.swap_apply_of_ne_of_ne hne hny

include hs hx hy hdis in
lemma splice_pow_card : ((Equiv.swap x y*N)^s.card) x=y := by
  have hp : 0<s.card := Finset.card_pos.mpr ⟨x,hx⟩
  have hc : s.card=(s.card-1)+1 := by omega
  rw [hc,pow_succ',mul_apply,splice_pow_lt N s t x y hs hx hy hdis _ (by omega)]
  have he : N ((N^(s.card-1)) x)=x := by
    rw [←mul_apply,←pow_succ',←hc]
    exact hs.pow_card_apply hx
  rw [mul_apply,he,Equiv.swap_apply_left]

include hs ht hx hy hdis in
/-- Splicing two distinct actual boundary circuits at designated entries
joins them to ONE circuit and retains every side, including singleton loops. -/
theorem splice_isCycle : (Equiv.swap x y*N).IsCycleOn ((s∪t : Finset α) : Set α) := by
  have hxy : (Equiv.swap x y*N).SameCycle x y :=
    ⟨(s.card : ℤ),by simpa using splice_pow_card N s t x y hs hx hy hdis⟩
  have hxs : ∀ z∈s,(Equiv.swap x y*N).SameCycle x z := by
    intro z hz
    obtain ⟨n,hn,rfl⟩ := hs.exists_pow_eq hx hz
    exact ⟨(n : ℤ),by simpa using splice_pow_lt N s t x y hs hx hy hdis n hn⟩
  have hyt : ∀ z∈t,(Equiv.swap x y*N).SameCycle y z := by
    intro z hz
    obtain ⟨n,hn,rfl⟩ := ht.exists_pow_eq hy hz
    refine ⟨(n : ℤ),?_⟩
    simpa only [zpow_natCast,Equiv.swap_comm y x] using
      splice_pow_lt N t s y x ht hy hx hdis.symm n hn
  refine ⟨?_,?_⟩
  · have hN : Set.BijOn N ((s∪t : Finset α) : Set α) ((s∪t : Finset α) : Set α) := by
      simpa only [Finset.coe_union] using hs.1.union ht.1 N.injective.injOn
    exact (Equiv.bijOn_swap (by simp [hx]) (by simp [hy])).comp hN
  · intro a ha b hb
    have ha' : (Equiv.swap x y*N).SameCycle x a := by
      rcases Finset.mem_union.mp ha with h|h
      · exact hxs a h
      · exact hxy.trans (hyt a h)
    have hb' : (Equiv.swap x y*N).SameCycle x b := by
      rcases Finset.mem_union.mp hb with h|h
      · exact hxs b h
      · exact hxy.trans (hyt b h)
    exact ha'.symm.trans hb'

end IntegralCharacterVarieties.BoundarySurgery

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand
open scoped Classical
variable {F : Type} {p : F} {a b : List F} (B : RealizedBand p a b)

abbrev StripRoot := {x : B.StripNode // ¬∃ e,B.stripTarget e=x}
abbrev ShortChild := (B.kind 0).table.Child (B.kind 0).input ⊕
  (B.kind (Fin.last B.length)).table.Child (B.kind (Fin.last B.length)).output

lemma inputStrip_injective : Function.Injective B.inputStrip := by
  intro c d h
  exact (B.kind 0).inputNode_injective (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
lemma outputStrip_injective : Function.Injective B.outputStrip := by
  intro c d h
  exact (B.kind (Fin.last B.length)).outputNode_injective (eq_of_heq (Sigma.mk.inj_iff.mp h).2)

lemma outputRoot_injective : Function.Injective (fun c => B.stripForest.root (B.outputStrip c)) := by
  intro c d h
  apply B.outputStrip_injective
  have ht := congrArg B.stripForest.tip h
  rw [B.stripForest.tip_root,B.stripForest.tip_root,
    B.stripForest.tip_of_sink _ (B.outputStrip_external c),
    B.stripForest.tip_of_sink _ (B.outputStrip_external d)] at ht
  exact ht

noncomputable def shortRoot : B.ShortChild → B.StripRoot
  | .inl c => ⟨B.inputStrip c,B.inputStrip_external c⟩
  | .inr c => ⟨B.stripForest.root (B.outputStrip c),B.stripForest.root_external _⟩

/-- Distinct incidence occurrences contact distinct doubled strips. In
particular a row and a column may carry the same old facet but they CANNOT be
identified before the actual gluing. -/
lemma shortRoot_injective (h : List.Disjoint a b) : Function.Injective B.shortRoot := by
  intro x y he
  have hv := congrArg Subtype.val he
  cases x with
  | inl c =>
    cases y with
    | inl d => exact congrArg Sum.inl (B.inputStrip_injective hv)
    | inr d => exact False.elim (B.no_short_to_short h c d hv.symm)
  | inr c =>
    cases y with
    | inl d => exact False.elim (B.no_short_to_short h d c hv)
    | inr d => exact congrArg Sum.inr (B.outputRoot_injective hv)

noncomputable def contactEmbedding (h : List.Disjoint a b) : B.ShortChild ↪ B.StripRoot :=
  ⟨B.shortRoot,B.shortRoot_injective h⟩

/-- These, and not cell-rank values, label the newly created disk facets. -/
abbrev FreshStrip := {r : B.StripRoot // r∉Set.range B.shortRoot}

noncomputable def stripDecomposition (h : List.Disjoint a b) :
    B.ShortChild ⊕ B.FreshStrip ≃ B.StripRoot :=
  (Equiv.sumCongr (Equiv.ofInjective B.shortRoot (B.shortRoot_injective h))
    (Equiv.refl B.FreshStrip)).trans (Equiv.sumCompl (fun r => r∈Set.range B.shortRoot))

lemma root_root (x : B.StripNode) : B.stripForest.root (B.stripForest.root x)=B.stripForest.root x :=
  B.stripForest.root_of_source _ (B.stripForest.root_external x)

lemma stripCycle_mem_orig (x : B.StripNode) :
    B.origStripSide x∈B.stripCycle (B.stripForest.root x) := ⟨x,rfl,Or.inl rfl⟩
lemma stripCycle_mem_mirror (x : B.StripNode) :
    B.mirrorStripSide x∈B.stripCycle (B.stripForest.root x) := ⟨x,rfl,Or.inr rfl⟩

/-- An actual short-end child occurs on a certified strip circuit, not just
in an endpoint list. -/
lemma inputContact_cycle (c) : B.mirrorStripSide (B.inputStrip c)∈
    B.stripCycle (B.shortRoot (.inl c)).val := by
  exact ⟨B.inputStrip c,B.stripForest.root_of_source _ (B.inputStrip_external c),Or.inr rfl⟩
lemma outputContact_cycle (c) : B.origStripSide (B.outputStrip c)∈
    B.stripCycle (B.shortRoot (.inr c)).val := B.stripCycle_mem_orig _

lemma contact_cycles_disjoint (h : List.Disjoint a b) {x y : B.ShortChild} (he : x≠y) :
    Disjoint (B.stripCycle (B.shortRoot x).val) (B.stripCycle (B.shortRoot y).val) :=
  B.stripCycle_disjoint (fun hxy => he (B.shortRoot_injective h (Subtype.ext hxy)))

lemma fresh_contact_disjoint (r : B.FreshStrip) (c : B.ShortChild) :
    Disjoint (B.stripCycle r.val.val) (B.stripCycle (B.shortRoot c).val) := by
  apply B.stripCycle_disjoint
  intro he
  exact r.property ⟨c,Subtype.ext he.symm⟩
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand

end OAI
