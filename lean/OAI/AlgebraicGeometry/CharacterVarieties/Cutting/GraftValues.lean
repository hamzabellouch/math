import OAI.AlgebraicGeometry.CharacterVarieties.Cutting.BoundaryEnumeration

namespace OAI

/-!
# Transport values on the old and inserted sides of an inverse-band graft.

This formalizes the band reconstruction for filtered surface local systems in
*Integral points on character varieties of curves*.
-/

noncomputable section
namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable
variable {F S V W I : Type} {arity : S → ℕ}
    (A : PortAssembly F S V arity) {kind : W → Kind}
    (P : PortPatch kind I Bool Bool) (d : (w : W) → Decoration (kind w) F)
    (q : S) (hi : P.SignatureMatch d)
    (hp : ∀ b,portSignature d (P.plus (.inr b)).val=A.seamSignature q)
    (hm : ∀ b,portSignature d (P.minus (.inr b)).val=A.seamSignature q)
local notation "C" => graftAssembly A P d q hi hp hm
local notation "W" => graftWiring A P d q hi hp hm

def graftLabelArity (z : S ⊕ (I ⊕ Bool)) : ℕ := (W).seamArity (graftPlus A P z)
lemma graftLabelArity_old (s : S) : graftLabelArity A P d q hi hp hm (.inl s)=arity s :=
  A.portAt_arity s true
lemma graftLabelArity_short (b : Bool) : graftLabelArity A P d q hi hp hm (.inr (.inr b))=arity q := by
  have h := congrArg (fun z : F × List F => z.2.length) (hp b)
  simp only [portSignature,Decoration.signature,Decoration.children,
    PortAssembly.seamSignature,List.length_ofFn] at h
  exact h

lemma graft_old_color (s : S) (i : Option (Fin (arity s))) :
    (C).facet ⟨graftPlus A P (.inl s),
      i.map (finCongr (graftLabelArity_old A P d q hi hp hm s).symm)⟩=A.facet ⟨s,i⟩ := by
  change (A.decoration (A.portAt true s).val.1).portColor (A.portAt true s).val.2 _=_
  erw [A.decoration_portColor]
  have he := A.attach_portAt s true
  cases i with
  | none => exact congrArg (fun s => A.facet ⟨s,none⟩) (congrArg Prod.fst he)
  | some i =>
    have haux {s t : S} (h : s=t) (i : Fin (arity s)) (j : Fin (arity t))
        (hij : i.val=j.val) : A.facet ⟨s,some i⟩=A.facet ⟨t,some j⟩ := by
      subst t
      congr 2
      exact congrArg some (Fin.ext hij)
    exact haux (congrArg Prod.fst he) _ i rfl

lemma graft_short_color (b : Bool) (i : Option (Fin (arity q))) :
    (C).facet ⟨graftPlus A P (.inr (.inr b)),
      i.map (finCongr (graftLabelArity_short A P d q hi hp hm b).symm)⟩=A.facet ⟨q,i⟩ := by
  cases i with
  | none => exact congrArg Prod.fst (hp b)
  | some i =>
    have h := congrArg Prod.snd (hp b)
    change (d (P.plus (.inr b)).val.1).children (P.plus (.inr b)).val.2=
      List.ofFn (fun i => A.facet ⟨q,some i⟩) at h
    have he := congrArg (fun l : List F => l[i.val]?) h
    have ht : i.val<(kind (P.plus (.inr b)).val.1).arity (P.plus (.inr b)).val.2 :=
      (finCongr (graftLabelArity_short A P d q hi hp hm b).symm i).isLt
    simp only [Decoration.children,List.getElem?_ofFn,dite_eq_left ht,dite_eq_left i.isLt] at he
    exact Option.some.inj he

/-- Sides have complete positive-port coordinates. The arity is the ACTUAL
arity of that port, not merely a count inferred from endpoint names. -/
def graftSideEquiv :
    ((z : S ⊕ (I ⊕ Bool)) × Option (Fin (graftLabelArity A P d q hi hp hm z))) ≃
      Side (W).Seam (W).seamArity :=
  Equiv.sigmaCongr (graftPlus A P) (fun _ => Equiv.refl _)
end IntegralCharacterVarieties.OccurrenceIncidence
end

noncomputable section
namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical Matrix
open VertexTable
variable {F S V W I R : Type} {arity : S → ℕ} [CommRing R]
    (A : PortAssembly F S V arity) {kind : W → Kind}
    (P : PortPatch kind I Bool Bool) (d : (w : W) → Decoration (kind w) F)
    (q : S) (hi : P.SignatureMatch d)
    (hp : ∀ b,portSignature d (P.plus (.inr b)).val=A.seamSignature q)
    (hm : ∀ b,portSignature d (P.minus (.inr b)).val=A.seamSignature q)
local notation "C" => graftAssembly A P d q hi hp hm
local notation "E" => graftSideEquiv A P d q hi hp hm
local notation "a" => graftLabelArity A P d q hi hp hm
variable (rank : F → ℕ)
abbrev FacetUnit (f : F) := (Matrix (Fin (rank f)) (Fin (rank f)) R)ˣ

def graftLabelValues (old : (s : Side S arity) → FacetUnit (R:=R) rank (A.facet s))
    (short : Bool → (i : Option (Fin (arity q))) → FacetUnit (R:=R) rank (A.facet ⟨q,i⟩))
    (z : S ⊕ (I ⊕ Bool)) (i : Option (Fin (a z))) :
    FacetUnit (R:=R) rank ((C).facet (E ⟨z,i⟩)) := by
  rcases z with s|(j|b)
  · let h := graftLabelArity_old A P d q hi hp hm s
    let j := i.map (finCongr h)
    have hj : j.map (finCongr h.symm)=i := by
      cases i with
      | none => rfl
      | some i => simp only [j,Option.map_some]; congr 1
    have hc := graft_old_color A P d q hi hp hm s j
    erw [hj] at hc
    exact cast (congrArg (FacetUnit (R:=R) rank) hc.symm) (old ⟨s,j⟩)
  · exact 1
  · let h := graftLabelArity_short A P d q hi hp hm b
    let j := i.map (finCongr h)
    have hj : j.map (finCongr h.symm)=i := by
      cases i with
      | none => rfl
      | some i => simp only [j,Option.map_some]; congr 1
    have hc := graft_short_color A P d q hi hp hm b j
    erw [hj] at hc
    exact cast (congrArg (FacetUnit (R:=R) rank) hc.symm) (short b j)

def graftSideValues (old : (s : Side S arity) → FacetUnit (R:=R) rank (A.facet s))
    (short : Bool → (i : Option (Fin (arity q))) → FacetUnit (R:=R) rank (A.facet ⟨q,i⟩))
    (s : Side (graftWiring A P d q hi hp hm).Seam (graftWiring A P d q hi hp hm).seamArity) :
    FacetUnit (R:=R) rank ((C).facet s) :=
  Equiv.piCongrLeft (fun s => FacetUnit (R:=R) rank ((C).facet s)) (E)
    (fun v => graftLabelValues A P d q hi hp hm rank old short v.1 v.2) s

lemma graftSideValues_coord (old : (s : Side S arity) → FacetUnit (R:=R) rank (A.facet s))
    (short : Bool → (i : Option (Fin (arity q))) → FacetUnit (R:=R) rank (A.facet ⟨q,i⟩))
    (z : S ⊕ (I ⊕ Bool)) (i : Option (Fin (a z))) :
    graftSideValues A P d q hi hp hm rank old short (E ⟨z,i⟩)=
      graftLabelValues A P d q hi hp hm rank old short z i := by
  exact Equiv.piCongrLeft_apply_apply (fun s => FacetUnit (R:=R) rank ((C).facet s))
    (E) (fun v => graftLabelValues A P d q hi hp hm rank old short v.1 v.2) ⟨z,i⟩

end IntegralCharacterVarieties.OccurrenceIncidence
end

noncomputable section
namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical Matrix
open VertexTable SurfacePresentation.Diagram
variable {F S V W I R : Type} {arity : S → ℕ} [CommRing R]
    (A : PortAssembly F S V arity) {kind : W → Kind}
    (P : PortPatch kind I Bool Bool) (d : (w : W) → Decoration (kind w) F)
    (q : S) (hi : P.SignatureMatch d)
    (hp : ∀ b,portSignature d (P.plus (.inr b)).val=A.seamSignature q)
    (hm : ∀ b,portSignature d (P.minus (.inr b)).val=A.seamSignature q)
local notation "C" => graftAssembly A P d q hi hp hm
local notation "E" => graftSideEquiv A P d q hi hp hm
local notation "a" => graftLabelArity A P d q hi hp hm
variable (rank : F → ℕ)
    (old : (s : Side S arity) → FacetUnit (R:=R) rank (A.facet s))
    (short : Bool → (i : Option (Fin (arity q))) → FacetUnit (R:=R) rank (A.facet ⟨q,i⟩))

lemma graftSideValues_internal (j : I) (i : Option (Fin (a (.inr (.inl j))))) :
    graftSideValues A P d q hi hp hm rank old short (E ⟨.inr (.inl j),i⟩)=1 := by
  rw [graftSideValues_coord]
  rfl

lemma rebaseUnit_cast_facet {f g : F} (h : f=g) (u : FacetUnit (R:=R) rank g)
    (ht : FacetUnit (R:=R) rank g=FacetUnit (R:=R) rank f) :
    rebaseUnit (congrArg rank h) (cast ht u)=u := by
  subst g
  rfl

lemma graftSideValues_old (s : S) (i : Option (Fin (arity s))) :
    rebaseUnit (congrArg rank (graft_old_color A P d q hi hp hm s i))
      (graftSideValues A P d q hi hp hm rank old short
        (E ⟨.inl s,i.map (finCongr (graftLabelArity_old A P d q hi hp hm s).symm)⟩))=old ⟨s,i⟩ := by
  rw [graftSideValues_coord]
  unfold graftLabelValues
  dsimp only
  have hj : (i.map (finCongr (graftLabelArity_old A P d q hi hp hm s).symm)).map
      (finCongr (graftLabelArity_old A P d q hi hp hm s))=i := by
    cases i with
    | none => rfl
    | some _ => rfl
  generalize_proofs h₁ h₂
  have aux {c e : Option (Fin (arity s))} (hce : c=e)
      {u : F} (hu : u=A.facet ⟨s,e⟩)
      (ht : FacetUnit (R:=R) rank (A.facet ⟨s,c⟩)=FacetUnit (R:=R) rank u) :
      rebaseUnit (congrArg rank hu) (cast ht (old ⟨s,c⟩))=old ⟨s,e⟩ := by
    subst e
    exact rebaseUnit_cast_facet rank hu _ ht
  exact aux hj (graft_old_color A P d q hi hp hm s i) _

lemma graftSideValues_short (b : Bool) (i : Option (Fin (arity q))) :
    rebaseUnit (congrArg rank (graft_short_color A P d q hi hp hm b i))
      (graftSideValues A P d q hi hp hm rank old short
        (E ⟨.inr (.inr b),i.map (finCongr (graftLabelArity_short A P d q hi hp hm b).symm)⟩))=short b i := by
  rw [graftSideValues_coord]
  unfold graftLabelValues
  dsimp only
  have hj : (i.map (finCongr (graftLabelArity_short A P d q hi hp hm b).symm)).map
      (finCongr (graftLabelArity_short A P d q hi hp hm b))=i := by
    cases i with
    | none => rfl
    | some _ => rfl
  generalize_proofs h₁ h₂
  have aux {c e : Option (Fin (arity q))} (hce : c=e)
      {u : F} (hu : u=A.facet ⟨q,e⟩)
      (ht : FacetUnit (R:=R) rank (A.facet ⟨q,c⟩)=FacetUnit (R:=R) rank u) :
      rebaseUnit (congrArg rank hu) (cast ht (short b c))=short b e := by
    subst e
    exact rebaseUnit_cast_facet rank hu _ ht
  exact aux hj (graft_short_color A P d q hi hp hm b i) _
end IntegralCharacterVarieties.OccurrenceIncidence
end

noncomputable section
namespace IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
open scoped Classical Matrix
open VertexTable SurfacePresentation.Diagram
variable {F S V R : Type} {arity : S → ℕ} [CommRing R]
    (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
variable (rank : F → ℕ)
    (old : (s : Side S arity) → FacetUnit (R:=R) rank (A.facet s))
    (short : Bool → (i : Option (Fin (arity q))) → FacetUnit (R:=R) rank (A.facet ⟨q,i⟩))

def bandValues := graftSideValues A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus]; cases i <;> rfl) rank old short

def mirrorValue (v : Fin (B.length+1)) :=
  rebaseUnit (congrArg rank (mirrorSide_color A q B v))
    (bandValues A q B rank old short (mirrorSide A q B v))
def originalValue (v : Fin (B.length+1)) :=
  rebaseUnit (congrArg rank (originalSide_color A q B v))
    (bandValues A q B rank old short (originalSide A q B v))

lemma mirrorValue_last : mirrorValue A q B rank old short (Fin.last B.length)=short true none := by
  unfold mirrorValue bandValues
  exact graftSideValues_short A B.doublePatch (doubleDecoration B.decoration) q _ _ _ rank old short true none

lemma originalValue_zero : originalValue A q B rank old short 0=short false none := by
  unfold originalValue bandValues
  exact graftSideValues_short A B.doublePatch (doubleDecoration B.decoration) q _ _ _ rank old short false none

lemma mirrorValue_castSucc (j : Fin B.length) : mirrorValue A q B rank old short j.castSucc=1 := by
  unfold mirrorValue bandValues
  have h := graftSideValues_internal A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus]; cases i <;> rfl) rank old short
    (.inl (.inr j)) none
  change graftSideValues _ _ _ _ _ _ _ _ _ _ (mirrorSide A q B j.castSucc)=1 at h
  rw [h]
  exact (rebaseUnit (congrArg rank (mirrorSide_color A q B j.castSucc))).map_one

lemma originalValue_succ (j : Fin B.length) : originalValue A q B rank old short j.succ=1 := by
  unfold originalValue bandValues
  have h := graftSideValues_internal A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus]; cases i <;> rfl) rank old short
    (.inl (.inl j)) none
  change graftSideValues _ _ _ _ _ _ _ _ _ _ (originalSide A q B j.succ)=1 at h
  rw [h]
  exact (rebaseUnit (congrArg rank (originalSide_color A q B j.succ))).map_one

/-- The actual reflected principal circle has precisely the inverse-band inner
word, with the mirror orientation (not the unreflected gallery order). -/
lemma mirrorValues_word :
    (List.ofFn (fun i : Fin (B.length+1) => mirrorValue A q B rank old short i.rev)).reverse.prod=
      short true none := by
  rw [List.ofFn_succ,List.reverse_cons,List.prod_append]
  simp only [Fin.rev_zero,mirrorValue_last,List.prod_cons,List.prod_nil,mul_one]
  have h : (fun i : Fin B.length => mirrorValue A q B rank old short i.succ.rev)=fun _ => 1 := by
    funext i
    rw [Fin.rev_succ,mirrorValue_castSucc]
  rw [h]
  simp

lemma originalValues_identity (hshort : short false none=1) :
    ∀ i,originalValue A q B rank old short i=1 := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [originalValue_zero,hshort]
  · exact originalValue_succ A q B rank old short j
end IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
end

noncomputable section
namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical Matrix
open VertexTable SurfacePresentation.Diagram
variable {F S V W I R : Type} {arity : S → ℕ} [CommRing R]
    (A : PortAssembly F S V arity) {kind : W → Kind}
    (P : PortPatch kind I Bool Bool) (d : (w : W) → Decoration (kind w) F)
    (q : S) (hi : P.SignatureMatch d)
    (hp : ∀ b,portSignature d (P.plus (.inr b)).val=A.seamSignature q)
    (hm : ∀ b,portSignature d (P.minus (.inr b)).val=A.seamSignature q)
local notation "C" => graftAssembly A P d q hi hp hm
local notation "E" => graftSideEquiv A P d q hi hp hm
local notation "a" => graftLabelArity A P d q hi hp hm
variable (rank : F → ℕ)
    (old : (s : Side S arity) → FacetUnit (R:=R) rank (A.facet s))
    (short : Bool → (i : Option (Fin (arity q))) → FacetUnit (R:=R) rank (A.facet ⟨q,i⟩))

lemma graftSideValues_short_identity (b : Bool) (i : Fin (a (.inr (.inr b))))
    (hshort : ∀ j,short b (some j)=1) :
    graftSideValues A P d q hi hp hm rank old short (E ⟨.inr (.inr b),some i⟩)=1 := by
  let h := graftLabelArity_short A P d q hi hp hm b
  let j := finCongr h i
  have he : (some j).map (finCongr h.symm)=some i := rfl
  have z := graftSideValues_short A P d q hi hp hm rank old short b (some j)
  rw [hshort] at z
  apply (rebaseUnit (congrArg rank (graft_short_color A P d q hi hp hm b (some j)))).injective
  exact z.trans ((rebaseUnit _).map_one).symm
end IntegralCharacterVarieties.OccurrenceIncidence
end

noncomputable section
namespace IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
open scoped Classical Matrix
open VertexTable SurfacePresentation.Diagram
variable {F S V R : Type} {arity : S → ℕ} [CommRing R]
    (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
private abbrev doubledSideEquiv :=
  graftSideEquiv A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus]; cases i <;> rfl)

local notation "E" => doubledSideEquiv A q B

lemma oldEmbedding_coord (s : S) (i : Option (Fin (arity s))) :
    oldEmbedding A q B ⟨s,i⟩=E ⟨.inl s,i.map (finCongr (A.portAt_arity s true).symm)⟩ := by
  apply sideNumber_injective
  change sideNumber (A.toWiring.sumSides B.doubleWiring (.inl (A.wiringSides ⟨s,i⟩)))=_
  rw [A.toWiring.sumSides_number_left]
  have h := A.wiringSides_number ⟨s,i⟩
  have hh := congrArg (fun x => (sumPortAt A.kind (sumKind B.kind (mirrorKind B.kind)) true
    (.inl x.1),x.2)) h
  refine hh.trans ?_
  cases i <;> rfl

variable (rank : F → ℕ)
    (old : (s : Side S arity) → FacetUnit (R:=R) rank (A.facet s))
    (short : Bool → (i : Option (Fin (arity q))) → FacetUnit (R:=R) rank (A.facet ⟨q,i⟩))

/-- BOTH strips inserted after an old child have identity transports on every
literal side, including their short-end child occurrences. This excludes only
the two principal short parents, proved disjoint from the actual strip circuit. -/
lemma bandValues_strip (hshort : ∀ b i,short b (some i)=1)
    (r : B.StripRoot) (z : Side B.doubleWiring.Seam B.doubleWiring.seamArity)
    (hz : z∈B.stripCycle r.val) :
    bandValues A q B rank old short (bandEmbedding A q B z)=1 := by
  obtain ⟨⟨label,i⟩,he⟩ := (E).surjective (bandEmbedding A q B z)
  have hn := (B.sideStripRoot_eq_some_iff _ _).mpr hz
  have hno (s : S) (j : Option (Fin (arity s))) :
      E ⟨.inl s,j.map (finCongr (A.portAt_arity s true).symm)⟩≠bandEmbedding A q B z := by
    exact (oldEmbedding_coord A q B s j) ▸ (old_band_ne A q B ⟨s,j⟩ z)
  have hf : (⟨shortPort A q B false,none⟩ : Side (base A q B).Seam (base A q B).seamArity)≠bandEmbedding A q B z := by
    rw [←bandEmbedding_input_parent]
    intro h
    have hh := (bandEmbedding A q B).injective h
    rw [←hh,B.sideStripRoot_origPrincipal] at hn
    cases hn
  have ht : (⟨shortPort A q B true,none⟩ : Side (base A q B).Seam (base A q B).seamArity)≠bandEmbedding A q B z := by
    rw [←bandEmbedding_output_parent]
    intro h
    have hh := (bandEmbedding A q B).injective h
    rw [←hh,B.sideStripRoot_mirrorPrincipal] at hn
    cases hn
  rcases label with s|(j|b)
  · let j := i.map (finCongr (A.portAt_arity s true))
    have hj : j.map (finCongr (A.portAt_arity s true).symm)=i := by cases i <;> rfl
    exact False.elim (hno s j (hj ▸ he))
  · rw [←he]
    exact graftSideValues_internal A B.doublePatch (doubleDecoration B.decoration) q _ _ _ rank old short j i
  · cases i with
    | none =>
      cases b
      · exact False.elim (hf he)
      · exact False.elim (ht he)
    | some i =>
      have hh := graftSideValues_short_identity A B.doublePatch (doubleDecoration B.decoration) q
        (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
        (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
        (fun i => by rw [B.double_signature_minus]; cases i <;> rfl) rank old short b i (hshort b)
      exact (congrArg (fun z => bandValues A q B rank old short z=1) he).mp hh
end IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
end

namespace IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
open scoped Classical
open VertexTable
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
lemma oldEmbedding_color (a : Side S arity) :
    (A.graftBand q B).facet (oldEmbedding A q B a)=A.facet a := by
  rcases a with ⟨s,i⟩
  rw [oldEmbedding_coord]
  exact graft_old_color A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus]; cases i <;> rfl) s i
lemma next_pow_color (a : Side (base A q B).Seam (base A q B).seamArity) (n : ℕ) :
    (A.graftBand q B).facet (((next A q B)^n) a)=(A.graftBand q B).facet a := by
  exact (A.graftBand q B).vertexAssembly.corners.boundaryNext_iterate_facet a n
end IntegralCharacterVarieties.OccurrenceIncidence.BandGraft

noncomputable section
namespace IntegralCharacterVarieties.CutCircleIndex
open scoped Classical
variable {F G : Type} (n : F → ℕ) (p : F)
def facet : Label (G:=G) n → F ⊕ G
  | .inl ⟨f,_⟩ => .inl f
  | .inr (.inl _) => .inl p
  | .inr (.inr g) => .inr g
lemma enumeration_facet (f : F ⊕ G) (i : Fin (count n p f)) :
    facet n p (enumeration n p ⟨f,i⟩)=f := by
  cases f with
  | inl f =>
    refine Fin.addCases (motive:=fun i : Fin (n f+extra p f) =>
      facet n p (enumeration n p ⟨Sum.inl f,i⟩)=Sum.inl f) ?_ ?_ i
    · intro j
      rw [enumeration_old]
      rfl
    · intro j
      by_cases h : f=p
      · subst f
        have hj : j.val=0 := by
          have he : extra p p=1 := by simp [extra]
          have hi : j.val<1 := lt_of_lt_of_le j.isLt he.le
          omega
        have hh : j=⟨0,by simp [extra]⟩ := Fin.ext hj
        subst j
        exact congrArg (facet n p) (enumeration_mirror n p)
      · have hh : extra p f=0 := by simp [extra,h]
        exact (Fin.elim0 (j.cast hh))
  | inr g =>
    have hi : i=⟨0,Nat.zero_lt_one⟩ := @Subsingleton.elim (Fin 1) inferInstance _ _
    subst i
    rw [enumeration_fresh]
    rfl
end IntegralCharacterVarieties.CutCircleIndex
end

end OAI
