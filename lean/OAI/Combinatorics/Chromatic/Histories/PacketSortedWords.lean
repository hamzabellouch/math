import Mathlib
import OAI.Combinatorics.Chromatic.Walls.ElementaryMatrixDuality
import OAI.Combinatorics.Chromatic.Histories.SortedFiberPerm

namespace OAI

section
namespace ElementaryPositivity.Packets
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ} {A B:Type*} [Fintype A] [LinearOrder A] [Fintype B] [DecidableEq B]
variable (π:Fin n → B)

def rows (w:Fin n → A) (b:B):Finset A:=(fiber π b).image w
omit [Fintype A] [Fintype B] in
lemma sorted_injOn (w:Fin n → A) (hw:Sorted π w) (b:B) : Set.InjOn w (fiber π b) := by
  intro i hi j hj he
  have hh:π i=π j:=(mem_fiber π b i).mp hi |>.trans ((mem_fiber π b j).mp hj).symm
  rcases lt_trichotomy i j with h|h|h
  · exact False.elim ((ne_of_lt (hw i j hh h)) he)
  · exact h
  · exact False.elim ((ne_of_lt (hw j i hh.symm h)) he.symm)
omit [Fintype A] [Fintype B] in
lemma rows_card (w:Fin n → A) (hw:Sorted π w) (b:B) : (rows π w b).card=card π b:=
  Finset.card_image_of_injOn (sorted_injOn π w hw b)

def wordCount (w:Fin n → A) : A →₀ ℕ:=∑i,Finsupp.single (w i) 1
omit [Fintype A] in
lemma wordCount_apply (w:Fin n → A) (a:A) : wordCount w a=(Finset.univ.filter (fun i=>w i=a)).card:=by
  simp [wordCount,Finsupp.single_apply,eq_comm]
omit [Fintype A] [LinearOrder A] in
lemma wordCount_degree (w:Fin n → A) : (wordCount w).degree=n := by
  simp [wordCount,map_sum]

omit [Fintype A] in
lemma rows_colCount (w:Fin n → A) (hw:Sorted π w) : ElementaryMatrix.colCount (rows π w)=wordCount w := by
  unfold ElementaryMatrix.colCount rows wordCount
  conv_lhs=>arg 2; ext b; rw [Finset.sum_image (sorted_injOn π w hw b)]
  change (∑b,∑i∈Finset.univ.filter (fun i=>π i=b),Finsupp.single (w i) 1)=_
  rw [Finset.sum_fiberwise]

abbrev SortedWord:= {w:Fin n → A // Sorted π w}
abbrev RowFamily:= {s:B → Finset A // ∀b,(s b).card=card π b}

def fromRows (s:RowFamily (A:=A) π) (i:Fin n) : A:=
  (s.val (π i)).orderEmbOfFin (s.property (π i)) ((fiberOrder π (π i) rfl).symm ⟨i,rfl⟩)

omit [Fintype A] [Fintype B] in
lemma fromRows_mem (s:RowFamily (A:=A) π) (i:Fin n) : fromRows π s i∈s.val (π i):=
  (s.val (π i)).orderEmbOfFin_mem _ _

omit [Fintype A] [Fintype B] in
lemma fromRows_at (s:RowFamily (A:=A) π) (b:B) (i:{i // π i=b}) :
    fromRows π s i.val=(s.val b).orderEmbOfFin (s.property b) ((fiberOrder π b rfl).symm i) := by
  have hi:=i.property
  rcases i with ⟨i,hi⟩
  dsimp only at hi ⊢
  subst b
  rfl

omit [Fintype A] [Fintype B] in
lemma fromRows_sorted (s:RowFamily (A:=A) π) : Sorted π (fromRows π s) := by
  intro i j hij hlt
  rw [fromRows_at π s (π i) ⟨i,rfl⟩,fromRows_at π s (π i) ⟨j,hij.symm⟩]
  exact ((s.val (π i)).orderEmbOfFin _).strictMono
    ((fiberOrder π (π i) rfl).symm.strictMono hlt)

omit [Fintype A] [Fintype B] in
lemma rows_fromRows (s:RowFamily (A:=A) π) : rows π (fromRows π s)=s.val := by
  funext b
  apply Finset.Subset.antisymm
  · intro a ha
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp ha
    have H:=fromRows_mem π s i
    rwa [(mem_fiber π b i).mp hi] at H
  · intro a ha
    let k:=((s.val b).orderIsoOfFin (s.property b)).symm ⟨a,ha⟩
    let i: {i // π i=b}:=fiberOrder π b rfl k
    refine Finset.mem_image.mpr ⟨i.val,(mem_fiber π b i.val).mpr i.property,?_⟩
    rw [fromRows_at π s b i]
    dsimp [i]
    rw [OrderIso.symm_apply_apply]
    exact congrArg Subtype.val (((s.val b).orderIsoOfFin (s.property b)).apply_symm_apply ⟨a,ha⟩)

omit [Fintype B] in
lemma sorted_rows_unique (w v:Fin n → A) (hw:Sorted π w) (hv:Sorted π v)
    (he:rows π w=rows π v) : w=v := by
  let iso (u:Fin n → A) (hu:Sorted π u) (b:B) : {i // π i=b} ≃o (rows π u b):=
    StrictMono.orderIsoOfSurjective (fun i=>⟨u i,Finset.mem_image.mpr ⟨i,(mem_fiber π b i.val).mpr i.property,rfl⟩⟩)
      (fun i j hij=>hu i j (i.property.trans j.property.symm) hij)
      (by
        rintro ⟨a,ha⟩
        obtain ⟨i,hi,he⟩:=Finset.mem_image.mp ha
        exact ⟨⟨i,(mem_fiber π b i).mp hi⟩,Subtype.ext he⟩)
  funext i
  let vIso:= (iso v hv (π i)).trans (Set.orderIsoOfEq _ _
    (congrArg (fun s:Finset A=>(s:Set A)) (congrFun he.symm (π i))))
  have H:iso w hw (π i)=vIso:=Subsingleton.elim _ _
  exact congrArg (fun q=>(q ⟨i,rfl⟩).val) H

def rowsEquiv : SortedWord (A:=A) π ≃ RowFamily (A:=A) π where
  toFun w:=⟨rows π w.val,rows_card π w.val w.property⟩
  invFun s:=⟨fromRows π s,fromRows_sorted π s⟩
  left_inv w:=Subtype.ext (sorted_rows_unique π _ _ (fromRows_sorted π _) w.property (rows_fromRows π _))
  right_inv s:=Subtype.ext (rows_fromRows π s)
end
end ElementaryPositivity.Packets

end
section
namespace ElementaryPositivity.Packets
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ} {A:Type*} [Fintype A] [LinearOrder A]

def packetProfile (J:Finset (Fin (n-1))) : Fin (n+1) →₀ ℕ:=wordCount (index J)
lemma packetProfile_apply (J:Finset (Fin (n-1))) (b:Fin (n+1)) :
    packetProfile J b=card (index J) b:=wordCount_apply _ _
lemma packetProfile_degree (J:Finset (Fin (n-1))) : (packetProfile J).degree=n:=wordCount_degree _

omit [Fintype A] in
lemma anchor_required_iff (J:Finset (Fin (n-1))) (w:Fin n → A) :
    J⊆ascentMask (·<·) w ↔ Sorted (index J) w := by
  constructor
  · intro hw i j he hij
    exact inside_of_required (·<·) (fun _ _ _=>lt_trans) J w hw i j hij he
  · intro hw t ht
    apply (mem_ascentMask _ _ _).mpr
    exact hw (left t) (right t) ((index_left_right J t).mpr ht) (by change t.val<t.val+1; omega)

abbrev AnchorWord (μ:A →₀ ℕ):={w:Fin n → A // wordCount w=μ}
abbrev RequiredAnchor (μ:A →₀ ℕ) (J:Finset (Fin (n-1))):=
  {w:Fin n → A // wordCount w=μ ∧ J⊆ascentMask (·<·) w}
abbrev PacketRows (μ:A →₀ ℕ) (J:Finset (Fin (n-1))):=
  {s:Fin (n+1) → Finset A // ElementaryMatrix.rowCount s=packetProfile J ∧ ElementaryMatrix.colCount s=μ}

def anchorRowsEquiv (μ:A →₀ ℕ) (J:Finset (Fin (n-1))) : RequiredAnchor μ J ≃ PacketRows μ J where
  toFun w:=⟨rows (index J) w.val,by
    have hs:Sorted (index J) w.val:=(anchor_required_iff J w.val).mp w.property.2
    constructor
    · apply (ElementaryMatrix.rowCount_eq _ _).mpr
      intro b
      rw [rows_card _ _ hs,packetProfile_apply]
    · rw [rows_colCount _ _ hs,w.property.1]⟩
  invFun s:=by
    let t:RowFamily (A:=A) (index J):=⟨s.val,fun b=>by
      rw [←packetProfile_apply J b]
      exact (ElementaryMatrix.rowCount_eq _ _).mp s.property.1 b⟩
    exact ⟨fromRows (index J) t,by
      constructor
      · rw [←rows_colCount _ _ (fromRows_sorted _ t),rows_fromRows]
        exact s.property.2
      · exact (anchor_required_iff J _).mpr (fromRows_sorted _ t)⟩
  left_inv w:=by
    apply Subtype.ext
    exact sorted_rows_unique _ _ _ (fromRows_sorted _ _) ((anchor_required_iff J w.val).mp w.property.2)
      (rows_fromRows _ _)
  right_inv s:=by
    apply Subtype.ext
    exact rows_fromRows _ _

lemma requiredAnchor_card {R:Type*} [CommSemiring R] (μ:A →₀ ℕ) (J:Finset (Fin (n-1))) :
    (∏i:A,MvPolynomial.esymm (Fin (n+1)) R (μ i)).coeff (packetProfile J)=
      (Fintype.card (RequiredAnchor μ J):R) := by
  rw [ElementaryMatrix.duality,ElementaryMatrix.elementary_product_coeff]
  rw [Fintype.card_congr (anchorRowsEquiv μ J)]
  simp only [Fintype.card_subtype]
  rw [←Finset.sum_filter]
  simp
end
end ElementaryPositivity.Packets

end

end OAI
