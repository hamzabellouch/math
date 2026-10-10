import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.BandCut
import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.BoundaryReordering

namespace OAI

/-!
# Ordered words for nonseparating surgery

Group identities describe the boundary words before and after a cut
at a specified occurrence of the parent side.
-/

namespace IntegralCharacterVarieties.SurfaceSurgery
variable {G : Type*} [Group G]

lemma ofFn_reverse_prod_blocks {m n : ℕ} (v : Fin (m*n) → G) :
    (List.ofFn v).reverse.prod =
      (List.ofFn (fun i : Fin m =>
        (List.ofFn (fun j : Fin n => v (finProdFinEquiv (i,j)))).reverse.prod)).reverse.prod := by
  rw [List.ofFn_mul]
  simp only [List.reverse_flatten,List.prod_flatten,List.map_reverse,List.map_ofFn]
  apply congrArg (fun f : Fin m → G => (List.ofFn f).reverse.prod)
  funext i
  apply congrArg (fun f : Fin n → G => (List.ofFn f).reverse.prod)
  funext j
  apply congrArg v
  apply Fin.ext
  simp [finProdFinEquiv,Nat.add_comm,Nat.mul_comm]

/-- The group identity for inverse nonseparating surgery at an arbitrary
position in the ordered surface word. -/
lemma inverse_cut_ordered_word (H R1 R2 c t a : G) :
    (t⁻¹*H*t)*((t⁻¹*(t*a*t⁻¹*a⁻¹))*R1*(t⁻¹*(t*a*t⁻¹*a⁻¹))⁻¹)*a*
      ((t⁻¹*a⁻¹*c)*R2*(t⁻¹*a⁻¹*c)⁻¹)*(t⁻¹*a⁻¹*c*t) =
        t⁻¹*(H*(t*a*t⁻¹*a⁻¹)*R1*c*R2)*t := by group
end IntegralCharacterVarieties.SurfaceSurgery

namespace IntegralCharacterVarieties.SurfaceSurgery
variable {G : Type*}

lemma ofFn_take_congr {n m : ℕ} (e f : Fin n → G)
    (h : ∀ (j : Fin n), j.val < m → e j=f j) :
    (List.ofFn e).take m=(List.ofFn f).take m := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_take,List.getElem_ofFn]
    apply h
    change i < m
    simp only [List.length_take,List.length_ofFn] at hi
    omega

lemma ofFn_drop_congr {n m : ℕ} (e f : Fin n → G)
    (h : ∀ (j : Fin n), m ≤ j.val → e j=f j) :
    (List.ofFn e).drop m=(List.ofFn f).drop m := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_drop,List.getElem_ofFn]
    apply h
    change m ≤ m+i
    omega

lemma list_split_at (l : List G) (i : ℕ) (hi : i<l.length) :
    l=(l.take i++[l[i]])++l.drop (i+1) := by
  rw [← List.take_succ_eq_append_getElem hi,List.take_append_drop]

variable [Group G]

lemma ofFn_three_regions {n : ℕ} (e f : Fin n → G) (i : Fin n) (U V a : G)
    (hbefore : ∀ (j : Fin n), j.val < i.val → f j=U*e j*U⁻¹)
    (hat : f i=a)
    (hafter : ∀ (j : Fin n), i.val < j.val → f j=V*e j*V⁻¹) :
    (List.ofFn f).prod =
      (U*((List.ofFn e).take i.val).prod*U⁻¹)*a*
        (V*((List.ofFn e).drop (i.val+1)).prod*V⁻¹) := by
  have hb := ofFn_take_congr f (fun j => U*e j*U⁻¹) hbefore
  have ha := ofFn_drop_congr (m:=i.val+1) f (fun j => V*e j*V⁻¹) (fun j hj => hafter j (by omega))
  have hsplit := list_split_at (List.ofFn f) i.val (by simp)
  conv_lhs => rw [hsplit]
  simp only [List.prod_append,List.prod_cons,List.prod_nil,mul_one,List.getElem_ofFn]
  rw [hat,hb,ha]
  have hbmap := map_list_prod (MulAut.conj U) ((List.ofFn e).take i.val)
  have hamap := map_list_prod (MulAut.conj V) ((List.ofFn e).drop (i.val+1))
  simp only [List.map_take,List.map_drop,List.map_ofFn,Function.comp_def,MulAut.conj_apply] at hbmap hamap
  rw [← hbmap,← hamap]

lemma ofFn_reverse_replace {n : ℕ} (e f : Fin n → G) (i : Fin n) (a : G)
    (he : ∀ j, j≠i → f j=e j) (hat : f i=a) :
    (List.ofFn f).reverse.prod =
      ((List.ofFn e).drop (i.val+1)).reverse.prod*a*
        ((List.ofFn e).take i.val).reverse.prod := by
  have hb := ofFn_take_congr (m:=i.val) f e (fun j hj => he j (by intro h; subst j; omega))
  have ha := ofFn_drop_congr (m:=i.val+1) f e (fun j hj => he j (by intro h; subst j; omega))
  have hsplit := list_split_at (List.ofFn f) i.val (by simp)
  conv_lhs => rw [hsplit]
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.prod_append,
    List.prod_cons,List.prod_nil,mul_one,List.getElem_ofFn]
  rw [hat,hb,ha]
  group
end IntegralCharacterVarieties.SurfaceSurgery

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence PortAssembly MatrixExpression
variable {F S V A : Type} {arity : S → ℕ} [CommRing A]
variable (D : Diagram F S V arity) (q : S)
variable (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)
variable (J T : D.BandCutUnit (A:=A) q)

lemma rebaseUnit_index {I : Type*} (r : I → ℕ)
    (v : (i : I) → (Matrix (Fin (r i)) (Fin (r i)) A)ˣ)
    {i j : I} (he : i=j) {n : ℕ} (hi : r i=n) (hj : r j=n) :
    rebaseUnit hi (v i)=rebaseUnit hj (v j) := by subst j; rfl

def bandCutReplacement (a : Side S arity) :
    (Matrix (Fin (D.rank (D.ports.facet a))) (Fin (D.rank (D.ports.facet a))) A)ˣ :=
  if ha : a=⟨q,none⟩ then by
    subst a
    exact rebaseUnit (D.seamRank q).symm J
  else g (.side a)

def bandCutLongValue (a : Side S arity) (k : Fin 3) :
    (Matrix (Fin (D.rank (D.ports.facet a))) (Fin (D.rank (D.ports.facet a))) A)ˣ :=
  rebaseUnit (congrArg D.rank (D.ports.bandCutLong_facet q a k))
    (D.bandCutSideValues q g J T (bandCutLong q (a,k)))

lemma bandCutLongValue_triple (a : Side S arity) :
    (List.ofFn (D.bandCutLongValue q g J T a)).reverse.prod = D.bandCutReplacement q g J a := by
  rcases a with ⟨s,c⟩
  cases c with
  | none =>
    by_cases hs : s=q
    · subst s
      have hv (k : Fin 3) : D.bandCutLongValue q g J T ⟨q,none⟩ k =
          if k=1 then rebaseUnit (D.seamRank q).symm J else 1 := by
        unfold bandCutLongValue
        by_cases hk : k=1
        · have he : bandCutLong (arity:=arity) q (⟨q,none⟩,k)=⟨Sum.inr (),some 0⟩ := by
            simp [bandCutLong,hk]
          erw [rebaseUnit_index (fun a => D.rank ((D.ports.bandCutPorts q).facet a))
            (D.bandCutSideValues q g J T) he _ rfl]
          simp [bandCutSideValues,hk]
          erw [rebaseUnit_trans]
        · have he : bandCutLong (arity:=arity) q (⟨q,none⟩,k)=⟨Sum.inl (q,k),none⟩ := by
            simp [bandCutLong,hk]
          erw [rebaseUnit_index (fun a => D.rank ((D.ports.bandCutPorts q).facet a))
            (D.bandCutSideValues q g J T) he _ rfl]
          simp [bandCutSideValues,hk]
          rfl
      rw [show D.bandCutLongValue q g J T ⟨q,none⟩ = _ from funext hv]
      simp [List.ofFn_succ,bandCutReplacement]
    · have ha : (⟨s,none⟩ : Side S arity) ≠ ⟨q,none⟩ := by
        intro he; exact hs (congrArg Sigma.fst he)
      have hv (k : Fin 3) : D.bandCutLongValue q g J T ⟨s,none⟩ k =
          if k=2 then g (.side ⟨s,none⟩) else 1 := by
        unfold bandCutLongValue
        have he : bandCutLong (arity:=arity) q (⟨s,none⟩,k)=⟨Sum.inl (s,k),none⟩ := by
          simp [bandCutLong,hs]
        erw [rebaseUnit_index (fun a => D.rank ((D.ports.bandCutPorts q).facet a))
          (D.bandCutSideValues q g J T) he _ rfl]
        simp [bandCutSideValues,hs]
        rfl
      rw [show D.bandCutLongValue q g J T ⟨s,none⟩ = _ from funext hv]
      simp only [bandCutReplacement]
      erw [dite_eq_right ha]
      let x : (Matrix (Fin (D.rank (D.ports.facet ⟨s,none⟩)))
          (Fin (D.rank (D.ports.facet ⟨s,none⟩))) A)ˣ := g (.side ⟨s,none⟩)
      change (List.ofFn (fun k : Fin 3 => if k=2 then x else 1)).reverse.prod = x
      simp [List.ofFn_succ]
  | some c =>
    have ha : (⟨s,some c⟩ : Side S arity) ≠ ⟨q,none⟩ := by
      intro he
      have hs : s=q := congrArg Sigma.fst he
      subst s
      have hc : some c=none := eq_of_heq (Sigma.mk.inj_iff.mp he).2
      cases hc
    simp [bandCutLongValue,bandCutLong,bandCutSideValues,bandCutReplacement,ha,Fin.rev]
    let x : (Matrix (Fin (D.rank (D.ports.facet ⟨s,some c⟩)))
        (Fin (D.rank (D.ports.facet ⟨s,some c⟩))) A)ˣ := g (.side ⟨s,some c⟩)
    change (rebaseUnit (rfl : D.rank (D.ports.facet ⟨s,some c⟩) =
        D.rank (D.ports.facet ⟨s,some c⟩)) 1) *
      ((rebaseUnit rfl 1) * (rebaseUnit rfl x)) = x
    simp only [rebaseUnit_refl,one_mul]
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence PortAssembly MatrixExpression
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A]
variable (D : Diagram F S V arity) (q : S) (φ : R →+* A)
variable (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)
variable (J T : D.BandCutUnit (A:=A) q)
variable (h : (f : F) → Fin ((D.bandCutDiagram q).genus f) → Bool →
      (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ)

lemma boundaryEdge_eval_unit (f : F) (b : Fin (D.boundaryCount f))
    (i : Fin (D.boundaryLength f b)) :
    (D.boundaryEdgeWord f b i).eval φ g =
      rebaseUnit (congrArg D.rank (D.boundaryFacet f b i))
        (g (.side (D.boundarySide ⟨f,b,i⟩))) := by
  apply MatrixIso.unit_injective_general
  erw [rebaseUnit_iso]
  exact D.boundaryEdge_iso φ g f b i

lemma bandCutBoundaryEdge_long (f : F) (b : Fin (D.boundaryCount f))
    (i : Fin (D.boundaryLength f b)) (k : Fin 3) :
    ((D.bandCutDiagram q).boundaryEdgeWord f (finSumFinEquiv (.inl b))
      (Fin.cast (D.bandCutBoundaryLength_old q f b).symm (finProdFinEquiv (i,k)))).eval φ
      (D.bandCutValues q g J T h) =
      rebaseUnit (congrArg D.rank (D.boundaryFacet f b i))
        (D.bandCutLongValue q g J T (D.boundarySide ⟨f,b,i⟩) k) := by
  erw [boundaryEdge_eval_unit]
  change rebaseUnit _ (D.bandCutSideValues q g J T _)=_
  unfold bandCutLongValue
  erw [rebaseUnit_trans]
  apply rebaseUnit_index (fun a => D.rank ((D.ports.bandCutPorts q).facet a))
    (D.bandCutSideValues q g J T)
  change D.bandCutBoundarySide q ⟨f,finSumFinEquiv (.inl b),
    Fin.cast (D.bandCutBoundaryLength_old q f b).symm (finProdFinEquiv (i,k))⟩=_
  rw [bandCutBoundarySide_old]
  have he := finProdFinEquiv.symm_apply_apply (i,k)
  exact congrArg (fun p => bandCutLong q (D.boundarySide ⟨f,b,p.1⟩,p.2)) he

lemma bandCutBoundaryWord_long (f : F) (b : Fin (D.boundaryCount f)) :
    ((D.bandCutDiagram q).boundaryWord f (finSumFinEquiv (.inl b))).eval φ
      (D.bandCutValues q g J T h) =
      (List.ofFn (fun i => rebaseUnit (congrArg D.rank (D.boundaryFacet f b i))
        (D.bandCutReplacement q g J (D.boundarySide ⟨f,b,i⟩)))).reverse.prod := by
  erw [boundaryWord_eval_raw]
  erw [List.ofFn_congr (D.bandCutBoundaryLength_old q f b)]
  erw [SurfaceSurgery.ofFn_reverse_prod_blocks]
  apply congrArg (fun v : Fin (D.boundaryLength f b) →
      (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ => (List.ofFn v).reverse.prod)
  funext i
  have he := funext (fun k : Fin 3 => D.bandCutBoundaryEdge_long q φ g J T h f b i k)
  erw [he]
  have hh := map_list_prod (rebaseUnit (congrArg D.rank (D.boundaryFacet f b i)))
    (List.ofFn (D.bandCutLongValue q g J T (D.boundarySide ⟨f,b,i⟩))).reverse
  rw [D.bandCutLongValue_triple q g J T] at hh
  simp only [List.map_reverse,List.map_ofFn,Function.comp_def] at hh
  convert! hh.symm using 1
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence PortAssembly MatrixExpression
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A]
variable (D : Diagram F S V arity) (q : S) (φ : R →+* A)
variable (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)
variable (J T : D.BandCutUnit (A:=A) q)
variable (h : (f : F) → Fin ((D.bandCutDiagram q).genus f) → Bool →
      (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ)

lemma bandCutBoundaryEdge_short (j : Fin (D.bandCutExtra q (D.bandCutParent q))) (i : Fin 2) :
    ((D.bandCutDiagram q).boundaryEdgeWord (D.bandCutParent q) (finSumFinEquiv (.inr j))
      (Fin.cast (D.bandCutBoundaryLength_new q _ j).symm i)).eval φ
        (D.bandCutValues q g J T h) =
    if i=0 then rebaseUnit (D.seamRank q).symm (T⁻¹*J⁻¹*D.bandCutP q g*T) else 1 := by
  erw [boundaryEdge_eval_unit]
  change rebaseUnit _ (D.bandCutSideValues q g J T _)=_
  have he := D.bandCutBoundarySide_new q (D.bandCutParent q) j i
  erw [rebaseUnit_index (fun a => D.rank ((D.ports.bandCutPorts q).facet a))
    (D.bandCutSideValues q g J T) he _ (congrArg D.rank (D.ports.bandCutShort_facet q i))]
  fin_cases i
  · change rebaseUnit _ (D.bandCutSideValues q g J T ⟨Sum.inl (q,1),none⟩)=_
    simp only [bandCutSideValues]
    rfl
  · change rebaseUnit _ (D.bandCutSideValues q g J T ⟨Sum.inr (),none⟩)=_
    simp [bandCutSideValues]

lemma bandCutBoundaryWord_short (j : Fin (D.bandCutExtra q (D.bandCutParent q))) :
    ((D.bandCutDiagram q).boundaryWord (D.bandCutParent q) (finSumFinEquiv (.inr j))).eval φ
        (D.bandCutValues q g J T h) =
      rebaseUnit (D.seamRank q).symm (T⁻¹*J⁻¹*D.bandCutP q g*T) := by
  erw [boundaryWord_eval_raw,List.ofFn_congr (D.bandCutBoundaryLength_new q _ j)]
  have he := funext (fun i : Fin 2 => D.bandCutBoundaryEdge_short q φ g J T h j i)
  erw [he]
  let x : (Matrix (Fin (D.rank (D.bandCutParent q)))
      (Fin (D.rank (D.bandCutParent q))) A)ˣ :=
    rebaseUnit (D.seamRank q).symm (T⁻¹*J⁻¹*D.bandCutP q g*T)
  change (List.ofFn (fun i : Fin 2 => if i=0 then x else 1)).reverse.prod = x
  simp [List.ofFn_succ]
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence PortAssembly MatrixExpression
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A]
variable (D : Diagram F S V arity) (q : S) (φ : R →+* A)
variable (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)
variable (J T : D.BandCutUnit (A:=A) q)
variable (h : (f : F) → Fin ((D.bandCutDiagram q).genus f) → Bool →
      (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ)

/-- The ordered prefix preceding a chosen boundary occurrence. -/
def boundaryPrefix (f : F) (b : Fin (D.boundaryCount f)) (i : Fin (D.boundaryLength f b)) :=
  ((List.ofFn fun j => (D.boundaryEdgeWord f b j).eval φ g).take i.val).reverse.prod

def boundaryTail (f : F) (b : Fin (D.boundaryCount f)) (i : Fin (D.boundaryLength f b)) :=
  ((List.ofFn fun j => (D.boundaryEdgeWord f b j).eval φ g).drop (i.val+1)).reverse.prod

lemma boundaryWord_split (f : F) (b : Fin (D.boundaryCount f)) (i : Fin (D.boundaryLength f b)) :
    (D.boundaryWord f b).eval φ g =
      D.boundaryTail φ g f b i*(D.boundaryEdgeWord f b i).eval φ g*D.boundaryPrefix φ g f b i := by
  erw [boundaryWord_eval_raw]
  exact SurfaceSurgery.ofFn_reverse_replace _ _ i _ (fun _ _ => rfl) rfl

variable (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
variable (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))
variable (hb : D.boundarySide ⟨D.bandCutParent q,b0,i0⟩=⟨q,none⟩)
include hb

lemma bandCut_other_side {j : Fin (D.boundaryLength (D.bandCutParent q) b0)} (hj : j≠i0) :
    D.boundarySide ⟨D.bandCutParent q,b0,j⟩ ≠ ⟨q,none⟩ := by
  intro he
  have hp := D.boundarySide.injective (he.trans hb.symm)
  apply hj
  simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using hp

lemma bandCut_other_circle (f : F) (b : Fin (D.boundaryCount f))
    (hne : (⟨f,b⟩ : D.BoundaryCircle) ≠ ⟨D.bandCutParent q,b0⟩)
    (i : Fin (D.boundaryLength f b)) : D.boundarySide ⟨f,b,i⟩ ≠ ⟨q,none⟩ := by
  intro he
  have hp := D.boundarySide.injective (he.trans hb.symm)
  exact hne (congrArg (fun p => (⟨p.1,p.2.1⟩ : D.BoundaryCircle)) hp)

lemma bandCutChosenEdge : (D.boundaryEdgeWord (D.bandCutParent q) b0 i0).eval φ g =
    rebaseUnit (D.seamRank q).symm (D.bandCutP q g) := by
  erw [boundaryEdge_eval_unit]
  erw [rebaseUnit_index (fun a => D.rank (D.ports.facet a))
    (fun a => g (.side a)) hb _ rfl]
  unfold bandCutP
  erw [rebaseUnit_trans]

lemma bandCutBoundaryWord_selected :
    ((D.bandCutDiagram q).boundaryWord (D.bandCutParent q) (finSumFinEquiv (.inl b0))).eval φ
      (D.bandCutValues q g J T h) =
    D.boundaryTail φ g (D.bandCutParent q) b0 i0*
      rebaseUnit (D.seamRank q).symm J*D.boundaryPrefix φ g (D.bandCutParent q) b0 i0 := by
  erw [bandCutBoundaryWord_long]
  apply SurfaceSurgery.ofFn_reverse_replace _ _ i0
  · intro j hj
    erw [bandCutReplacement,dite_eq_right (D.bandCut_other_side q b0 i0 hb hj)]
    exact (D.boundaryEdge_eval_unit φ g _ _ _).symm
  · erw [rebaseUnit_index (fun a => D.rank (D.ports.facet a))
      (D.bandCutReplacement q g J) hb _ rfl]
    simp only [bandCutReplacement]
    erw [dite_eq_left rfl,rebaseUnit_trans]

lemma bandCutBoundaryWord_other (f : F) (b : Fin (D.boundaryCount f))
    (hne : (⟨f,b⟩ : D.BoundaryCircle) ≠ ⟨D.bandCutParent q,b0⟩) :
    ((D.bandCutDiagram q).boundaryWord f (finSumFinEquiv (.inl b))).eval φ
      (D.bandCutValues q g J T h) = (D.boundaryWord f b).eval φ g := by
  erw [bandCutBoundaryWord_long,boundaryWord_eval_raw]
  apply congrArg (fun v : Fin (D.boundaryLength f b) →
      (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ => (List.ofFn v).reverse.prod)
  funext i
  erw [bandCutReplacement,dite_eq_right (D.bandCut_other_circle q b0 i0 hb f b hne i)]
  exact (D.boundaryEdge_eval_unit φ g f b i).symm
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
