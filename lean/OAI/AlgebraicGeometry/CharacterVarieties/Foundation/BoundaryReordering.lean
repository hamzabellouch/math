import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.CornerGauge

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.SurfaceSurgery
open scoped Classical
variable {I G : Type*} [Group G]

lemma list_prod_pointwise_conjugation (l : List I) (f : I → G) (z : G) :
    (l.map (fun i => z*f i*z⁻¹)).prod=z*(l.map f).prod*z⁻¹ := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons,List.prod_cons,ih]; group

/-- Each reordering admits basing paths preserving the total boundary word. circle labels are
distinct; equal facet labels are irrelevant. -/
theorem reorder_by_based_paths {l m : List I} (hp : l.Perm m) (hn : l.Nodup)
    (f : I → G) :
    ∃ z : I → G, (m.map (fun i => z i*f i*(z i)⁻¹)).prod=(l.map f).prod := by
  classical
  induction hp generalizing f with
  | nil => exact ⟨fun _ => 1,rfl⟩
  | @cons a l m hp ih =>
    have hna := List.nodup_cons.mp hn
    obtain ⟨z,hz⟩ := ih hna.2 f
    refine ⟨fun i => if i=a then 1 else z i,?_⟩
    have he : m.map (fun i => (if i=a then 1 else z i)*f i*(if i=a then 1 else z i)⁻¹)=
        m.map (fun i => z i*f i*(z i)⁻¹) := by
      apply List.map_congr_left
      intro i hi
      have hia : i≠a := by
        intro h
        subst i
        exact hna.1 (hp.mem_iff.mpr hi)
      simp only [ite_eq_right hia]
    simp only [List.map_cons,List.prod_cons,he,hz]
    simp
  | swap a b l =>
    have hba : b≠a := by
      intro h
      exact (List.nodup_cons.mp hn).1 (by simp [h])
    have hbl : b∉l := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
    refine ⟨fun i => if i=b then (f a)⁻¹ else 1,?_⟩
    have he : l.map (fun i => (if i=b then (f a)⁻¹ else 1)*f i*
        (if i=b then (f a)⁻¹ else 1)⁻¹)=l.map f := by
      apply List.map_congr_left
      intro i hi
      have hib : i≠b := by rintro rfl; exact hbl hi
      simp [hib]
    simp only [List.map_cons,List.prod_cons,ite_eq_right hba.symm,
      one_mul,inv_one,mul_one,he]
    simp only [ite_true]
    group
  | @trans l m n hp hq ihp ihq =>
    obtain ⟨z,hz⟩ := ihp hn f
    obtain ⟨w,hw⟩ := ihq (hp.nodup_iff.mp hn) (fun i => z i*f i*(z i)⁻¹)
    refine ⟨fun i => w i*z i,?_⟩
    rw [← hz,← hw]
    congr 2
    funext i
    group

/-- Chosen paths may be words in the old boundary generators. Their images under evaluation work in
every group and over every coefficient ring. -/
theorem reorder_by_words {l m : List I} (hp : l.Perm m) (hn : l.Nodup) :
    ∃ z : I → FreeGroup I,
      ∀ {H : Type*} [Group H] (f : I → H),
        (m.map (fun i => (FreeGroup.lift f) (z i)*f i*
          ((FreeGroup.lift f) (z i))⁻¹)).prod=(l.map f).prod := by
  obtain ⟨z,hz⟩ := reorder_by_based_paths hp hn (FreeGroup.of : I → FreeGroup I)
  refine ⟨z,?_⟩
  intro H _ f
  have h := congrArg (FreeGroup.lift f) hz
  simpa only [map_list_prod,List.map_map,Function.comp_def,map_mul,map_inv,
    FreeGroup.lift_apply_of] using h
end IntegralCharacterVarieties.SurfaceSurgery

namespace IntegralCharacterVarieties.SurfaceSurgery
/-- The based words are chosen from the enumeration alone, before evaluating any old solution or any
coefficient ring. -/
theorem fin_reorder_by_words {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ∃ z : Fin n → FreeGroup (Fin n),
      ∀ {H : Type*} [Group H] (f : Fin n → H),
        (List.ofFn (fun b => (FreeGroup.lift f) (z (σ b))*f (σ b)*
          ((FreeGroup.lift f) (z (σ b)))⁻¹)).prod=(List.ofFn f).prod := by
  have hn : (List.ofFn (fun i : Fin n => i)).Nodup := List.nodup_ofFn.mpr Function.injective_id
  have hm : (List.ofFn σ).Nodup := List.nodup_ofFn.mpr σ.injective
  have hp : (List.ofFn (fun i : Fin n => i)).Perm (List.ofFn σ) := by
    apply (List.perm_ext_iff_of_nodup hn hm).mpr
    intro a
    simp only [List.mem_ofFn]
    exact ⟨fun _ => σ.surjective a,fun _ => ⟨a,rfl⟩⟩
  obtain ⟨z,hz⟩ := reorder_by_words hp hn
  refine ⟨z,?_⟩
  intro H _ f
  simpa only [List.map_ofFn,Function.comp_def] using hz f
end IntegralCharacterVarieties.SurfaceSurgery

namespace IntegralCharacterVarieties.MatrixExpression
open scoped Classical Matrix
variable {R A E : Type*} [CommRing R] [CommRing A] {r : E → ℕ}
lemma Term.eval_transport_iso (φ : R →+* A)
    (g : (e : E) → (Matrix (Fin (r e)) (Fin (r e)) A)ˣ)
    {n m : ℕ} (h : n=m) (t : Term R E r n) :
    MatrixIso.unit ((h ▸ t).eval φ g)=
      (MatrixIso.unit (t.eval φ g)).reindex (finCongr h.symm) (finCongr h.symm) := by
  subst m
  simp only [finCongr_refl,MatrixIso.reindex_refl_eq]
end IntegralCharacterVarieties.MatrixExpression

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A]
variable (D : Diagram F S V arity) (φ : R →+* A)
variable (G : D.CircleBases (R:=A))
variable (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)

lemma wordProduct_eval_raw {n : ℕ} (L : List (D.Word R n)) :
    (D.wordProduct L).eval φ g=(L.map (fun t => t.eval φ g)).prod := by
  induction L with
  | nil => simp [wordProduct,Term.eval,mapUnit]
  | cons x xs ih =>
    simpa only [wordProduct,List.foldr_cons,Term.eval,List.map_cons,List.prod_cons] using
      congrArg (fun z => x.eval φ g*z) ih

lemma boundaryWord_eval_raw (f : F) (b : Fin (D.boundaryCount f)) :
    (D.boundaryWord f b).eval φ g=
      ((List.ofFn (fun i => (D.boundaryEdgeWord f b i).eval φ g)).reverse).prod := by
  rw [boundaryWord,D.wordProduct_eval_raw,List.map_reverse,List.map_ofFn]
  rfl

lemma boundaryEdge_iso (f : F) (b : Fin (D.boundaryCount f))
    (i : Fin (D.boundaryLength f b)) :
    MatrixIso.unit ((D.boundaryEdgeWord f b i).eval φ g)=
      (MatrixIso.unit (g (.side (D.boundarySide ⟨f,b,i⟩)))).reindex
        (finCongr (congrArg D.rank (D.boundaryFacet f b i)).symm)
        (finCongr (congrArg D.rank (D.boundaryFacet f b i)).symm) := by
  unfold boundaryEdgeWord
  exact Term.eval_transport_iso φ g (congrArg D.rank (D.boundaryFacet f b i))
    (D.sideWord (D.boundarySide ⟨f,b,i⟩))

lemma sideBasis_boundary (f : F) (b : Fin (D.boundaryCount f))
    (i : Fin (D.boundaryLength f b)) :
    (D.sideBasis G (D.boundarySide ⟨f,b,i⟩)).reindex
      (finCongr (congrArg D.rank (D.boundaryFacet f b i)).symm)
      (finCongr (congrArg D.rank (D.boundaryFacet f b i)).symm)=G ⟨f,b⟩ := by
  have h := MatrixIso.finite_basis_transport (fun B : D.BoundaryCircle => D.rank B.1) G
    ⟨f,b⟩ (D.sideCircle (D.boundarySide ⟨f,b,i⟩))
    (D.rank f) (D.rank (D.ports.facet (D.boundarySide ⟨f,b,i⟩)))
    rfl (congrArg D.rank (D.sideCircle_facet (D.boundarySide ⟨f,b,i⟩)).symm)
    (D.sideCircle_boundary f b i).symm (congrArg D.rank (D.boundaryFacet f b i)).symm
  simpa only [sideBasis,finCongr_refl,MatrixIso.reindex_refl_eq] using h

lemma boundaryEdge_gauge (f : F) (b : Fin (D.boundaryCount f))
    (i : Fin (D.boundaryLength f b)) :
    (D.boundaryEdgeWord f b i).eval φ (D.gaugeGenerators G g)=
      (G ⟨f,b⟩).toUnit*(D.boundaryEdgeWord f b i).eval φ g*((G ⟨f,b⟩).toUnit)⁻¹ := by
  have h := D.boundaryEdge_iso φ (D.gaugeGenerators G g) f b i
  rw [show MatrixIso.unit ((D.gaugeGenerators G g) (.side (D.boundarySide ⟨f,b,i⟩)))=
      (((D.sideBasis G (D.boundarySide ⟨f,b,i⟩)).symm.trans
        (MatrixIso.unit (g (.side (D.boundarySide ⟨f,b,i⟩))))).trans
        (D.sideBasis G (D.boundarySide ⟨f,b,i⟩))) by
          unfold gaugeGenerators
          erw [MatrixIso.unit_toUnit]] at h
  erw [MatrixIso.bases_reindex,D.sideBasis_boundary,← D.boundaryEdge_iso φ g] at h
  apply Units.ext
  have hh := congrArg MatrixIso.val h
  change _=(G ⟨f,b⟩).val*
    (((D.boundaryEdgeWord f b i).eval φ g) : Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)*
      (G ⟨f,b⟩).inv
  simpa only [MatrixIso.unit,MatrixIso.trans,MatrixIso.symm,MatrixIso.toUnit,
    Units.val_mul,Units.val_inv,Matrix.mul_assoc] using hh

lemma boundaryWord_gauge (f : F) (b : Fin (D.boundaryCount f)) :
    (D.boundaryWord f b).eval φ (D.gaugeGenerators G g)=
      (G ⟨f,b⟩).toUnit*(D.boundaryWord f b).eval φ g*((G ⟨f,b⟩).toUnit)⁻¹ := by
  rw [D.boundaryWord_eval_raw,D.boundaryWord_eval_raw]
  simp_rw [D.boundaryEdge_gauge]
  have h := SurfaceSurgery.list_prod_pointwise_conjugation
    ((List.ofFn (fun i : Fin (D.boundaryLength f b) => i)).reverse)
    (fun i => (D.boundaryEdgeWord f b i).eval φ g) ((G ⟨f,b⟩).toUnit)
  simpa only [List.map_reverse,List.map_ofFn,Function.comp_def] using h
end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.SurfaceSurgery
variable {G : Type*} [Group G]

/-- Directed multiplication with wholly independent intermediate bases. -/
lemma reverse_product_gauge (b e : ℕ → G) (n : ℕ) :
    (List.ofFn (fun i : Fin n => b (i.val+1)*e i.val*(b i.val)⁻¹)).reverse.prod=
      b n*(List.ofFn (fun i : Fin n => e i.val)).reverse.prod*(b 0)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ',List.concat_eq_append,List.reverse_concat,List.prod_cons]
    rw [List.ofFn_succ' (fun i : Fin (n+1) => e i.val),List.concat_eq_append,List.reverse_concat,List.prod_cons]
    simp only [Fin.val_castSucc,Fin.val_last]
    rw [ih]
    group

lemma cyclic_reverse_product_gauge (n : ℕ) (hn : 0<n) (b e : Fin n → G) :
    (List.ofFn (fun i : Fin n => b ⟨(i.val+1)%n,Nat.mod_lt _ hn⟩*e i*(b i)⁻¹)).reverse.prod=
      b ⟨0,hn⟩*(List.ofFn e).reverse.prod*(b ⟨0,hn⟩)⁻¹ := by
  have h := reverse_product_gauge (fun i => b ⟨i%n,Nat.mod_lt _ hn⟩)
    (fun i => e ⟨i%n,Nat.mod_lt _ hn⟩) n
  simpa only [Nat.mod_self,Nat.zero_mod,Fin.eta,Nat.mod_eq_of_lt (Fin.isLt _)] using h
end IntegralCharacterVarieties.SurfaceSurgery

end

end OAI
