import Mathlib
import OAI.CategoryTheory.Thomason.CylinderWeights
import OAI.CategoryTheory.Thomason.IntervalExtension

namespace OAI

/-! Standard Comparison. -/

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma table_functor_ext {n : ℕ} {M : DirectedComplex.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu M.nu)
    (hend : ∀ a x, F.map (atEnd a x) = G.map (atEnd a x))
    (hvert : ∀ r a b,
      (F.map (verticalTable (truncate r a (topTable n)))).row (r+1) b =
      (G.map (verticalTable (truncate r a (topTable n)))).row (r+1) b) : F = G := by
  have he (p : ℕ) (x : Table (K.{u} n)) (hx : truncate p false x = x) :
      ∀ b, (F.map x).row p b = (G.map x).row p b := by
    apply generated_bounded n p (fun z => ∀ b, (F.map z).row p b = (G.map z).row p b)
      (fun a x hx b => congrArg (fun z : Table M => z.row p b) (hend a x)) ?_ ?_ x hx
    · intro r hr t ht b
      obtain ⟨d,a,_,hdr,ht'⟩ := bounded_table_classification t ht
      have hb : truncate d false t = t := by rw [ht']; simp only [truncate_truncate,lt_self_iff_false,ite_false]
      have hF : truncate (d+1) false (F.map (verticalTable t)) = F.map (verticalTable t) :=
        (F.map_source (d+1) _).symm.trans (congrArg F.map (vertical_fixed t hb))
      have hG : truncate (d+1) false (G.map (verticalTable t)) = G.map (verticalTable t) :=
        (G.map_source (d+1) _).symm.trans (congrArg G.map (vertical_fixed t hb))
      by_cases hp : d+1 < p
      · rw [row_above_fixed _ hF hp, row_above_fixed _ hG hp]
      · have hp' : p = d+1 := by omega
        rw [hp',ht']
        exact hvert d a b
    · intro l s t h hs ht b
      have hf := F.map_comp l s t h (F.map_composable h)
      have hg := G.map_comp l s t h (G.map_composable h)
      change F.map (DirectedComplex.Table.comp l s t h) = DirectedComplex.Table.comp l _ _ (F.map_composable h) at hf
      change G.map (DirectedComplex.Table.comp l s t h) = DirectedComplex.Table.comp l _ _ (G.map_composable h) at hg
      erw [hf,hg,comp_row,comp_row]
      split_ifs <;> simp only [hs,ht]
  apply OmegaCategory.Functor.ext
  funext x
  change Table (K.{u} n) at x
  apply DirectedComplex.Table.ext
  funext p b
  have h := he p (truncate p b x) (by simp only [truncate_truncate,lt_self_iff_false,ite_false]) false
  have hf : F.map (truncate p b x) = truncate p b (F.map x) := by
    cases b <;> first | exact F.map_source p x | exact F.map_target p x
  have hg : G.map (truncate p b x) = truncate p b (G.map x) := by
    cases b <;> first | exact G.map_source p x | exact G.map_target p x
  rw [hf,hg] at h
  erw [truncate_row,truncate_row] at h
  simpa only [lt_self_iff_false,ite_false,ite_true] using h

def tableCylinder {M : DirectedComplex.{v}} (n : ℕ) (t : Table M) :
    OmegaCategory.Functor (K.{u} n).nu M.cylinder.nu := (tableMap n t).cylinder.nu

lemma tableCylinder_endpoint {M : DirectedComplex.{v}} (n : ℕ) (t : Table M)
    (a : Bool) (x : Table (complex.{u} n)) :
    (tableCylinder n t).map (atEnd a x) = (M.cylinderEndpoint a).nu.map ((tableMap n t).nu.map x) := by
  exact congrArg (fun h => h.nu.map x) (Hom.cylinder_endpoint (tableMap n t) a)

lemma tableCylinder_endpoint_top {M : DirectedComplex.{v}} (n : ℕ) (t : Table M) (a : Bool) :
    (tableCylinder.{u,v} n t).map (atEnd a (topTable n)) = (M.cylinderEndpoint a).nu.map (truncate n false t) := by
  rw [tableCylinder_endpoint, tableMap_nu_top]

lemma tableCylinder_vertical {M : DirectedComplex.{v}} (n : ℕ) (t : Table M) :
    (tableCylinder.{u,v} n t).map (verticalTable (topTable n)) = verticalTable (truncate n false t) :=
  (verticalTable_natural (tableMap n t) (topTable n)).trans (congrArg verticalTable (tableMap_nu_top n t))

lemma tableCylinder_restrict {M : DirectedComplex.{v}} (n : ℕ) (t : Table M)
    (ht : truncate n false t = t) (i : ℕ) (b : Bool) :
    restrictCylinder i b (tableCylinder.{u,v} n t) = tableCylinder i (truncate i b t) := by
  have he : Hom.comp (faceMap.{u} n i b) (tableMap.{u,v} n t) = tableMap i (truncate i b t) := by
    apply GlobeComplex.hom_ext
    change (tableMap n t).nu.map ((faceMap n i b).nu.map (topTable i)) = _
    erw [faceMap_top, ← face_nu, OmegaCategory.Functor.map_face, tableMap_nu_top, ht]
    rw [tableMap_nu_top]
    cases b <;> change truncate i _ t = truncate i false (truncate i _ t)
    all_goals simp only [truncate_truncate,lt_self_iff_false,ite_false]
  change (Hom.comp (faceMap n i b).cylinder (tableMap n t).cylinder).nu = _
  rw [← Hom.cylinder_comp,he]
  rfl

lemma tableCylinder_matching {M : DirectedComplex.{v}} {n k : ℕ} {x y : Table M}
    (hx : truncate n false x = x) (hy : truncate n false y = y)
    (h : truncate k true x = truncate k false y) :
    FaceMatching k (tableCylinder.{u,v} n x) (tableCylinder n y) := by
  intro z
  have he : restrictCylinder k true (tableCylinder.{u,v} n x) =
      restrictCylinder k false (tableCylinder.{u,v} n y) := by
    rw [tableCylinder_restrict n x hx, tableCylinder_restrict n y hy,h]
  exact congrArg (fun P => P.map z) he

lemma vertical_top_row {M : DirectedComplex.{v}} {n : ℕ} (x : Table M)
    (hx : truncate n false x = x) (b : Bool) :
    (verticalTable x).row (n+1) b = (0,0,x.row n false) := by
  have h₀ := row_above_fixed x hx (by omega : n < n+1)
  have h₁ : x.row n true = x.row n false := by
    have he := congrArg (fun t : Table M => t.row n true) hx
    simpa only [truncate_row, lt_self_iff_false, ite_false, ite_true] using he.symm
  cases b <;> simp [verticalTable,verticalRow,h₀,h₁]

lemma table_comp_bounded {M : DirectedComplex.{v}} {n k : ℕ} (hk : k < n)
    (x y : Table M) (hx : truncate n false x = x) (hy : truncate n false y = y)
    (h : truncate k true x = truncate k false y) :
    truncate n false (DirectedComplex.Table.comp k x y h) = DirectedComplex.Table.comp k x y h := by
  apply fixed_of_rows_zero
  intro p hp b
  rw [comp_row]
  simp only [show ¬p < k by omega, show p ≠ k by omega, ite_false,
    row_above_fixed x hx hp, row_above_fixed y hy hp, add_zero]

lemma restrictCylinder_vertical_top {n i : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) (b : Bool) :
    (restrictCylinder i b F).map (verticalTable (topTable i)) =
      F.map (verticalTable (truncate i b (topTable n))) := by
  change F.map ((faceMap n i b).cylinder.nu.map (verticalTable (topTable i))) = _
  rw [verticalTable_natural,faceMap_top]

lemma tableCylinder_comp {M : DirectedComplex.{v}} {n k : ℕ} (hk : k < n)
    (x y : Table M) (hx : truncate n false x = x) (hy : truncate n false y = y)
    (h : truncate k true x = truncate k false y) :
    pasteCylinder hk (tableCylinder.{u,v} n x) (tableCylinder n y) (tableCylinder_matching hx hy h) =
      tableCylinder n (DirectedComplex.Table.comp k x y h) := by
  have hz := table_comp_bounded hk x y hx hy h
  apply table_functor_ext
  · intro a t
    have he : endGlobe (pasteCylinder hk (tableCylinder.{u,v} n x) (tableCylinder n y)
        (tableCylinder_matching hx hy h)) a =
        endGlobe (tableCylinder n (DirectedComplex.Table.comp k x y h)) a := by
      apply GlobeComplex.functor_ext
      change (pasteCylinder hk _ _ _).map (atEnd a (topTable n)) = _
      rw [pasteCylinder_endpoint_top,tableCylinder_endpoint_top,tableCylinder_endpoint_top,hx,hy]
      change M.cylinder.nu.join k ((M.cylinderEndpoint a).nu.map x) ((M.cylinderEndpoint a).nu.map y) =
        (tableCylinder n (DirectedComplex.Table.comp k x y h)).map (atEnd a (topTable n))
      rw [tableCylinder_endpoint_top,hz, ← (M.cylinderEndpoint a).nu.map_join k x y h, M.nu.join_eq k x y h]
      rfl
    exact congrArg (fun P => P.map t) he
  · intro r a b
    rw [← restrictCylinder_vertical_top, ← restrictCylinder_vertical_top]
    by_cases hr : r ≤ k
    · rw [pasteCylinder_lower_face n k r hk hr]
      cases a <;> simp only [Bool.false_eq_true,ite_false,ite_true]
      · rw [tableCylinder_restrict _ _ hx,tableCylinder_restrict _ _ hz,source_comp_le r k hr]
      · rw [tableCylinder_restrict _ _ hy,tableCylinder_restrict _ _ hz,target_comp_le r k hr]
    · have hkr : k < r := by omega
      rw [pasteCylinder_restrict_gt n k r hk hkr]
      have hw := pasteCylinder_weight r k hkr (CellWeight.row M.cylinder (r+1) b)
        (restrictCylinder r a (tableCylinder.{u,v} n x))
        (restrictCylinder r a (tableCylinder.{u,v} n y)) ((tableCylinder_matching hx hy h).restrict hkr a)
      change ((pasteCylinder hkr (restrictCylinder r a (tableCylinder.{u,v} n x))
        (restrictCylinder r a (tableCylinder.{u,v} n y))
        ((tableCylinder_matching hx hy h).restrict hkr a)).map (verticalTable (topTable r))).row (r+1) b =
        ((restrictCylinder r a (tableCylinder.{u,v} n x)).map (verticalTable (topTable r))).row (r+1) b +
        ((restrictCylinder r a (tableCylinder.{u,v} n y)).map (verticalTable (topTable r))).row (r+1) b at hw
      rw [hw,tableCylinder_restrict _ _ hx,tableCylinder_restrict _ _ hy,tableCylinder_restrict _ _ hz,
        tableCylinder_vertical,tableCylinder_vertical,tableCylinder_vertical]
      have hfix (z : Table M) : truncate r false (truncate r a z) = truncate r a z := by
        simp only [truncate_truncate,lt_self_iff_false,ite_false]
      rw [hfix,hfix,hfix,vertical_top_row _ (hfix x),vertical_top_row _ (hfix y),
        vertical_top_row _ (hfix (DirectedComplex.Table.comp k x y h))]
      simp only [truncate_row,lt_self_iff_false,ite_false,ite_true,comp_row,
        show ¬r < k by omega, show r ≠ k by omega, Prod.mk_add_mk, zero_add]
end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable {M N : DirectedComplex.{u}}

def tableCell (x : Table M) : Cell M.cylinder.nu :=
  ofMap (tableCylinder (M.nu.finite_dimension x).choose x)

lemma tableCell_of_bounded (n : ℕ) (x : Table M) (hx : truncate n false x = x) :
    tableCell x = ofMap (tableCylinder n x) := by
  apply Subtype.ext
  funext j
  change restrictCylinder j false (tableCylinder (M.nu.finite_dimension x).choose x) =
    restrictCylinder j false (tableCylinder n x)
  rw [tableCylinder_restrict _ _ (M.nu.finite_dimension x).choose_spec,
    tableCylinder_restrict _ _ hx]

lemma tableCell_face (i : ℕ) (b : Bool) (x : Table M) :
    tableCell (truncate i b x) = face i b (tableCell x) := by
  obtain ⟨n,hn⟩ := M.nu.finite_dimension x
  rw [tableCell_of_bounded n x hn,face_ofMap,tableCylinder_restrict n x hn,
    tableCell_of_bounded i (truncate i b x) (by simp only [truncate_truncate,lt_self_iff_false,ite_false])]

lemma tableCell_comp (k : ℕ) (x y : Table M) (h : truncate k true x = truncate k false y)
    (h' : face k true (tableCell x) = face k false (tableCell y)) :
    tableCell (DirectedComplex.Table.comp k x y h) = comp k (tableCell x) (tableCell y) h' := by
  obtain ⟨n₁,h₁⟩ := M.nu.finite_dimension x
  obtain ⟨n₂,h₂⟩ := M.nu.finite_dimension y
  let n := max (k+1) (max n₁ n₂)
  have hk : k < n := by omega
  have hx : truncate n false x = x := M.nu.source_fixed_upwards (by omega) h₁
  have hy : truncate n false y = y := M.nu.source_fixed_upwards (by omega) h₂
  clear_value n
  simp only [tableCell_of_bounded n x hx,tableCell_of_bounded n y hy] at h' ⊢
  rw [comp_ofMap hk]
  rw [tableCell_of_bounded n _ (table_comp_bounded hk x y hx hy h)]
  exact congrArg ofMap (tableCylinder_comp hk x y hx hy h).symm

def chainDiagram (M : DirectedComplex.{u}) : M.nu ⟶ omegaCategory M.cylinder.nu where
  map := tableCell
  map_source k x := tableCell_face k false x
  map_target k x := tableCell_face k true x
  map_comp k x y h h' := tableCell_comp k x y h h'

lemma tableCylinder_map (a : Hom M N) (n : ℕ) (x : Table M) :
    OmegaCategory.Functor.comp (tableCylinder n x) a.cylinder.nu = tableCylinder n (a.nu.map x) := by
  have he : Hom.comp (tableMap n x) a = tableMap n (a.nu.map x) := by
    apply GlobeComplex.hom_ext
    change a.nu.map ((tableMap n x).nu.map (topTable n)) = _
    erw [tableMap_nu_top,tableMap_nu_top]
    exact a.nu.map_source n x
  change (Hom.comp (tableMap n x).cylinder a.cylinder).nu = _
  rw [← Hom.cylinder_comp,he]
  rfl

lemma tableCell_map (a : Hom M N) (x : Table M) :
    mapCell a.cylinder.nu (tableCell x) = tableCell (a.nu.map x) := by
  obtain ⟨n,hn⟩ := M.nu.finite_dimension x
  have hm : truncate n false (a.nu.map x) = a.nu.map x :=
    (a.nu.map_source n x).symm.trans (congrArg a.nu.map hn)
  rw [tableCell_of_bounded n x hn,mapCell_ofMap,tableCylinder_map,
    tableCell_of_bounded n (a.nu.map x) hm]

lemma chainDiagram_natural (a : Hom M N) :
    a.nu ≫ chainDiagram N = chainDiagram M ≫ functor.map a.cylinder.nu :=
  OmegaCategory.Functor.ext (funext fun x => (tableCell_map a x).symm)

def chainComparison (M : DirectedComplex.{u}) : tensorFunctor.obj M.nu ⟶ M.cylinder.nu :=
  uncurry (chainDiagram M)

lemma chainComparison_generator (M : DirectedComplex.{u}) (n : ℕ) (x : M.nu.Cells n) (z : (K.{u} n).nu.Cell) :
    (chainComparison M).map ((tensorPresentation M.nu).generator ⟨n,x,z⟩) = (tableCylinder n x.val).map z := by
  change (eval n (tableCell x.val)).map z = _
  rw [tableCell_of_bounded n x.val x.property,eval_ofMap_self]

lemma chainComparison_natural (a : Hom M N) :
    tensorFunctor.map a.nu ≫ chainComparison N = chainComparison M ≫ a.cylinder.nu := by
  apply (tensorPresentation M.nu).functor_ext
  intro ⟨n,x,z⟩
  change (chainComparison N).map ((tensorFunctor.map a.nu).map ((tensorPresentation M.nu).generator ⟨n,x,z⟩)) =
    a.cylinder.nu.map ((chainComparison M).map ((tensorPresentation M.nu).generator ⟨n,x,z⟩))
  erw [tensorFunctor_map_generator,chainComparison_generator,chainComparison_generator]
  exact congrArg (fun P => P.map z) (tableCylinder_map a n x.val).symm

lemma chainComparison_endpoint (M : DirectedComplex.{u}) (b : Bool) :
    (tensorEndpoint b).app M.nu ≫ chainComparison M = (M.cylinderEndpoint b).nu := by
  apply OmegaCategory.Functor.ext
  funext x
  obtain ⟨n,hn⟩ := M.nu.finite_dimension x
  change (chainComparison M).map (((tensorEndpoint b).app M.nu).map x) = _
  erw [tensorEndpoint_bounded b M.nu n ⟨x,hn⟩,chainComparison_generator,
    tableCylinder_endpoint_top]
  exact congrArg (M.cylinderEndpoint b).nu.map hn

lemma chainComparison_projection (M : DirectedComplex.{u}) :
    chainComparison M ≫ M.cylinderProjection.nu = tensorProjection.app M.nu := by
  apply (tensorPresentation M.nu).functor_ext
  intro ⟨n,x,z⟩
  change M.cylinderProjection.nu.map ((chainComparison M).map ((tensorPresentation M.nu).generator ⟨n,x,z⟩)) = _
  rw [chainComparison_generator,tensorProjection_generator]
  have he := congrArg (fun a => a.nu.map z) (Hom.cylinder_projection (tableMap n x.val))
  change M.cylinderProjection.nu.map ((tableCylinder n x.val).map z) = (tableMap n x.val).nu.map (project z) at he
  rw [he,tableMap_nu x.val x.property]

lemma chainComparison_globe (n : ℕ) : chainComparison (complex.{u} n) = (globeTensorIso n).hom := by
  apply (homEquiv (complex.{u} n).nu (K.{u} n).nu).injective
  change curry (uncurry (chainDiagram (complex n))) = curry (uncurry (globeDiagram n))
  rw [curry_uncurry,curry_uncurry]
  apply GlobeComplex.functor_ext
  change tableCell (topTable n) = _
  rw [tableCell_of_bounded n _ (topTable_bounded n),globeDiagram_top]
  apply congrArg ofMap
  have he : tableMap.{u,u} n (topTable n) = Hom.id (complex n) := by
    apply GlobeComplex.hom_ext
    rw [tableMap_nu_top,topTable_bounded]
    rfl
  rw [tableCylinder,he,Hom.cylinder_id]
  rfl

instance chainComparison_globe_isIso (n : ℕ) : IsIso (chainComparison (complex.{u} n)) := by
  rw [chainComparison_globe]
  infer_instance
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

def intervalExtensionOfSimplexIsIso
    (h : ∀ (P : Type u) [LinearOrder P] [Finite P],
      IsIso (chainComparison (NormalizedChains.complex P))) : RightIntervalExtension.{u} where
  tensor := tensorFunctor
  endpoint := tensorEndpoint
  projection := tensorProjection
  endpoint_projection := tensorEndpoint_projection
  cocontinuous := tensorFunctor_preservesColimits
  rightAdjoint := tensorFunctor_isLeftAdjoint
  simplex P _ _ := by
    letI := h P
    exact asIso (chainComparison (NormalizedChains.complex P))
  simplex_natural _ _ _ _ _ _ a := chainComparison_natural a
  simplex_endpoint P _ _ b := chainComparison_endpoint (NormalizedChains.complex P) b
  simplex_projection P _ _ := chainComparison_projection (NormalizedChains.complex P)
  globe := globeTensorIso
  globe_natural := globeTensorIso_natural
  globe_endpoint := globeTensorIso_endpoint
  globe_projection := globeTensorIso_projection

theorem fullMain_of_simplexComparison_isIso
    (h : ∀ (P : Type u) [LinearOrder P] [Finite P],
      IsIso (chainComparison (NormalizedChains.complex P))) : FullMain.{u} :=
  fullMain_of_rightIntervalExtension ⟨intervalExtensionOfSimplexIsIso h⟩
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex
open CategoryTheory

def cylinderFunctor : DirectedComplex.{u} ⥤ DirectedComplex.{u} where
  obj := cylinder
  map := Hom.cylinder
  map_id _ := Hom.cylinder_id
  map_comp f g := Hom.cylinder_comp f g

end Thomason.DirectedComplex

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains
open CategoryTheory DirectedComplex

def complexOrderIso {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (e : P ≃o Q) : complex P ≅ complex Q where
  hom := complexMap (e : P →o Q)
  inv := complexMap (e.symm : Q →o P)
  hom_inv_id := by
    change Hom.comp (complexMap (e : P →o Q)) (complexMap (e.symm : Q →o P)) = _
    rw [← complexMap_comp]
    have he : (e.symm : Q →o P).comp (e : P →o Q) = OrderHom.id := by
      ext x
      exact e.symm_apply_apply x
    rw [he, complexMap_id]
    rfl
  inv_hom_id := by
    change Hom.comp (complexMap (e.symm : Q →o P)) (complexMap (e : P →o Q)) = _
    rw [← complexMap_comp]
    have he : (e : P →o Q).comp (e.symm : Q →o P) = OrderHom.id := by
      ext x
      exact e.apply_symm_apply x
    rw [he, complexMap_id]
    rfl

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex

lemma chainComparison_isIso_of_iso {M N : DirectedComplex.{u}} (e : M ≅ N)
    [IsIso (chainComparison M)] : IsIso (chainComparison N) := by
  have h := chainComparison_natural e.hom
  have : IsIso (tensorFunctor.map e.hom.nu) :=
    show IsIso ((nuFunctor ⋙ tensorFunctor).map e.hom) from inferInstance
  have : IsIso ((cylinderFunctor ⋙ nuFunctor).map e.hom) := inferInstance
  have : IsIso (tensorFunctor.map e.hom.nu ≫ chainComparison N) := by
    rw [h]
    change IsIso (chainComparison M ≫ (cylinderFunctor ⋙ nuFunctor).map e.hom)
    exact IsIso.comp_isIso' ‹IsIso (chainComparison M)›
      ‹IsIso ((cylinderFunctor ⋙ nuFunctor).map e.hom)›
  exact IsIso.of_isIso_comp_left (tensorFunctor.map e.hom.nu) (chainComparison N)

instance chainComparison_empty_isIso (P : Type u) [PartialOrder P] [IsEmpty P] :
    IsIso (chainComparison (NormalizedChains.complex P)) := by
  have : IsEmpty (NormalizedChains.complex P).nu.Cell :=
    ⟨fun x => isEmptyElim (NormalizedChains.PosetTables.tableStart x)⟩
  have : IsEmpty (NormalizedChains.complex P).cylinder.nu.Cell :=
    ⟨fun x => isEmptyElim ((NormalizedChains.complex P).cylinderProjection.nu.map x)⟩
  exact Limits.isIso_of_isInitial
    ((emptyOmegaIsInitial (NormalizedChains.complex P).nu).isInitialObj tensorFunctor _)
    (emptyOmegaIsInitial (NormalizedChains.complex P).cylinder.nu) _

end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory DirectedComplex NormalizedChains

def raisedOrientalChain (N : ℕ) {K : DirectedComplex.{v}}
    (F : OmegaCategory.Functor (complex (ULift.{u} (Fin (N+1)))).nu K.nu) :
    Hom (complex (ULift.{u} (Fin (N+1)))) K :=
  Hom.comp (complexMap (orderULiftDown (Fin (N+1))))
    (orientalChain N (OmegaCategory.Functor.comp
      (complexMap (orderULiftUp (Fin (N+1)))).nu F))

lemma raisedOrientalChain_nu (N : ℕ) {K : DirectedComplex.{v}}
    (F : OmegaCategory.Functor (complex (ULift.{u} (Fin (N+1)))).nu K.nu) :
    (raisedOrientalChain N F).nu = F := by
  have he : Hom.comp (complexMap (orderULiftDown (Fin (N+1))))
      (complexMap (orderULiftUp (Fin (N+1)))) =
      Hom.id (complex (ULift.{u} (Fin (N+1)))) := by
    rw [← complexMap_comp, orderULiftDown_up, complexMap_id]
  apply OmegaCategory.Functor.ext
  funext x
  change (orientalChain N _).nu.map
    ((complexMap (orderULiftDown (Fin (N+1)))).nu.map x) = _
  rw [orientalChain_nu]
  change F.map (((Hom.comp (complexMap (orderULiftDown (Fin (N+1))))
    (complexMap (orderULiftUp (Fin (N+1))))).nu.map x)) = F.map x
  rw [he]
  rfl

lemma raisedOrientalChain_of_nu (N : ℕ) {K : DirectedComplex.{v}}
    (f : Hom (complex (ULift.{u} (Fin (N+1)))) K) :
    raisedOrientalChain N f.nu = f := by
  unfold raisedOrientalChain
  change Hom.comp (complexMap (orderULiftDown (Fin (N+1))))
    (orientalChain N (Hom.comp (complexMap (orderULiftUp (Fin (N+1)))) f).nu) = f
  rw [orientalChain_of_nu]
  change Hom.comp (Hom.comp (complexMap (orderULiftDown (Fin (N+1))))
    (complexMap (orderULiftUp (Fin (N+1))))) f = f
  rw [← complexMap_comp, orderULiftDown_up, complexMap_id]
  rfl

lemma raisedOriental_nu_injective {N : ℕ} {K : DirectedComplex.{v}}
    {f g : Hom (complex (ULift.{u} (Fin (N+1)))) K} (h : f.nu = g.nu) : f = g := by
  simpa only [raisedOrientalChain_of_nu] using congrArg (raisedOrientalChain N) h

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains
open CategoryTheory DirectedComplex DirectedComplex.Table

lemma table_truncated_of_card_le {P : Type u} [LinearOrder P] [Fintype P]
    {n : ℕ} (h : Fintype.card P ≤ n+1) : (complex P).nu.IsTruncated n := by
  intro x
  apply dimension_of_rows_above_zero
  intro p hp b
  apply Subtype.ext
  exact grade_eq_zero_of_card_lt (E := P) (k := p+1) (x.row p b).property (by omega)

lemma edgeTable_bounded {P : Type u} [PartialOrder P] (a b : P) (h : a ≤ b) :
    truncate 1 false (edgeTable a b h) = edgeTable a b h := by
  apply dimension_of_rows_above_zero
  intro p hp e
  cases p with
  | zero => omega
  | succ p => cases p with
    | zero => omega
    | succ p => rfl

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.GlobeComplex
open CategoryTheory DirectedComplex DirectedComplex.Table

def topOneArrow : OmegaCategory.OneHom (complex.{u} 1).nu
    ((complex.{u} 1).nu.sourceObject (topTable 1))
    ((complex.{u} 1).nu.targetObject (topTable 1)) :=
  ⟨topTable 1, topTable_bounded 1, rfl, rfl⟩

def simplexOneFunctor : OmegaCategory.Functor (NormalizedChains.complex (Fin 2)).nu
    (complex.{u} 1).nu :=
  NormalizedChains.ordinalDiagramFunctor (ComposableArrows.mk₁ topOneArrow)

lemma simplexOneFunctor_edge :
    simplexOneFunctor.{u}.map (NormalizedChains.edgeTable 0 1 (by decide)) = topTable 1 := by
  unfold simplexOneFunctor NormalizedChains.ordinalDiagramFunctor
  change (complex 1).nu.oneSkeletonEvaluation.map
    ((OmegaCategory.ofCategoryMap (ComposableArrows.mk₁ topOneArrow)).map
      (NormalizedChains.tableEndpoints.map (NormalizedChains.edgeTable 0 1 (by decide)))) = _
  rw [NormalizedChains.tableEndpoints_edge]
  rfl

lemma simplexOneFunctor_vertex (b : Fin 2) :
    simplexOneFunctor.{u}.map (NormalizedChains.vertexTable b) =
      truncate 0 (decide (b = 1)) (topTable 1) := by
  unfold simplexOneFunctor NormalizedChains.ordinalDiagramFunctor
  change (complex 1).nu.oneSkeletonEvaluation.map
    ((OmegaCategory.ofCategoryMap (ComposableArrows.mk₁ topOneArrow)).map
      (NormalizedChains.tableEndpoints.map (NormalizedChains.vertexTable b))) = _
  rw [NormalizedChains.tableEndpoints_vertex]
  fin_cases b <;> rfl

def toSimplexOne : Hom (complex.{u} 1)
    (NormalizedChains.complex (ULift.{u} (Fin 2))) :=
  tableMap 1 (NormalizedChains.edgeTable ⟨0⟩ ⟨1⟩ (by decide))

def fromSimplexOne : Hom (NormalizedChains.complex (ULift.{u} (Fin 2)))
    (complex.{u} 1) :=
  Hom.comp (NormalizedChains.complexMap (NormalizedChains.orderULiftDown (Fin 2)))
    (orientalChain 1 simplexOneFunctor)

lemma toSimplexOne_top : toSimplexOne.{u}.nu.map (topTable 1) =
    NormalizedChains.edgeTable ⟨0⟩ ⟨1⟩ (by decide) := by
  rw [toSimplexOne, tableMap_nu_top, NormalizedChains.edgeTable_bounded]

lemma fromSimplexOne_edge : fromSimplexOne.{u}.nu.map
    (NormalizedChains.edgeTable ⟨0⟩ ⟨1⟩ (by decide)) = topTable 1 := by
  change (orientalChain 1 simplexOneFunctor).nu.map
    ((NormalizedChains.complexMap (NormalizedChains.orderULiftDown (Fin 2))).nu.map _) = _
  erw [NormalizedChains.complexMap_edge, orientalChain_nu]
  exact simplexOneFunctor_edge

lemma to_fromSimplexOne : Hom.comp toSimplexOne.{u} fromSimplexOne = Hom.id (complex 1) := by
  apply hom_ext
  change fromSimplexOne.nu.map (toSimplexOne.nu.map (topTable 1)) = topTable 1
  rw [toSimplexOne_top, fromSimplexOne_edge]

lemma fromSimplexOne_vertex (b : Fin 2) :
    fromSimplexOne.{u}.nu.map (NormalizedChains.vertexTable ⟨b⟩) =
      truncate 0 (decide (b = 1)) (topTable 1) := by
  change (orientalChain 1 simplexOneFunctor).nu.map
    ((NormalizedChains.complexMap (NormalizedChains.orderULiftDown (Fin 2))).nu.map _) = _
  erw [NormalizedChains.complexMap_vertex, orientalChain_nu]
  exact simplexOneFunctor_vertex b

lemma toSimplexOne_face (b : Bool) :
    toSimplexOne.{u}.nu.map (truncate 0 b (topTable 1)) =
      NormalizedChains.vertexTable ⟨if b then 1 else 0⟩ := by
  have h := toSimplexOne.{u}.nu.map_face 0 b (topTable 1)
  rw [face_nu, toSimplexOne_top] at h
  cases b
  · exact h.trans (NormalizedChains.edgeTable_source _ _ _)
  · exact h.trans (NormalizedChains.edgeTable_target _ _ _)

lemma from_toSimplexOne : Hom.comp fromSimplexOne.{u} toSimplexOne =
    Hom.id (NormalizedChains.complex (ULift.{u} (Fin 2))) := by
  apply raisedOriental_nu_injective (N := 1)
  apply OmegaCategory.Functor.ext
  funext x
  change toSimplexOne.nu.map (fromSimplexOne.nu.map x) = x
  have hdim : (NormalizedChains.complex (ULift.{u} (Fin 2))).nu.IsTruncated 1 :=
    NormalizedChains.table_truncated_of_card_le (by simp)
  have hx := NormalizedChains.map_table_eq_edge hdim
    (OmegaCategory.Functor.id _) x
  change x = NormalizedChains.edgeTable (NormalizedChains.tableStart x)
    (NormalizedChains.tableFinish x) (NormalizedChains.tableStart_le_finish x) at hx
  have hedge : ∀ (a b : ULift.{u} (Fin 2)) (h : a ≤ b),
      toSimplexOne.nu.map (fromSimplexOne.nu.map (NormalizedChains.edgeTable a b h)) =
        NormalizedChains.edgeTable a b h := by
    rintro ⟨a⟩ ⟨b⟩ hab
    fin_cases a <;> fin_cases b
    · rw [NormalizedChains.edgeTable_diagonal, fromSimplexOne_vertex, toSimplexOne_face]
      rfl
    · exact (congrArg toSimplexOne.nu.map fromSimplexOne_edge).trans toSimplexOne_top
    · exact False.elim (by simp at hab)
    · rw [NormalizedChains.edgeTable_diagonal, fromSimplexOne_vertex, toSimplexOne_face]
      rfl
  rw [hx]
  exact hedge _ _ _

def simplexOneIso : complex.{u} 1 ≅ NormalizedChains.complex (ULift.{u} (Fin 2)) where
  hom := toSimplexOne
  inv := fromSimplexOne
  hom_inv_id := to_fromSimplexOne
  inv_hom_id := from_toSimplexOne

end Thomason.GlobeComplex

end

noncomputable section
universe u v w z


namespace Thomason.GlobeComplex
open CategoryTheory DirectedComplex DirectedComplex.Table

def toSimplexZero : Hom (complex.{u} 0)
    (NormalizedChains.complex (ULift.{u} (Fin 1))) :=
  tableMap 0 (NormalizedChains.vertexTable ⟨0⟩)

def fromSimplexZero : Hom (NormalizedChains.complex (ULift.{u} (Fin 1)))
    (complex.{u} 0) :=
  raisedOrientalChain 0 (OmegaCategory.constantAt _ (topTable 0) (topTable_bounded 0))

lemma fromSimplexZero_nu (x : (NormalizedChains.complex (ULift.{u} (Fin 1))).nu.Cell) :
    fromSimplexZero.{u}.nu.map x = topTable 0 := by
  unfold fromSimplexZero
  rw [raisedOrientalChain_nu]
  rfl

lemma toSimplexZero_top : toSimplexZero.{u}.nu.map (topTable 0) =
    NormalizedChains.vertexTable ⟨0⟩ := by
  rw [toSimplexZero, tableMap_nu_top]
  exact NormalizedChains.vertexTable_source _

lemma simplexZero_table_unique (x : (NormalizedChains.complex (ULift.{u} (Fin 1))).nu.Cell) :
    x = NormalizedChains.vertexTable ⟨0⟩ := by
  have hdim : (NormalizedChains.complex (ULift.{u} (Fin 1))).nu.IsTruncated 1 :=
    NormalizedChains.table_truncated_of_card_le (by simp)
  have hx := NormalizedChains.map_table_eq_edge hdim
    (OmegaCategory.Functor.id _) x
  change x = NormalizedChains.edgeTable (NormalizedChains.tableStart x)
    (NormalizedChains.tableFinish x) (NormalizedChains.tableStart_le_finish x) at hx
  have hs : NormalizedChains.tableStart x = (⟨0⟩ : ULift.{u} (Fin 1)) := Subsingleton.elim _ _
  have ht : NormalizedChains.tableFinish x = (⟨0⟩ : ULift.{u} (Fin 1)) := Subsingleton.elim _ _
  simp only [hs, ht, NormalizedChains.edgeTable_diagonal] at hx
  exact hx

lemma to_fromSimplexZero : Hom.comp toSimplexZero.{u} fromSimplexZero = Hom.id (complex 0) := by
  apply hom_ext
  change fromSimplexZero.nu.map (toSimplexZero.nu.map (topTable 0)) = topTable 0
  exact fromSimplexZero_nu _

lemma from_toSimplexZero : Hom.comp fromSimplexZero.{u} toSimplexZero =
    Hom.id (NormalizedChains.complex (ULift.{u} (Fin 1))) := by
  apply raisedOriental_nu_injective (N := 0)
  apply OmegaCategory.Functor.ext
  funext x
  change toSimplexZero.nu.map (fromSimplexZero.nu.map x) = x
  rw [fromSimplexZero_nu, toSimplexZero_top, simplexZero_table_unique x]

def simplexZeroIso : complex.{u} 0 ≅ NormalizedChains.complex (ULift.{u} (Fin 1)) where
  hom := toSimplexZero
  inv := fromSimplexZero
  hom_inv_id := to_fromSimplexZero
  inv_hom_id := from_toSimplexZero

end Thomason.GlobeComplex

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex

instance chainComparison_simplexZero_isIso :
    IsIso (chainComparison (NormalizedChains.complex (ULift.{u} (Fin 1)))) :=
  chainComparison_isIso_of_iso GlobeComplex.simplexZeroIso

instance chainComparison_simplexOne_isIso :
    IsIso (chainComparison (NormalizedChains.complex (ULift.{u} (Fin 2)))) :=
  chainComparison_isIso_of_iso GlobeComplex.simplexOneIso

end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains
open CategoryTheory DirectedComplex

def complexFinIso (P : Type u) [LinearOrder P] [Fintype P]
    {k : ℕ} (h : Fintype.card P = k) :
    complex (ULift.{u} (Fin k)) ≅ complex P :=
  complexOrderIso (ULift.orderIso.trans (Fintype.orderIsoFinOfCardEq P h))

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex

lemma chainComparison_small_isIso (P : Type u) [LinearOrder P] [Fintype P]
    (h : Fintype.card P ≤ 2) :
    IsIso (chainComparison (NormalizedChains.complex P)) := by
  have hcases : Fintype.card P = 0 ∨ Fintype.card P = 1 ∨ Fintype.card P = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · let : IsEmpty P := Fintype.card_eq_zero_iff.mp h0
    infer_instance
  · exact chainComparison_isIso_of_iso (NormalizedChains.complexFinIso P h1)
  · exact chainComparison_isIso_of_iso (NormalizedChains.complexFinIso P h2)

lemma simplexComparison_isIso_of_standard
    (h : ∀ m : ℕ, IsIso (chainComparison
      (NormalizedChains.complex (ULift.{u} (Fin (m+3))))))
    (P : Type u) [LinearOrder P] [Finite P] :
    IsIso (chainComparison (NormalizedChains.complex P)) := by
  let := Fintype.ofFinite P
  by_cases hsmall : Fintype.card P ≤ 2
  · exact chainComparison_small_isIso P hsmall
  · have hcard : Fintype.card P = (Fintype.card P - 3) + 3 := by omega
    let := h (Fintype.card P - 3)
    exact chainComparison_isIso_of_iso (NormalizedChains.complexFinIso P hcard)

theorem fullMain_of_standardSimplexComparison_isIso
    (h : ∀ m : ℕ, IsIso (chainComparison
      (NormalizedChains.complex (ULift.{u} (Fin (m+3)))))) : FullMain.{u} :=
  fullMain_of_simplexComparison_isIso (simplexComparison_isIso_of_standard h)
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory.Presentation

lemma cells_induction (P : Presentation.{u}) (Q : P.category.Cell → Prop)
    (gen : ∀ g, Q (P.generator g))
    (source : ∀ k x, Q x → Q (P.category.source k x))
    (target : ∀ k x, Q x → Q (P.category.target k x))
    (comp : ∀ k x y (h : P.category.target k x = P.category.source k y),
      Q x → Q y → Q (P.category.comp k x y h))
    (x : P.category.Cell) : Q x := by
  induction x using Quotient.inductionOn with | h x =>
    rcases x with ⟨x,hx⟩
    induction hx with
    | gen g => exact gen g
    | source k x hx ih => exact source k _ ih
    | target k x hx ih => exact target k _ ih
    | comp k x y hx hy hm ihx ihy =>
      have hc : P.category.target k (Quotient.mk _ ⟨x,hx⟩) =
          P.category.source k (Quotient.mk _ ⟨y,hy⟩) := Quotient.sound hm
      rw [← P.mk_comp k ⟨x,hx⟩ ⟨y,hy⟩ hm hc]
      exact comp k _ _ hc ihx ihy

end Thomason.OmegaCategory.Presentation

end

end OAI
