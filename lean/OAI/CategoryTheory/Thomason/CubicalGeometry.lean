import Mathlib
import OAI.CategoryTheory.Thomason.RelativeRepresentation

namespace OAI

/-! Cubical Geometry. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval

namespace Thomason.GeometricRecognition
open LastVertexProof KanLocal

lemma realization_homotopy_rel {A B K : SSet.{u}} (i : B ⟶ A) [Mono i]
    {f g : A ⟶ K} (H : SSet.Homotopy f g)
    (hH : i ▷ Δ[1] ≫ H.h = fst B Δ[1] ≫ i ≫ g) :
    Nonempty ((SSet.toTop.map f).hom.HomotopyRel (SSet.toTop.map g).hom
      (Set.range (SSet.toTop.map i))) := by
  let s := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i
    (SSet.stdSimplex.δ (n := 0) (0 : Fin 2))
  have hinl : s.inl ≫ s.ι = A ◁ SSet.stdSimplex.δ (n := 0) 0 := s.inl_ι
  have hinr : s.inr ≫ s.ι = i ▷ Δ[1] := s.inr_ι
  have heq : s.ι ≫ H.h = s.ι ≫ fst A Δ[1] ≫ g := by
    apply s.isPushout.hom_ext
    · rw [← Category.assoc,hinl,← Category.assoc,hinl]
      apply (cancel_epi (SimplicialCylinder.zeroFactorIso A).hom).mp
      rw [← Category.assoc,CoherentGluing.zeroFactor_one,H.h₁,
        ← Category.assoc,CoherentGluing.zeroFactor_one,SSet.ι₁_fst_assoc]
    · rw [← Category.assoc,hinr,← Category.assoc,hinr,hH,
        whiskerRight_fst_assoc]
  obtain ⟨r,hr,_,⟨R⟩⟩ := TopologicalHorn.anodyne_realization_retract s.ι
    (SSet.anodyneExtensions_pushoutObjObjι s (SimplicialCylinder.delta_one_anodyne 0))
  let j := SSet.toTop.map s.ι
  let e := SSet.toTop.map (SSet.ι₀ (X := A))
  let z : C(SSet.toTop.obj A,SSet.toTop.obj (A ⊗ Δ[1])) := j.hom.comp (r.hom.comp e.hom)
  have hz (b : SSet.toTop.obj B) : e (SSet.toTop.map i b) ∈ Set.range j := by
    refine ⟨SSet.toTop.map (SSet.ι₀ ≫ s.inr) b,?_⟩
    change (SSet.toTop.map (SSet.ι₀ ≫ s.inr) ≫ j) b = _
    dsimp only [j,e]
    rw [← Functor.map_comp,Category.assoc,hinr,SSet.ι₀_comp,Functor.map_comp]
    rfl
  let h : z.HomotopyRel e.hom (Set.range (SSet.toTop.map i)) :=
    { toHomotopy := R.toHomotopy.compContinuousMap e.hom
      prop' := by
        rintro t a ⟨b,rfl⟩
        exact R.prop t _ (hz b) }
  let h₁ := h.compContinuousMap (SSet.toTop.map H.h).hom
  let h₂ := h.compContinuousMap (SSet.toTop.map (fst A Δ[1] ≫ g)).hom
  have hstart : (SSet.toTop.map H.h).hom.comp z =
      (SSet.toTop.map (fst A Δ[1] ≫ g)).hom.comp z := by
    have hh : (SSet.toTop.map H.h).hom.comp j.hom =
        (SSet.toTop.map (fst A Δ[1] ≫ g)).hom.comp j.hom := by
      change (SSet.toTop.map s.ι ≫ SSet.toTop.map H.h).hom =
        (SSet.toTop.map s.ι ≫ SSet.toTop.map (fst A Δ[1] ≫ g)).hom
      rw [← Functor.map_comp,← Functor.map_comp,heq]
    simpa only [z,← ContinuousMap.comp_assoc] using
      congrArg (fun q : C(SSet.toTop.obj s.pt,SSet.toTop.obj K) =>
        q.comp (r.hom.comp e.hom)) hh
  have hf : (SSet.toTop.map H.h).hom.comp e.hom = (SSet.toTop.map f).hom := by
    change (SSet.toTop.map SSet.ι₀ ≫ SSet.toTop.map H.h).hom = _
    rw [← Functor.map_comp,H.h₀]
  have hg : (SSet.toTop.map (fst A Δ[1] ≫ g)).hom.comp e.hom = (SSet.toTop.map g).hom := by
    change (SSet.toTop.map SSet.ι₀ ≫ SSet.toTop.map (fst A Δ[1] ≫ g)).hom = _
    rw [← Functor.map_comp,SSet.ι₀_fst_assoc]
  exact ⟨(h₁.cast rfl hf).symm.trans (h₂.cast hstart.symm hg)⟩
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

lemma based_homotopy_boundary {A B K : SSet.{u}} (i : B ⟶ A) (z : B ⟶ K)
    {a b : A ⟶ K} (H : BasedHomotopy i z a b) : i ≫ a = z ∧ i ≫ b = z := by
  obtain ⟨H,hH⟩ := H
  constructor
  · have hh := congrArg (fun q => SSet.ι₀ ≫ q) hH
    simpa only [SSet.ι₀_comp_assoc,H.h₀,SSet.ι₀_fst_assoc] using hh
  · have hh := congrArg (fun q => SSet.ι₁ ≫ q) hH
    simpa only [SSet.ι₁_comp_assoc,H.h₁,SSet.ι₁_fst_assoc] using hh

lemma based_related_boundary {A B K : SSet.{u}} (i : B ⟶ A) (z : B ⟶ K)
    {a b : A ⟶ K} (H : BasedRelated i z a b) : i ≫ a = i ≫ b := by
  induction H with
  | rel a b H => exact (based_homotopy_boundary i z H).1.trans (based_homotopy_boundary i z H).2.symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

lemma based_related_homotopy {A B K : SSet.{u}} [SSet.KanComplex K]
    (i : B ⟶ A) [Mono i] (z : B ⟶ K) {a b : A ⟶ K}
    (H : BasedRelated i z a b) : i ≫ a = z → BasedHomotopy i z a b := by
  induction H with
  | rel a b H => exact fun _ => H
  | refl a => exact fun ha => based_homotopy_refl i z a ha
  | symm a b H ih =>
    intro hb
    exact based_homotopy_symm i z (ih ((based_related_boundary i z H).trans hb))
  | trans a b c Hab Hbc ih ih' =>
    intro ha
    exact based_homotopy_trans i z (ih ha) (ih' ((based_related_boundary i z Hab).symm.trans ha))

lemma based_related_pre {A B A' B' K : SSet.{u}}
    (i : B ⟶ A) (j : B' ⟶ A') (f : A' ⟶ A) (g : B' ⟶ B)
    (w : j ≫ f = g ≫ i) (z : B ⟶ K) {a b : A ⟶ K}
    (H : BasedRelated i z a b) : BasedRelated j (g ≫ z) (f ≫ a) (f ≫ b) := by
  induction H with
  | rel a b H => exact Relation.EqvGen.rel _ _ (based_homotopy_pre i j f g w z H)
  | refl a => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'

lemma based_related_post {A B K L : SSet.{u}} (i : B ⟶ A) (z : B ⟶ K)
    {a b : A ⟶ K} (H : BasedRelated i z a b) (f : K ⟶ L) :
    BasedRelated i (z ≫ f) (a ≫ f) (b ≫ f) := by
  induction H with
  | rel a b H => exact Relation.EqvGen.rel _ _ (based_homotopy_post i z H f)
  | refl a => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'

lemma pair_relative_nerve_detection (P B : PartOrd.{u}) [Finite P]
    (i : B →o P) (hi : Function.Injective i) {Q : Type u} [PartialOrder Q]
    (q : Q) (f g : P →o Q) (H : (affineMap f).Homotopy (affineMap g))
    (hH : ∀ (t : unitInterval) (x : PolyPoint B), H (t,map i (preservesChains_monotone i) x) = vertex q) :
    ∃ n, BasedRelated (nerveMap (levelMap i n).toFunctor)
      (nerveMap (constantOrder (level B n) q).toFunctor)
      (nerveMap (f.comp (last P n)).toFunctor)
      (nerveMap (g.comp (last P n)).toFunctor) := by
  let : Fintype P := Fintype.ofFinite P
  let A : Set (PolyPoint P) := Set.range (map i (preservesChains_monotone i))
  have hA : ∀ t x, x ∈ A → H (t,x) = vertex q := by
    rintro t x ⟨y,rfl⟩
    exact hH t y
  obtain ⟨n,hn⟩ := homotopy_relative_subdivision_contiguity P f g H A q hA
  let c : level B (n+1) →o relativeFaceSet (relativeVertices P A n) :=
    { toFun := fun s => ⟨s.map (levelMap i n),by
        intro p hp
        obtain ⟨x,hx,rfl⟩ := (NonemptyFiniteChains.mem_map_iff s (levelMap i n) p).mp hp
        change levelHomeomorph P n (vertex (levelMap i n x)) ∈ A
        refine ⟨levelHomeomorph B n (vertex x),?_⟩
        rw [← map_vertex (levelMap i n) (preservesChains_monotone (levelMap i n)),
          levelHomeomorph_natural i hi]⟩
      monotone' := fun _ _ h => (NonemptyFiniteChains.orderHomMap (levelMap i n)).monotone h }
  have hw : nerveMap (levelMap i (n+1)).toFunctor ≫ 𝟙 _ =
      nerveMap c.toFunctor ≫ nerveMap (relativeFaceInclusion (relativeVertices P A n)).toFunctor := by
    rw [Category.comp_id,← nerveOrderMap_comp]
    rfl
  have hn' := based_related_pre _ (nerveMap (levelMap i (n+1)).toFunctor) (𝟙 _)
    (nerveMap c.toFunctor) hw _ (relative_related_nerve (relativeVertices P A n) q _ _ hn)
  have hf : orientedMap (toChainMap (f.comp (last P n))).toFun
      (toChainMap (f.comp (last P n))).chains = f.comp (last P (n+1)) := by
    ext s
    exact orientedMap_monotone (f.comp (last P n)) s
  have hg : orientedMap (toChainMap (g.comp (last P n))).toFun
      (toChainMap (g.comp (last P n))).chains = g.comp (last P (n+1)) := by
    ext s
    exact orientedMap_monotone (g.comp (last P n)) s
  refine ⟨n+1,?_⟩
  simpa only [hf,hg,Category.id_comp,nerve_constant_pre'] using hn'

lemma pair_relative_nerve_descent (P B : PartOrd.{u}) [Finite P]
    (i : B →o P) (hi : Function.Injective i) {Q : Type u} [PartialOrder Q]
    (q : Q) (f g : P →o Q) (hf : f.comp i = constantOrder B q)
    (hg : g.comp i = constantOrder B q)
    (H : (affineMap f).Homotopy (affineMap g))
    (hH : ∀ (t : unitInterval) (x : PolyPoint B),
      H (t,map i (preservesChains_monotone i) x) = vertex q)
    (K : SSet.{u}) [SSet.KanComplex K] (r : nerve Q ⟶ K) :
    BasedHomotopy (nerveMap i.toFunctor) (nerveMap (constantOrder B q).toFunctor ≫ r)
      (nerveMap f.toFunctor ≫ r) (nerveMap g.toFunctor ≫ r) := by
  obtain ⟨n,hn⟩ := pair_relative_nerve_detection P B i hi q f g H hH
  let : Mono (nerveMap i.toFunctor) := nerveOrderMap_mono i hi
  let : Mono (nerveMap (levelMap i n).toFunctor) :=
    nerveOrderMap_mono _ (levelMap_injective i hi n)
  have hfr : nerveMap i.toFunctor ≫ nerveMap f.toFunctor ≫ r =
      nerveMap (constantOrder B q).toFunctor ≫ r := by
    rw [← Category.assoc,← nerveOrderMap_comp,hf]
  have hgr : nerveMap i.toFunctor ≫ nerveMap g.toFunctor ≫ r =
      nerveMap (constantOrder B q).toFunctor ≫ r := by
    rw [← Category.assoc,← nerveOrderMap_comp,hg]
  have hb : nerveMap (levelMap i n).toFunctor ≫ nerveMap (f.comp (last P n)).toFunctor ≫ r =
      nerveMap (constantOrder (level B n) q).toFunctor ≫ r := by
    rw [← Category.assoc,← nerveOrderMap_comp,OrderHom.comp_assoc,last_natural,
      ← OrderHom.comp_assoc,hf,constantOrder_comp]
  obtain ⟨G,hG⟩ := based_related_homotopy _ _ (based_related_post _ _ hn r) hb
  let G' : SSet.Homotopy (nerveMap (last P n).toFunctor ≫ nerveMap f.toFunctor ≫ r)
      (nerveMap (last P n).toFunctor ≫ nerveMap g.toFunctor ≫ r) :=
    CoherentGluing.toHomotopy G.h
      (by simpa only [nerveOrderMap_comp,Category.assoc] using G.h₀)
      (by simpa only [nerveOrderMap_comp,Category.assoc] using G.h₁)
  refine pair_local_injective_plain (nerveMap i.toFunctor)
    (nerveMap (levelMap i n).toFunctor) (nerveMap (last P n).toFunctor)
    (nerveMap (last B n).toFunctor)
    (by rw [← nerveOrderMap_comp,← nerveOrderMap_comp,last_natural])
    (last_local P n) (last_local B n) _ _ _ hfr hgr G' ?_
  simpa only [G',CoherentGluing.toHomotopy,Category.assoc,nerve_constant_pre'_assoc] using hG
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Nerve Simplicial

namespace Thomason.GeometricRecognition
open PolyPoint
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

lemma map_eval {ι : Type*} [Fintype ι] [LinearOrder ι]
    (f : P →o Q) (a : ι →o P) (x : Convexity.StdSimplex ℝ ι) :
    PolyPoint.map f (preservesChains_monotone f) (eval a x) = eval (f.comp a) x := by
  apply PolyPoint.ext
  simp only [PolyPoint.map, PolyPoint.eval, evalWeights, Finsupp.mapDomain_finsetSum,
    Finsupp.mapDomain_single, OrderHom.comp_coe, Function.comp_apply]

lemma nerveMap_realizeSimplex {n : ℕ} (f : P →o Q) (a : Fin (n+1) →o P)
    (x : Convexity.StdSimplex ℝ (Fin (n+1))) :
    SSet.toTop.map (nerveMap f.monotone.functor) (realizeSimplex a x) =
      realizeSimplex (f.comp a) x := by
  have he : (SSet.yonedaEquiv (X := nerve P)).symm a.monotone.functor ≫
      nerveMap f.monotone.functor =
      (SSet.yonedaEquiv (X := nerve Q)).symm (f.comp a).monotone.functor := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp]
    rfl
  simp only [realizeSimplex]
  rw [← TopCat.comp_app, ← Functor.map_comp, he]

lemma nerveRealizationHomeomorph_natural (f : P →o Q) (z : |nerve P|) :
    nerveRealizationHomeomorph (SSet.toTop.map (nerveMap f.monotone.functor) z) =
      PolyPoint.map f (preservesChains_monotone f) (nerveRealizationHomeomorph z) := by
  obtain ⟨x,rfl⟩ := (nerveRealizationHomeomorph (P := P)).symm.surjective z
  change realizationToPoly Q (SSet.toTop.map (nerveMap f.monotone.functor)
      (polyToRealization x)) = PolyPoint.map f (preservesChains_monotone f)
        (realizationToPoly P (polyToRealization x))
  rw [realizationToPoly_polyToRealization]
  let s := supportIndex x
  let y : Face s.carrier := ⟨x,Finset.Subset.refl _⟩
  have hx : eval s.vertices (s.coordinates y) = x := s.eval_coordinates y
  rw [← hx, polyToRealization_eval, nerveMap_realizeSimplex,
    realizationToPoly_realizeSimplex, map_eval]
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial PartialOrder

namespace Thomason.GeometricRecognition
open LastVertexProof KanLocal Subdivision Mesh Contiguity PolyPoint Approximation

def realizeMap {A B : SSet.{u}} (f : A ⟶ B) : C(SSet.toTop.obj A,SSet.toTop.obj B) :=
  (SSet.toTop.map f).hom

lemma realizeMap_comp {A B C : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    realizeMap (f ≫ g) = (realizeMap g).comp (realizeMap f) := by
  dsimp only [realizeMap]
  rw [Functor.map_comp]
  rfl

lemma cancel_geometric_homotopy {P Q T : Type u}
    [TopologicalSpace P] [TopologicalSpace Q] [TopologicalSpace T]
    (f : C(Q,T)) (r : C(T,Q)) (hf : (r.comp f).Homotopic (ContinuousMap.id _))
    (a b : C(P,Q)) (h : (f.comp a).Homotopic (f.comp b)) : a.Homotopic b := by
  have h₀ := hf.comp (.refl a)
  have h₁ := hf.comp (.refl b)
  have h₂ := ContinuousMap.Homotopic.comp (.refl r) h
  have ha : a.Homotopic (r.comp (f.comp a)) := by
    simpa only [ContinuousMap.comp_assoc,ContinuousMap.id_comp] using h₀.symm
  have hb : (r.comp (f.comp b)).Homotopic b := by
    simpa only [ContinuousMap.comp_assoc,ContinuousMap.id_comp] using h₁
  exact ha.trans (h₂.trans hb)

lemma geometric_homotopy_to_affine {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (f g : P →o Q) (h : (realizeMap (nerveMap f.toFunctor)).Homotopic
      (realizeMap (nerveMap g.toFunctor))) :
    (affineMap f).Homotopic (affineMap g) := by
  have he (a : P →o Q) : (realizationToPoly Q).hom.comp
      ((realizeMap (nerveMap a.toFunctor)).comp polyToRealizationHom.hom) = affineMap a := by
    apply ContinuousMap.ext
    intro x
    have hh := nerveRealizationHomeomorph_natural a (polyToRealization x)
    change realizationToPoly Q (SSet.toTop.map (nerveMap a.toFunctor) (polyToRealization x)) = _ at hh
    rw [show nerveRealizationHomeomorph (polyToRealization x) = x from
      realizationToPoly_polyToRealization x] at hh
    exact hh
  have hh := ContinuousMap.Homotopic.comp (.refl (realizationToPoly Q).hom)
    (h.comp (.refl polyToRealizationHom.hom))
  rwa [he,he] at hh

theorem finite_order_geometric_faithful (P : PartOrd.{u}) [Finite P]
    (K : SSet.{u}) [SSet.KanComplex K] (a b : nerve P ⟶ K)
    (H : (realizeMap a).Homotopic (realizeMap b)) : Homotopic a b := by
  obtain ⟨Q,r,e,hr,hre,he⟩ := kan_poset_replacement_heq K
  obtain ⟨R₁,hR₁,l₁,c₁,hl₁,hc₁⟩ := finite_order_representative Q r e he hre P a
  obtain ⟨R₂,hR₂,l₂,c₂,hl₂,hc₂⟩ := finite_order_representative Q r e he hre R₁
    (nerveMap l₁.toFunctor ≫ b)
  let c : R₂ →o Q := c₁.comp l₂
  have hca : Homotopic (nerveMap l₂.toFunctor ≫ nerveMap l₁.toFunctor ≫ a)
      (nerveMap c.toFunctor ≫ r) := by
    simpa only [c,nerveOrderMap_comp,Category.assoc] using
      homotopic_pre (nerveMap l₂.toFunctor) hc₁
  have hh := H.comp (.refl (realizeMap (nerveMap l₂.toFunctor ≫ nerveMap l₁.toFunctor)))
  have hhr : (realizeMap (nerveMap c.toFunctor ≫ r)).Homotopic
      (realizeMap (nerveMap c₂.toFunctor ≫ r)) := by
    have h₁ := realization_homotopic hca
    have h₂ := realization_homotopic hc₂
    change (realizeMap _).Homotopic (realizeMap _) at h₁ h₂
    have hh' : (realizeMap (nerveMap l₂.toFunctor ≫ nerveMap l₁.toFunctor ≫ a)).Homotopic
        (realizeMap (nerveMap l₂.toFunctor ≫ nerveMap l₁.toFunctor ≫ b)) := by
      simpa only [realizeMap_comp,ContinuousMap.comp_assoc] using hh
    exact h₁.symm.trans (hh'.trans h₂)
  obtain ⟨s,hs,_⟩ := local_realization_heq r hr
  have htop : (realizeMap (nerveMap c.toFunctor)).Homotopic
      (realizeMap (nerveMap c₂.toFunctor)) := by
    apply cancel_geometric_homotopy (realizeMap r) s.hom hs
    simpa only [realizeMap_comp] using hhr
  let : Fintype R₂ := Fintype.ofFinite R₂
  obtain ⟨hpoly⟩ := geometric_homotopy_to_affine c c₂ htop
  obtain ⟨n,hn⟩ := geometric_homotopy_detected R₂ c c₂ hpoly
  have hn' : Homotopic (nerveMap c.toFunctor ≫ r) (nerveMap c₂.toFunctor ≫ r) := by
    apply precomp_injective (nerveMap (last R₂ n).toFunctor) (last_local R₂ n)
    simpa only [nerveOrderMap_comp,Category.assoc] using homotopic_post hn r
  have hab := homotopic_trans hca (homotopic_trans hn' (homotopic_symm hc₂))
  have hab' := precomp_injective (nerveMap l₂.toFunctor) hl₂ _ _ hab
  exact precomp_injective (nerveMap l₁.toFunctor) hl₁ a b hab'
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open PartialOrder

namespace Thomason.GeometricRecognition.Cubical
open PolyPoint
variable {I : Type u} [Fintype I] [LinearOrder I]
local instance cubeDecEqFaces : DecidableEq (Finset I) := Classical.decEq _
local instance cubeFintypeChains : Fintype (NonemptyFiniteChains I) := Fintype.ofFinite _

def chain (s : Finset I) (hs : s.Nonempty) : NonemptyFiniteChains I :=
  ⟨s,hs,fun p q => le_total p.val q.val⟩

def allFacesEquiv : Option (NonemptyFiniteChains I) ≃ Finset I where
  toFun s := s.elim ∅ NonemptyFiniteChains.finset
  invFun s := if hs : s.Nonempty then some (chain s hs) else none
  left_inv s := by
    cases s with
    | none => simp
    | some s =>
      change (if hs : s.finset.Nonempty then some (chain s.finset hs) else none) = some s
      rw [dite_eq_left s.nonempty]
      exact congrArg some (NonemptyFiniteChains.ext rfl)
  right_inv s := by
    dsimp
    split_ifs with hs
    · rfl
    · exact (Finset.not_nonempty_iff_eq_empty.mp hs).symm

lemma sum_faces (f : Finset I → ℝ) :
    ∑ s, f s = f ∅ + ∑ s : NonemptyFiniteChains I, f s.finset := by
  rw [← allFacesEquiv.sum_comp]
  exact Fintype.sum_option _

def compress (w : Finset I →₀ ℝ) : NonemptyFiniteChains I →₀ ℝ :=
  Finsupp.equivFunOnFinite.symm (fun s => w s.finset * (s.finset.card : ℝ))

@[simp] lemma compress_apply (w : Finset I →₀ ℝ) (s : NonemptyFiniteChains I) :
    compress w s = w s.finset * (s.finset.card : ℝ) := rfl

omit [Fintype I] in
lemma card_pos (s : NonemptyFiniteChains I) : 0 < (s.finset.card : ℝ) := by
  exact_mod_cast Finset.card_pos.mpr s.nonempty

lemma compress_mem_support (w : Finset I →₀ ℝ) (s : NonemptyFiniteChains I) :
    s ∈ (compress w).support ↔ s.finset ∈ w.support := by
  simp only [Finsupp.mem_support_iff,compress_apply]
  exact mul_ne_zero_iff.trans (and_iff_left (ne_of_gt (card_pos s)))

def coordinate (w : Finset I →₀ ℝ) (i : I) : ℝ :=
  ∑ s : Finset I, if i ∈ s then w s else 0

lemma compress_evaluate (w : Finset I →₀ ℝ) (i : I) :
    barycentricLinear (compress w) i = coordinate w i := by
  rw [barycentricLinear_apply, (compress w).sum_fintype (fun s r => r * (barycenter s).weights i) (by simp)]
  rw [coordinate,sum_faces]
  simp only [Finset.notMem_empty,ite_false,zero_add]
  apply Finset.sum_congr rfl
  intro s hs
  rw [compress_apply,barycenter_apply]
  split_ifs with hi
  · exact mul_inv_cancel_right₀ (ne_of_gt (card_pos s)) _
  · simp

lemma compress_nonneg (w : Finset I →₀ ℝ) (hn : ∀ s, 0 ≤ w s) :
    ∀ s, 0 ≤ compress w s := fun s => mul_nonneg (hn _) (le_of_lt (card_pos s))

lemma compress_chain (w : Finset I →₀ ℝ)
    (hc : IsChain (· ≤ ·) (w.support : Set (Finset I))) :
    IsChain (· ≤ ·) ((compress w).support : Set (NonemptyFiniteChains I)) := by
  intro s hs t ht hst
  exact hc.total ((compress_mem_support w s).mp hs) ((compress_mem_support w t).mp ht)

omit [LinearOrder I] in
lemma sum_weights (x : PolyPoint (Finset I)) : ∑ s, x.weights s = 1 := by
  exact (x.weights.sum_fintype (fun _ r => r) (fun _ => rfl)).symm.trans x.total

lemma coordinate_nonneg (w : Finset I →₀ ℝ) (hn : ∀ s, 0 ≤ w s) (i : I) :
    0 ≤ coordinate w i := by
  apply Finset.sum_nonneg
  intro s hs
  split_ifs <;> first | exact hn s | exact le_rfl

lemma coordinate_le_sum (w : Finset I →₀ ℝ) (hn : ∀ s, 0 ≤ w s) (i : I) :
    coordinate w i ≤ ∑ s, w s := by
  apply Finset.sum_le_sum
  intro s hs
  split_ifs <;> first | exact le_rfl | exact hn s

def evaluate (x : PolyPoint (Finset I)) : I → unitInterval := fun i =>
  ⟨coordinate x.weights i,coordinate_nonneg _ x.nonneg i,
    (coordinate_le_sum _ x.nonneg i).trans (sum_weights x).le⟩

lemma continuous_evaluate : Continuous (@evaluate I _ _) := by
  apply continuous_pi
  intro i
  apply Continuous.subtype_mk
  apply continuous_finsetSum
  intro s hs
  by_cases hi : i ∈ s
  · simpa only [hi,ite_true] using (continuous_weights (P := Finset I) s)
  · simp only [hi,ite_false]
    exact continuous_const

lemma evaluate_injective : Function.Injective (@evaluate I _ _) := by
  intro x y he
  have hg : compress x.weights = compress y.weights := by
    apply barycentricLinear_injective_nonneg_flag _ _
      (compress_nonneg _ x.nonneg) (compress_nonneg _ y.nonneg)
      (compress_chain _ x.chain) (compress_chain _ y.chain)
    ext i
    rw [compress_evaluate,compress_evaluate]
    exact congrArg Subtype.val (congrFun he i)
  have hn (s : NonemptyFiniteChains I) : x.weights s.finset = y.weights s.finset := by
    have h := DFunLike.congr_fun hg s
    exact mul_right_cancel₀ (ne_of_gt (card_pos s)) h
  apply PolyPoint.ext
  ext s
  by_cases hs : s.Nonempty
  · exact hn (chain s hs)
  · have hxe := sum_weights x
    have hye := sum_weights y
    rw [sum_faces] at hxe hye
    have heq := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun a _ => hn a)
    rw [heq] at hxe
    have hs0 := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    linarith

def uncompress (g : NonemptyFiniteChains I →₀ ℝ) : Finset I →₀ ℝ :=
  Finsupp.equivFunOnFinite.symm (fun s =>
    if hs : s.Nonempty then g (chain s hs) / (s.card : ℝ) else 0)

@[simp] lemma uncompress_empty (g : NonemptyFiniteChains I →₀ ℝ) :
    uncompress g ∅ = 0 := by simp [uncompress]

lemma uncompress_nonempty (g : NonemptyFiniteChains I →₀ ℝ)
    (s : Finset I) (hs : s.Nonempty) :
    uncompress g s = g (chain s hs) / (s.card : ℝ) := by
  simp only [uncompress,Finsupp.coe_equivFunOnFinite_symm,dite_eq_left hs]

lemma compress_uncompress (g : NonemptyFiniteChains I →₀ ℝ) :
    compress (uncompress g) = g := by
  ext s
  rw [compress_apply,uncompress_nonempty _ _ s.nonempty]
  have he : chain s.finset s.nonempty = s := NonemptyFiniteChains.ext rfl
  rw [he]
  exact div_mul_cancel₀ _ (ne_of_gt (card_pos s))

lemma uncompress_nonneg (g : NonemptyFiniteChains I →₀ ℝ) (hn : ∀ s, 0 ≤ g s) :
    ∀ s, 0 ≤ uncompress g s := by
  intro s
  by_cases hs : s.Nonempty
  · rw [uncompress_nonempty _ _ hs]
    exact div_nonneg (hn _) (Nat.cast_nonneg _)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs,uncompress_empty]

lemma uncompress_support_nonempty (g : NonemptyFiniteChains I →₀ ℝ)
    {s : Finset I} (hs : s ∈ (uncompress g).support) : s.Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty.mp h,Finsupp.mem_support_iff,uncompress_empty] at hs
  exact hs rfl

lemma uncompress_chain (g : NonemptyFiniteChains I →₀ ℝ)
    (hc : IsChain (· ≤ ·) (g.support : Set (NonemptyFiniteChains I))) :
    IsChain (· ≤ ·) ((uncompress g).support : Set (Finset I)) := by
  intro s hs t ht hst
  let a := chain s (uncompress_support_nonempty g hs)
  let b := chain t (uncompress_support_nonempty g ht)
  have ha : a ∈ g.support := by
    rw [← compress_uncompress g,compress_mem_support]
    exact hs
  have hb : b ∈ g.support := by
    rw [← compress_uncompress g,compress_mem_support]
    exact ht
  exact hc.total ha hb

lemma sum_le_one_of_coordinates (w : Finset I →₀ ℝ)
    (hc : IsChain (· ≤ ·) (w.support : Set (Finset I)))
    (he : w ∅ = 0) (hb : ∀ i, coordinate w i ≤ 1) : ∑ s, w s ≤ 1 := by
  by_cases hw : w = 0
  · subst w
    simp
  have hne := Finsupp.support_nonempty_iff.mpr hw
  obtain ⟨s,hs,hmin⟩ := Finset.exists_min_image w.support Finset.card hne
  have hsne : s.Nonempty := by
    by_contra h
    have hs0 := Finset.not_nonempty_iff_eq_empty.mp h
    exact (Finsupp.mem_support_iff.mp hs) (hs0 ▸ he)
  obtain ⟨i,hi⟩ := hsne
  have hmem (t : Finset I) (ht : t ∈ w.support) : i ∈ t := by
    rcases hc.total hs ht with hst | hts
    · exact hst hi
    · exact (Finset.eq_of_subset_of_card_le hts (hmin t ht)) ▸ hi
  have hcoord : coordinate w i = ∑ s, w s := by
    apply Finset.sum_congr rfl
    intro t ht
    by_cases htw : t ∈ w.support
    · simp only [hmem t htw,ite_true]
    · rw [Finsupp.notMem_support_iff.mp htw]
      split_ifs <;> rfl
  rw [← hcoord]
  exact hb i

lemma coordinate_add (a b : Finset I →₀ ℝ) (i : I) :
    coordinate (a+b) i = coordinate a i + coordinate b i := by
  simp only [coordinate,Finsupp.add_apply,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  split_ifs <;> simp

lemma coordinate_empty (r : ℝ) (i : I) :
    coordinate (Finsupp.single ∅ r) i = 0 := by
  apply Finset.sum_eq_zero
  intro s hs
  by_cases hi : i ∈ s
  · rw [ite_eq_left hi,Finsupp.single_eq_of_ne]
    intro h
    subst s
    exact Finset.notMem_empty i hi
  · rw [ite_eq_right hi]

lemma evaluate_surjective : Function.Surjective (@evaluate I _ _) := by
  intro x
  let f : I →₀ ℝ := Finsupp.equivFunOnFinite.symm (fun i => (x i).val)
  have hn : ∀ i, 0 ≤ f i := fun i => (x i).property.1
  have hc : IsChain (· ≤ ·) (f.support : Set I) :=
    fun i hi j hj hij => le_total i j
  obtain ⟨g,hgn,hgc,hgs,hgf⟩ := exists_barycentric_decomposition f hn hc
  let w := uncompress g
  have heval (i : I) : coordinate w i = (x i).val := by
    rw [← compress_evaluate,compress_uncompress,hgf]
    rfl
  have htotal : (∑ s, w s) ≤ 1 := sum_le_one_of_coordinates w
    (uncompress_chain g hgc) (uncompress_empty g) (fun i => by rw [heval]; exact (x i).property.2)
  let w' := w + Finsupp.single ∅ (1 - ∑ s, w s)
  have hmem (s : Finset I) (hs : s ∈ w'.support) : s ∈ w.support ∨ s = ∅ := by
    rcases Finset.mem_union.mp (Finsupp.support_add hs) with h | h
    · exact Or.inl h
    · right
      by_contra hne
      exact (Finsupp.mem_support_iff.mp h) (Finsupp.single_eq_of_ne hne)
  let z : PolyPoint (Finset I) := {
    weights := w'
    nonneg s := by
      dsimp [w']
      rw [Finsupp.single_apply]
      apply add_nonneg (uncompress_nonneg g hgn s)
      split_ifs
      · exact sub_nonneg.mpr htotal
      · exact le_rfl
    total := by
      change (w + Finsupp.single ∅ (1 - ∑ s, w s)).sum (fun _ r => r) = 1
      rw [Finsupp.sum_add_index (fun _ _ => rfl) (fun _ _ _ _ => rfl),
        Finsupp.sum_single_index (by rfl), w.sum_fintype (fun _ r => r) (fun _ => rfl)]
      ring
    chain := by
      intro s hs t ht hst
      rcases hmem s hs with hs | rfl
      · rcases hmem t ht with ht | rfl
        · exact (uncompress_chain g hgc).total hs ht
        · exact Or.inr (Finset.empty_subset s)
      · exact Or.inl (Finset.empty_subset t) }
  refine ⟨z,?_⟩
  funext i
  apply Subtype.ext
  change coordinate w' i = (x i).val
  rw [coordinate_add,coordinate_empty,add_zero,heval]

def cubeHomeomorph : PolyPoint (Finset I) ≃ₜ (I → unitInterval) :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective evaluate ⟨evaluate_injective,evaluate_surjective⟩) continuous_evaluate

end Thomason.GeometricRecognition.Cubical

end

noncomputable section
universe u v w z
open PartialOrder
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition.Cubical
open PolyPoint
variable {I : Type u} [Fintype I] [LinearOrder I]
local instance : DecidableEq (Finset I) := Classical.decEq _

lemma coordinate_eq_zero_iff (x : PolyPoint (Finset I)) (i : I) :
    coordinate x.weights i = 0 ↔ ∀ s ∈ x.weights.support, i ∉ s := by
  rw [coordinate,Finset.sum_eq_zero_iff_of_nonneg (fun s _ => by
    split_ifs <;> first | exact x.nonneg s | exact le_rfl)]
  constructor
  · intro h s hs hi
    have hz := h s (Finset.mem_univ s)
    simp only [hi,ite_true] at hz
    exact (Finsupp.mem_support_iff.mp hs) hz
  · intro h s hs
    split_ifs with hi
    · by_contra hn
      exact h s (Finsupp.mem_support_iff.mpr hn) hi
    · rfl

lemma coordinate_eq_one_iff (x : PolyPoint (Finset I)) (i : I) :
    coordinate x.weights i = 1 ↔ ∀ s ∈ x.weights.support, i ∈ s := by
  have he : (∑ s : Finset I, if i ∉ s then x.weights s else 0) =
      1 - coordinate x.weights i := by
    rw [← sum_weights x,coordinate,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    split_ifs <;> simp_all
  conv_lhs => rw [eq_comm,← sub_eq_zero,← he]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun s _ => by
    split_ifs <;> first | exact x.nonneg s | exact le_rfl)]
  constructor
  · intro h s hs
    by_contra hi
    have hz := h s (Finset.mem_univ s)
    simp only [hi] at hz
    exact (Finsupp.mem_support_iff.mp hs) hz
  · intro h s hs
    by_cases hi : i ∈ s
    · simp [hi]
    · have hz : x.weights s = 0 := by
        by_contra hn
        exact hi (h s (Finsupp.mem_support_iff.mpr hn))
      simp [hi,hz]

def boundaryFaces (I : Type u) [Fintype I] : Set (NonemptyFiniteChains (Finset I)) :=
  {s | ∃ i : I, (∀ v ∈ s.finset, i ∉ v) ∨ (∀ v ∈ s.finset, i ∈ v)}

omit [LinearOrder I] in
lemma boundaryFaces_downward {s t : NonemptyFiniteChains (Finset I)}
    (h : s ≤ t) (ht : t ∈ boundaryFaces I) : s ∈ boundaryFaces I := by
  obtain ⟨i,hi⟩ := ht
  exact ⟨i,hi.imp (fun hi v hv => hi v (h hv)) (fun hi v hv => hi v (h hv))⟩

omit [Fintype I] [LinearOrder I] in
lemma subdivide_support (x : PolyPoint (NonemptyFiniteChains (Finset I))) :
    (subdivide x).weights.support = x.weights.support.biUnion NonemptyFiniteChains.finset :=
  barycentricLinear_support_eq x.weights x.nonneg

lemma cube_boundary_iff (x : PolyPoint (Finset I)) :
    evaluate x ∈ Cube.boundary I ↔
      ∃ i : I, (∀ v ∈ x.weights.support, i ∉ v) ∨ (∀ v ∈ x.weights.support, i ∈ v) := by
  change (∃ i, evaluate x i = 0 ∨ evaluate x i = 1) ↔ _
  apply exists_congr
  intro i
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl ((coordinate_eq_zero_iff x i).mp (congrArg Subtype.val h))
    · exact Or.inr ((coordinate_eq_one_iff x i).mp (congrArg Subtype.val h))
  · intro h
    rcases h with h | h
    · exact Or.inl (Subtype.ext ((coordinate_eq_zero_iff x i).mpr h))
    · exact Or.inr (Subtype.ext ((coordinate_eq_one_iff x i).mpr h))

lemma face_vertex_boundary (s : NonemptyFiniteChains (Finset I)) :
    evaluate (subdivide (vertex s)) ∈ Cube.boundary I ↔ s ∈ boundaryFaces I := by
  have he : subdivide (vertex s) = barycenter s := by
    apply PolyPoint.ext
    change barycentricLinear (Finsupp.single s 1) = _
    simp [barycentricLinear]
  rw [he,cube_boundary_iff,barycenter_support]
  rfl

lemma subdivided_cube_boundary_iff (x : PolyPoint (NonemptyFiniteChains (Finset I))) :
    evaluate (subdivide x) ∈ Cube.boundary I ↔
      ∀ s ∈ x.weights.support, s ∈ boundaryFaces I := by
  rw [cube_boundary_iff,subdivide_support]
  constructor
  · rintro ⟨i,hi⟩ s hs
    exact ⟨i,hi.imp (fun hi v hv => hi v (Finset.mem_biUnion.mpr ⟨s,hs,hv⟩))
      (fun hi v hv => hi v (Finset.mem_biUnion.mpr ⟨s,hs,hv⟩))⟩
  · intro h
    let c : NonemptyFiniteChains (NonemptyFiniteChains (Finset I)) :=
      ⟨x.weights.support,(supportIndex x).nonempty,fun a b => x.chain.total a.property b.property⟩
    let t := greatest c
    obtain ⟨i,hi⟩ := h t (greatest_mem c)
    refine ⟨i,hi.imp ?_ ?_⟩
    · intro hi v hv
      obtain ⟨s,hs,hv⟩ := Finset.mem_biUnion.mp hv
      exact hi v ((le_greatest c s hs) hv)
    · intro hi v hv
      obtain ⟨s,hs,hv⟩ := Finset.mem_biUnion.mp hv
      exact hi v ((le_greatest c s hs) hv)
end Thomason.GeometricRecognition.Cubical

end

noncomputable section
universe u v w z
open PartialOrder
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition.Cubical
open PolyPoint
variable {I : Type u} [Fintype I] [LinearOrder I]

def pairCubeHomeomorph : PolyPoint (NonemptyFiniteChains (Finset I)) ≃ₜ (I → unitInterval) :=
  subdivisionHomeomorph.trans cubeHomeomorph

def boundaryEvaluate (x : PolyPoint (boundaryFaces I)) : Cube.boundary I :=
  ⟨evaluate (subdivide (map (inclusion (boundaryFaces I))
    (preservesChains_monotone (inclusion (boundaryFaces I))) x)),
    (subdivided_cube_boundary_iff _).mpr (map_subtype_support (boundaryFaces I) x)⟩

lemma boundaryEvaluate_injective : Function.Injective (@boundaryEvaluate I _ _) := by
  intro x y h
  apply map_injective (inclusion (boundaryFaces I)) Subtype.val_injective
  apply pairCubeHomeomorph.injective
  exact congrArg Subtype.val h

lemma boundaryEvaluate_surjective : Function.Surjective (@boundaryEvaluate I _ _) := by
  intro y
  let x := (pairCubeHomeomorph (I := I)).symm y.val
  have hx : ∀ s ∈ x.weights.support, s ∈ boundaryFaces I := by
    apply (subdivided_cube_boundary_iff x).mp
    change pairCubeHomeomorph x ∈ Cube.boundary I
    rw [show pairCubeHomeomorph x = y.val from pairCubeHomeomorph.apply_symm_apply y.val]
    exact y.property
  refine ⟨restrict (boundaryFaces I) x hx,?_⟩
  apply Subtype.ext
  change pairCubeHomeomorph (map (inclusion (boundaryFaces I))
    (preservesChains_monotone (inclusion (boundaryFaces I))) (restrict _ x hx)) = y.val
  rw [map_subtype_restrict]
  exact pairCubeHomeomorph.apply_symm_apply y.val

lemma continuous_boundaryEvaluate : Continuous (@boundaryEvaluate I _ _) := by
  apply Continuous.subtype_mk
  exact continuous_evaluate.comp (continuous_subdivide.comp (continuous_map _ _))

def boundaryHomeomorph : PolyPoint (boundaryFaces I) ≃ₜ Cube.boundary I :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective boundaryEvaluate
      ⟨boundaryEvaluate_injective,boundaryEvaluate_surjective⟩) continuous_boundaryEvaluate

lemma boundaryHomeomorph_natural (x : PolyPoint (boundaryFaces I)) :
    (boundaryHomeomorph x).val = pairCubeHomeomorph
      (map (inclusion (boundaryFaces I)) (preservesChains_monotone (inclusion (boundaryFaces I))) x) := rfl
end Thomason.GeometricRecognition.Cubical

end

end OAI
